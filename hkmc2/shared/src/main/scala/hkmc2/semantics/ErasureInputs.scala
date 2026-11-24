package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*
import ErasureInputs.{InputSlot, InputSymbol, ResultSlot}

/** Source declarations needed both when observing inference and when assigning representations.
  * Several declarations are outside subStatements: split bindings, handler parameters,
  * auxiliary constructor parameters, and the definitions synthesized for record fields.
  * Keep their enumeration shared so every delayed slot is prepared before erasure reads it.
  *
  * Variables include the temporaries that hold a split's scrutinee or save the value of `x`
  * across `set x = v in body`. These slots need the representation of the value they hold,
  * including when a match or a restored assignment reads an unboxed primitive on Wasm.
  */
private[hkmc2] final class ErasureDeclarations(root: Statement):
  val statements = mutable.ArrayBuffer.empty[Statement]
  val parameters = mutable.LinkedHashMap.empty[VarSymbol, Param]
  val variables = mutable.LinkedHashSet.empty[InputSymbol]
  private val visited = mutable.Set.empty[Identity[Statement]]

  private def parameter(p: Param): Unit =
    parameters(p.sym) = p
    p.subTerms.foreach(visit)

  private def variable(sym: InputSymbol): Unit =
    variables += sym
    val declaration = sym match
      case sym: (VarSymbol | TempSymbol) => sym.decl
      case sym: TermSymbol => sym.decl
    declaration match
      case S(p: Param) => parameter(p)
      case _ => ()

  private def pattern(pat: Pattern): Unit =
    // Transform bindings are local to their pattern and absent from its exported variables.
    // Lowering still assigns them, including unused bindings, so erase every allocated alias.
    pat match
      case Pattern.Constructor(target, arguments) =>
        visit(target)
        arguments.foreach(_.foreach(pattern))
      case Pattern.Composition(_, left, right) => pattern(left); pattern(right)
      case Pattern.Negation(inner) => pattern(inner)
      case _: (Pattern.Wildcard | Pattern.Literal | Pattern.Range) => ()
      case Pattern.Concatenation(left, right) => pattern(left); pattern(right)
      case Pattern.Tuple(leading, spread) =>
        leading.foreach(pattern)
        spread.foreach: (_, middle, trailing) =>
          pattern(middle)
          trailing.foreach(pattern)
      case Pattern.Record(fields) => fields.foreach((_, inner) => pattern(inner))
      case Pattern.Chain(first, second) => pattern(first); pattern(second)
      case alias @ Pattern.Alias(inner, _) =>
        alias.symbolOption.foreach(variable)
        pattern(inner)
      case Pattern.Transform(inner, parameters, transform) =>
        pattern(inner)
        parameters.foreach((_, param) => variable(param))
        visit(transform)
      case Pattern.Annotated(inner, annotations) =>
        pattern(inner)
        annotations.foreach(_.foreach(visit))
      case Pattern.Guarded(inner, guard) => pattern(inner); visit(guard)

  private def split(branches: SimpleSplit): Unit = branches match
    case SimpleSplit.Cons(SimpleSplit.Head.Let(sym, _), tail) =>
      variable(sym)
      split(tail)
    case SimpleSplit.Cons(SimpleSplit.Head.Match(_, pat, consequent), tail) =>
      pattern(pat)
      split(consequent)
      split(tail)
    case SimpleSplit.Else(_) | SimpleSplit.End => ()

  private def visit(statement: Statement): Unit = if visited.add(Identity(statement)) then
    statements += statement
    statement match
      case td: TermDefinition =>
        td.params.foreach(_.foreach(parameter))
        td.tparams.foreach(_.foreach(parameter))
      case cls: ClassLikeDef =>
        cls.paramsOpt.foreach(_.foreach(parameter))
        cls.auxParams.foreach(_.foreach(parameter))
        cls.ext.foreach(visit)
        cls match
          case pat: PatternDef =>
            pat.parameters.foreach(parameter)
            pattern(pat.pattern)
          case _ => ()
      case Lam(ps, _) => ps.foreach(parameter)
      case Forall(params, _, _) => params.foreach: param =>
        param.lb.foreach(visit)
        param.ub.foreach(visit)
      case Handle(_, _, _, _, definitions, _) => definitions.foreach: d =>
        variable(d.resumeSym)
        visit(d.td)
      case LetDecl(sym: InputSymbol, _) => variable(sym)
      case Ref(sym: VarSymbol) => variable(sym)
      case SimpleRef(sym: VarSymbol) => variable(sym)
      case IfLike(_, _, branches) => split(branches)
      case New(_, _, refinement) => refinement.foreach: (symbol, body) =>
        symbol.defn.fold(visit(body.blk))(visit)
      case Rcd(_, stats) => stats.foreach(visit)
      case field: RcdField => field.tsym.defn.foreach(visit)
      case _ => ()
    statement.subStatements.foreach(visit)
    // Legacy expansion can insert executable terms while sharing their source children.
    statement match
      case term: Resolvable => visit(term.expanded)
      case _ => ()

  visit(root)

/** Source values and virtual member results collected during resolution. Interface exposure
  * can subscribe to a member's results as they arrive. Erasure reads the completed observations
  * of the defining compilation unit. Later writes in an importing unit reach that unit's copy.
  */
private[hkmc2] final class ErasureInputs:
  private val values = mutable.Map.empty[InputSlot, TermShapeHost]
  private val results = mutable.Map.empty[TermSymbol, ResultSlot]

  // Includes property declarations synthesized by named-tuple resolution, which
  // have source expressions but are not separate nodes in the source syntax.
  def slots: Iterator[InputSlot] = values.keysIterator

  private[semantics] def register(slot: InputSlot)(connect: ResolutionContext.Listener => Unit)
      (using ResolutionContext): TermShapeHost = values.get(slot) match
    case S(host) => host
    case N =>
      val host = new TermShapeHost
      values(slot) = host
      // Even an unused/unproductive definition has a completed, empty observation.
      host.inferenceHost
      connect(host.publish)
      host

  /** Whether resolution prepared this slot in the current compilation unit. */
  def isPrepared(slot: InputSlot): Bool = values.contains(slot)

  /** The values a caller can receive through `member`. Connect the declaration once, before
    * replaying any of its results, so recursive members share the same slot.
    */
  private[semantics] def resultSlot(member: TermDefinition, inferredValues: Opt[TermShapeHost])
      (connect: ResolutionContext.Listener => Unit)(using ResolutionContext): ResultSlot = results.get(member.tsym) match
    case S(slot) => slot
    case N =>
      val slot = new ResultSlot(ErasureInputs.Representation(member, inferredValues))
      results(member.tsym) = slot
      slot.inferenceHost
      connect(value => slot.publish(ErasureInputs.Returned(member, value)))
      slot

  /** The completed inputs to a source slot, including the values or declared results of the
    * overrides that `includeOverride` accepts.
    */
  def observations(slot: InputSlot)(includeOverride: TermDefinition => Bool): Iterator[TermShape | TermDefinition] =
    val host = values.getOrElse(slot, lastWords("Source slot was not prepared for erasure"))
    val overriding = slot match
      case member: TermSymbol =>
        for
          slot <- results.get(member).iterator
          case source: ErasureInputs.Representation <- ErasureInputs.completed(slot) if includeOverride(source.member)
          value <- source.inputs
        yield value
      case _ => Iterator.empty
    ErasureInputs.completed(host) ++ overriding

private[hkmc2] object ErasureInputs:
  /** Symbols whose variable values or definition results supply runtime representations.
    * Elaboration temporaries include the saved value restored by a backtracking assignment.
    */
  type InputSymbol = LocalVarSymbol | TermSymbol
  type InputSlot = InputSymbol | LambdaResultSlot

  private def completed[A](host: Host[A]): Iterator[A] =
    assert(host.originalData.completed, "Erasure requires completed value observations")
    host.shapes.iterator

  private[semantics] final case class Returned(member: TermDefinition, value: TermShape)
  private[semantics] final case class Representation(member: TermDefinition, inferred: Opt[TermShapeHost]):
    def inputs: Iterator[TermShape | TermDefinition] = inferred.fold(Iterator.single(member))(completed)

  private given CandidateKey[Returned | Representation] with
    def apply(result: Returned | Representation)(using ResolutionContext): Any = result match
      case Returned(member, value) => (member.tsym, ShapeIdentity.key(value))
      case source: Representation => source.member.tsym

  /** The values clients can read from a member across all receivers, together with the
    * declarations that constrain its runtime representation. A fixed representation such as
    * a promise still forwards every overriding implementation's caller-visible values.
    */
  private[semantics] final class ResultSlot(private val representation: Representation)
      extends Host[Returned | Representation]:
    def showDbg(using DebugPrinter): Str = "override results"
    private[ErasureInputs] def publish(result: Returned | Representation)(using ResolutionContext): Unit = result match
      case _: Representation if representation.inferred.isEmpty => ()
      case _ => inferenceHost.publish(result)
    def include(overriding: ResultSlot)(using ResolutionContext): Unit =
      publish(overriding.representation)
      overriding.subscribeToShapes(publish)
    def listenValues(receive: ShapeListener[Returned])(using ResolutionContext): Unit = subscribeToShapes:
      case value: Returned => receive(value)
      case _: Representation => ()

