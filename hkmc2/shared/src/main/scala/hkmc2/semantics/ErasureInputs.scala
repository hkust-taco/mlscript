package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*
import ErasureInputs.{InputSlot, InputSymbol}

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

/** The source values of declarations in this compilation unit. Erasure reads the completed
  * observations. Later writes in an importing unit reach that unit's copy. */
private[hkmc2] final class ErasureInputs:
  private val values = mutable.Map.empty[InputSlot, TermShapeHost]

  /** Collect the possible values of the block's declarations and lambda results for erasure.
    * Observation starts before interface exposure so it also sees values supplied by external callers. */
  private[semantics] def observeBlock(root: Statement, resolver: NewResolver)(using ResolutionContext): Unit =
    val declarations = new ErasureDeclarations(root)
    declarations.parameters.values.foreach: p =>
      observeVariable(p.sym, resolver)
    declarations.variables.foreach:
      case symbol: VarSymbol => observeVariable(symbol, resolver)
      case symbol: TermSymbol if symbol.needsErasure => observeSymbol(symbol, resolver)(resolver.listenMemberVariable(symbol))
      // A temporary that elaboration declares (see ErasureDeclarations) is observed like a variable,
      // unless its representation was fixed when it was created.
      case symbol: TempSymbol if symbol.erasedType.isEmpty =>
        observeSymbol(symbol, resolver)(resolver.listenTerm(SimpleRef(symbol)(N)))
      case _ => ()
    declarations.statements.foreach:
      case td: TermDefinition => observeDefinition(td, resolver)
      case lam: Lam if !lam.resultSlot.isErasureReady =>
        register(lam.resultSlot): publish =>
          resolver.listenTermViews(lam.body)(publish)
      case _ => ()

  private def observeSymbol(symbol: InputSymbol, resolver: NewResolver)(connect: ResolutionContext.Listener => Unit)(using ResolutionContext): Opt[TermShapeHost] =
    Option.when(rctx.state.isOwnedSym(symbol))(register(symbol): publish =>
      // Expand instances while their type substitutions are in scope. Erasure reads the block's completed observations.
      connect(shape => resolver.listenInstanceViews(shape)(publish))
    )

  private def observeVariable(symbol: VarSymbol, resolver: NewResolver)(using ResolutionContext): Opt[TermShapeHost] =
    if symbol.isErasureReady then N else observeSymbol(symbol, resolver)(resolver.listenTerm(SimpleRef(symbol)(N)))

  private[semantics] def observeDefinition(td: TermDefinition, resolver: NewResolver)(using ResolutionContext): Opt[TermShapeHost] =
    if !td.tsym.needsErasure then N else observeSymbol(td.tsym, resolver): publish =>
      // The function body returns its payload. AsyncLowering wraps that body later;
      // the callable's promise representation is assigned separately by Erasure.
      td.body.foreach(body => resolver.listenResult(body)(publish))
      // A field that assignments can replace also holds the values assigned to it, including those that other
      // compilation units can assign when it is exposed (see `NewResolver.assignField` and `InterfaceExposure`). Assignments
      // in later blocks and in other compilation units reach consumer copies of the field's host instead, which
      // the field's representation does not include: lowering converts their values to that representation.
      if resolver.isAssignableField(td) then resolver.listenMemberVariable(td.tsym)(publish)

  /** Include a value written to a record copy when inferring the original field's runtime representation. */
  private[semantics] def observeCopyWrite(copy: RecordFieldSymbol, value: TermShape, resolver: NewResolver)(using caller: ResolutionContext): Unit =
    val root = copy.root
    if root isnt copy then
      // The declaration's representation is shared across calls. Interpret the assigned value with the
      // writer's type arguments so a write in a generic function contributes its instantiated shapes.
      val declaration = caller.withInstances(TypeSubstitution.empty)
      root.defn.flatMap(observeDefinition(_, resolver)(using declaration)).foreach: representation =>
        resolver.listenInstanceViews(value)(representation.publish)

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

  /** The values of this declaration when resolution of its defining block completed. */
  def observations(slot: InputSlot): Iterator[TermShape] =
    val host = values.getOrElse(slot, lastWords("Source slot was not prepared for erasure"))
    assert(host.originalData.completed, "Erasure requires completed value observations")
    host.shapes.iterator

private[hkmc2] object ErasureInputs:
  /** Symbols whose variable values or definition results supply runtime representations.
    * Elaboration temporaries include the saved value restored by a backtracking assignment.
    */
  type InputSymbol = LocalVarSymbol | TermSymbol
  type InputSlot = InputSymbol | LambdaResultSlot

