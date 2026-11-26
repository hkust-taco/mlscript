package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*
import ResolvedValues.{InputSlot, InputSymbol}

/** Source declarations and writable field copies in an elaborated block.
  * Several declarations are outside subStatements: split bindings, handler parameters,
  * auxiliary constructor parameters, and the definitions synthesized for record fields.
  * Include them so clients see declarations that do not appear as ordinary statements.
  *
  * Variables include the temporaries that hold a split's scrutinee or save the value of `x`
  * across `set x = v in body`. These slots need the representation of the value they hold,
  * including when a match or a restored assignment reads an unboxed primitive on Wasm.
  */
private[hkmc2] final class SourceDeclarations(root: Statement):
  val statements = mutable.ArrayBuffer.empty[Statement]
  val parameters = mutable.LinkedHashMap.empty[VarSymbol, Param]
  val variables = mutable.LinkedHashSet.empty[InputSymbol]
  val copiedFields = mutable.ArrayBuffer.empty[RecordFieldSymbol]
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
      case block: Blk => block.resolvedFields.foreach: field =>
        field.origin match
          case RecordFieldSymbol.Origin.Copied(_) => copiedFields += field
          case _ => field.defn.foreach(visit)
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
private[hkmc2] final class ResolvedValues:
  private val values = mutable.Map.empty[InputSlot, TermShapeHost]

  /** Collect the possible values of the block's declarations and lambda results while resolution
    * finishes. These include values admitted by the public interface and declarations discovered on demand. */
  private[semantics] def observeBlock(root: Blk, resolver: NewResolver)(resolve: => Unit)(using ResolutionContext): Unit =
    val declarations = new SourceDeclarations(root)
    def variable(sym: LocalVarSymbol): Unit =
      observeSymbol(sym, resolver)(resolver.listenTerm(SimpleRef(sym)(N)))
    declarations.parameters.values.foreach(p => variable(p.sym))
    declarations.variables.foreach:
      case sym: LocalVarSymbol => variable(sym)
      case sym: TermSymbol => observeSymbol(sym, resolver)(resolver.listenMemberVariable(sym))
    declarations.statements.foreach:
      case td: TermDefinition => observeDefinition(td, resolver)
      case lam: Lam =>
        register(lam.resultSlot): publish =>
          resolver.listenTermViews(lam.body)(publish)
      case _ => ()

    // Interface exposure can discover new fields, and observing a field can in turn expose a value.
    // Keep this observation live until exposure has processed those values.
    val fields = rctx.state.discoveredFields
    val detach = fields.inferenceHost.observe: (field, scope) =>
      given ResolutionContext = scope
      field.origin match
        case RecordFieldSymbol.Origin.Copied(_) =>
          // Listen across all calls. The assignment host replays each write with its own type arguments.
          observeSymbol(field, resolver)(resolver.listenMemberVariable(field))
        case _ => field.defn.foreach(observeDefinition(_, resolver))
    try resolve
    finally
      detach()
      root.resolvedFields = fields.shapes.iterator.map(_._1).toList
      rctx.state.discoveredFields = new DiscoveredFields

  private def observeSymbol(symbol: InputSymbol, resolver: NewResolver)(connect: ResolutionContext.Listener => Unit)(using ResolutionContext): Unit =
    if rctx.state.isOwnedSym(symbol) then register(symbol): publish =>
      // Expand instances while their type substitutions are in scope.
      connect(shape => resolver.listenInstanceViews(shape)(publish))

  private def observeDefinition(td: TermDefinition, resolver: NewResolver)(using ResolutionContext): Unit =
    observeSymbol(td.tsym, resolver): publish =>
      // An async function's body produces the payload of the promise its callers receive.
      td.body.foreach(body => resolver.listenResult(body)(publish))
      // In the defining block this includes writes admitted by interface exposure. Subsequent writes
      // in importing units reach consumer-local copies of the field's assignment host.
      if resolver.isAssignableField(td) then resolver.listenMemberVariable(td.tsym)(publish)

  private[semantics] def register(slot: InputSlot)(connect: ResolutionContext.Listener => Unit)
      (using ResolutionContext): Unit =
    if !values.contains(slot) then
      val host = new TermShapeHost
      values(slot) = host
      // Even an unused/unproductive definition has a completed, empty observation.
      host.inferenceHost
      connect(host.publish)

  /** Whether resolution prepared this slot in the current compilation unit. */
  def isPrepared(slot: InputSlot): Bool = values.contains(slot)

  /** The values of this declaration when resolution of its defining block completed. */
  def observations(slot: InputSlot): Iterator[TermShape] =
    val host = values.getOrElse(slot, lastWords("No resolved values were recorded for this declaration"))
    assert(host.originalData.completed, "Reading resolved values before block completion")
    host.shapes.iterator

private[hkmc2] object ResolvedValues:
  /** Symbols whose variable values or definition results supply runtime representations.
    * Elaboration temporaries include the saved value restored by a backtracking assignment.
    */
  type InputSymbol = LocalVarSymbol | TermSymbol
  type InputSlot = InputSymbol | LambdaResultSlot

