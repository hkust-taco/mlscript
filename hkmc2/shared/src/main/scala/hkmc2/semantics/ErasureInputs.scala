package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*

/** Source declarations needed both when observing inference and when assigning representations.
  * Several declarations are outside subStatements: split bindings, handler parameters,
  * auxiliary constructor parameters, and the definitions synthesized for record fields.
  * Keep their enumeration shared so every delayed slot is prepared before erasure reads it.
  */
private[hkmc2] final class ErasureDeclarations(root: Statement):
  val statements = mutable.ArrayBuffer.empty[Statement]
  val parameters = mutable.LinkedHashMap.empty[VarSymbol, Param]
  val variables = mutable.LinkedHashSet.empty[VarSymbol | TermSymbol]
  val mutableFields = mutable.Set.empty[TermSymbol]
  private val visited = mutable.Set.empty[Identity[Statement]]

  private def parameter(p: Param): Unit =
    parameters(p.sym) = p
    p.subTerms.foreach(visit)

  private def variable(sym: VarSymbol | TermSymbol): Unit =
    variables += sym
    val declaration = sym match
      case sym: VarSymbol => sym.decl
      case sym: TermSymbol => sym.decl
    declaration match
      case S(p: Param) => parameter(p)
      case _ => ()

  private def pattern(pat: Pattern): Unit =
    pat.variables.symbols.foreach(variable)
    pat.subTerms.foreach(visit)

  private def split(branches: SimpleSplit): Unit = branches match
    case SimpleSplit.Cons(SimpleSplit.Head.Let(sym: VarSymbol, _), tail) =>
      variable(sym)
      split(tail)
    case SimpleSplit.Cons(SimpleSplit.Head.Match(_, pat, consequent), tail) =>
      pattern(pat)
      split(consequent)
      split(tail)
    case SimpleSplit.Cons(_, tail) => split(tail)
    case _ => ()

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
      case LetDecl(sym: (VarSymbol | TermSymbol), _) => variable(sym)
      case Ref(sym: VarSymbol) => variable(sym)
      case SimpleRef(sym: VarSymbol) => variable(sym)
      case IfLike(_, _, branches) => split(branches)
      case New(_, _, refinement) => refinement.foreach: (symbol, body) =>
        symbol.defn.fold(visit(body.blk))(visit)
      case Rcd(mut, stats) =>
        if mut then stats.collect { case field: RcdField => field.tsym }.foreach(mutableFields += _)
        stats.foreach(visit)
      case field: RcdField => field.tsym.defn.foreach(visit)
      case _ => ()
    statement.subStatements.foreach(visit)
    // Legacy expansion can insert executable terms while sharing their source children.
    statement match
      case term: Resolvable => visit(term.expanded)
      case _ => ()

  visit(root)

/** Inference-only inputs to the representation pass. Each source slot owns a host in its
  * defining compilation unit. Forwarding listeners capture only that host; imported inference
  * writes to the consumer's publisher copy, never to these completed original candidates.
  * No erased types or mutable bookkeeping are stored on source symbols during resolution.
  */
private[hkmc2] final class ErasureInputs:
  private val values = mutable.Map.empty[Symbol, TermShapeHost]

  // Includes property declarations synthesized by named-tuple resolution, which
  // have source expressions but are not separate nodes in the source syntax.
  def symbols: Ls[Symbol] = values.keysIterator.toList

  private[semantics] def register(symbol: Symbol)(connect: ResolutionContext.Listener => Unit)
      (using ResolutionContext): Unit = if !values.contains(symbol) then
    val host = new TermShapeHost
    values(symbol) = host
    // Even an unused/unproductive definition has a completed, empty observation.
    host.inferenceHost
    connect(host.publish)

  def shapes(symbol: Symbol): Ls[TermShape] =
    val host = values.getOrElse(symbol, lastWords("Source slot was not prepared for erasure"))
    assert(host.originalData.completed, "Erasure requires completed value observations")
    host.shapes.toList

