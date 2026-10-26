package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*


object ResolutionSources:
  final case class Scope(binders: Set[VarSymbol], boundaries: Set[ResolutionBoundary])

  /** Visit source dependencies without flattening nested definitions. Seal
    * every host belonging to the unit, including children
    * omitted by the ordinary term traversal: parent clauses, auxiliary lists,
    * quantifier bounds, patterns, refinements, and handler definitions.
    */
  def children(statement: Statement)(visit: Statement => Unit, pattern: Pattern => Unit): Unit =
    import Term.*
    statement match
      case cls: ClassLikeDef =>
        cls.ext.foreach(visit)
        cls.auxParams.foreach(_.subTerms.foreach(visit))
        cls match
          case definition: PatternDef => pattern(definition.pattern)
          case _ => ()
      case Forall(parameters, _, _) => parameters.foreach: parameter =>
        parameter.lb.foreach(visit)
        parameter.ub.foreach(visit)
      case IfLike(_, _, split) =>
        def branches(split: SimpleSplit): Unit = split match
          case SimpleSplit.Cons(SimpleSplit.Head.Match(_, pat, consequent), tail) =>
            pattern(pat)
            branches(consequent)
            branches(tail)
          case SimpleSplit.Cons(_, tail) => branches(tail)
          case _ => ()
        branches(split)
      case New(_, _, refinement) => refinement.foreach(value => visit(value._2.blk))
      case Handle(_, _, _, symbol, handlers, _) =>
        symbol.defn.foreach(visit)
        handlers.foreach(handler => visit(handler.td))
      case _ => ()
    statement match
      case Rcd(_, statements) => statements.foreach(visit)
      case _ => statement.subStatements.foreach(visit)

  def patternChildren(source: Pattern)(visit: Statement => Unit, pattern: Pattern => Unit): Unit = source match
    // Pattern.children flattens these cases for location calculations. Their
    // nested patterns still have inference hosts and source metadata of their own.
    case Pattern.Record(fields) => fields.foreach((_, nested) => pattern(nested))
    case Pattern.Guarded(nested, guard) =>
      pattern(nested)
      visit(guard)
    case _ => source.children.foreach:
      case nested: Pattern => pattern(nested)
      case term: Term => visit(term)
      case _ => ()


/** Source facts recorded by the defining compilation unit, before its graph is
  * observed. They do not vary with activation or import context. Consumers read
  * them through the source symbol/node, without copying them into memo tables.
  */
final class ResolutionSources:
  import ResolutionSources.Scope
  val definitions = mutable.Map.empty[AnyDefinitionSymbol, Scope]
  val sites = mutable.Map.empty[FlowSymbol, Set[VarSymbol]]
  val parameterSignatures = mutable.Map.empty[VarSymbol, DeclaredType]
  val recordReads = mutable.Map.empty[Identity[Pattern.Record], (FlowSymbol, Term)]
