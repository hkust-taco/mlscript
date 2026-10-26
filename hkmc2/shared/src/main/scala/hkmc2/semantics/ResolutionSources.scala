package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*


object ResolutionSources:
  final case class Scope(binders: Set[VarSymbol], boundaries: Set[ResolutionBoundary])



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
