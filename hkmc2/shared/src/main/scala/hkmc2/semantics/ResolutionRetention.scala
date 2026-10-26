package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*


object ResolutionRetention:
  /** Tables expose their entries only to the finalization pass. The predicate
    * selects entries, never constructs values or invokes inference callbacks.
    */
  trait Table:
    def retain(keep: (ResolutionContext, Any) => Bool): Unit

/** Conservative ownership of resolution work. A computation belongs to the
  * named body being elaborated, including its anonymous closures. Shared graph
  * entries record every body that uses them. Work outside a named body is kept.
  * This bookkeeping is temporary; finalization leaves only the selected graph.
  */
private[hkmc2] final class ResolutionRetention(owner: Elaborator.State):
  import ResolutionRetention.Table
  /** Reading an entry depends on the code that produced it, not on every other
    * reader. This distinction keeps sharing a nominal interface from making all
    * its users live, while preserving inputs already fed into a reachable host.
    */
  private final class Uses:
    var readers = Set.empty[Opt[AnyDefinitionSymbol]]
    var writers = Set.empty[AnyDefinitionSymbol]
    def read(code: Opt[AnyDefinitionSymbol]): Unit = readers += code
    def write(code: Opt[AnyDefinitionSymbol]): Unit =
      read(code)
      writers ++= code
    def needed(keeps: AnyDefinitionSymbol => Bool): Bool = readers.exists(_.forall(keeps))
  private val tables = mutable.Map.empty[Table, mutable.Map[(ResolutionContext, Any), Uses]]
  private val hosts = mutable.Map.empty[Publisher.Data[?], Uses]
  val exposedDefinitions = mutable.Set.empty[AnyDefinitionSymbol]
  val exposedValues = mutable.Set.empty[Identity[Term]]
  // Synthetic property symbols and invocation sites may not occur as nodes in
  // the written AST. Remember their enclosing code only until finalization.
  val sourceOwners = mutable.Map.empty[Symbol, Opt[AnyDefinitionSymbol]]

  private def code(using context: ResolutionContext): Opt[AnyDefinitionSymbol] =
    context.code.filter(_.getState is owner)
  def source(symbol: Symbol)(using ResolutionContext): Unit =
    sourceOwners.getOrElseUpdate(symbol, code)
  private def entry(table: Table, key: Any)(using context: ResolutionContext): Uses =
    tables.getOrElseUpdate(table, mutable.Map.empty).getOrElseUpdate((context, key), new Uses)
  def use(table: Table, key: Any)(using ResolutionContext): Unit = entry(table, key).read(code)
  def define(table: Table, key: Any)(using ResolutionContext): Unit = entry(table, key).write(code)
  def useHost(host: Publisher.Data[?])(using ResolutionContext): Unit =
    hosts.getOrElseUpdate(host, new Uses).read(code)
  def publishHost(host: Publisher.Data[?])(using ResolutionContext): Unit =
    hosts.getOrElseUpdate(host, new Uses).write(code)
  /** Inference is an overapproximation: even a never-called body may already
    * have contributed inputs to a live helper. Preserve those inputs' defining
    * code as well as static callees; opaque callbacks can still refer to it.
    */
  def close(reachability: ResolutionReachability): Unit =
    var changed = true
    while changed do
      changed = false
      val uses = tables.valuesIterator.flatMap(_.valuesIterator) ++ hosts.valuesIterator
      val needed = uses.filter(_.needed(reachability.keeps)).flatMap(_.writers).toSet
      needed.foreach: symbol =>
        if !reachability.keeps(symbol) then
          reachability.include(symbol)
          changed = true
  def finish(reachable: AnyDefinitionSymbol => Bool): Unit =
    tables.foreach: (table, uses) =>
      table.retain((context, key) => uses.get((context, key)).forall(_.needed(reachable)))
    hosts.foreach: (host, users) =>
      host.retainListeners(code => code.forall(symbol => !(symbol.getState is owner) || reachable(symbol)), users.needed(reachable))
  def retained(host: Publisher.Data[?], reachable: AnyDefinitionSymbol => Bool): Bool =
    hosts.get(host).forall(_.needed(reachable))
