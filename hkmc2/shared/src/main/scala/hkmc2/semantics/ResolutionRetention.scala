package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*


object ResolutionRetention:
  /** Reading an entry depends on the code that produced it, not on every other
    * reader. This distinction keeps sharing a nominal interface from making all
    * its users live, while preserving inputs already fed into a reachable host.
    */
  class Uses:
    private var readers = Set.empty[Opt[AnyDefinitionSymbol]]
    private[semantics] var writers = Set.empty[AnyDefinitionSymbol]
    def read(code: Opt[AnyDefinitionSymbol]): Unit = readers += code
    def write(code: Opt[AnyDefinitionSymbol]): Unit =
      read(code)
      writers ++= code
    def needed(keeps: AnyDefinitionSymbol => Bool): Bool = readers.exists(_.forall(keeps))

  final class Entry[V](var value: V) extends Uses

  /** Usage belongs to the entries being tracked. Finalization selects their
    * values and discards the tracking records, without replaying inference.
    */
  trait Table:
    def uses: Iterator[Uses]
    def finish(keep: AnyDefinitionSymbol => Bool): Unit

/** Conservative ownership of resolution work. A computation belongs to the
  * named body being elaborated, including its anonymous closures. Shared graph
  * entries record every body that uses them. Work outside a named body is kept.
  * This bookkeeping is temporary; finalization leaves only the selected graph.
  */
private[hkmc2] final class ResolutionRetention(owner: Elaborator.State):
  import ResolutionRetention.{Table, Uses}
  private val tables = mutable.ArrayBuffer.empty[Table]
  private val hosts = mutable.ArrayBuffer.empty[Publisher.Data[?]]
  val exposedDefinitions = mutable.Set.empty[AnyDefinitionSymbol]
  val exposedValues = mutable.Set.empty[Identity[Term]]
  // Synthetic property symbols and invocation sites may not occur as nodes in
  // the written AST. Remember their enclosing code only until finalization.
  val sourceOwners = mutable.Map.empty[Symbol, Opt[AnyDefinitionSymbol]]

  private def code(using context: ResolutionContext): Opt[AnyDefinitionSymbol] =
    context.code.filter(_.getState is owner)
  def source(symbol: Symbol)(using ResolutionContext): Unit =
    sourceOwners.getOrElseUpdate(symbol, code)
  def track(table: Table): Unit = tables += table
  def use(entry: Uses)(using ResolutionContext): Unit = entry.read(code)
  def define(entry: Uses)(using ResolutionContext): Unit = entry.write(code)
  private def hostUses(host: Publisher.Data[?]): Uses =
    if host.retentionUses == null then
      host.retentionUses = new Uses
      hosts += host
    host.retentionUses.nn
  def useHost(host: Publisher.Data[?])(using ResolutionContext): Unit = use(hostUses(host))
  def publishHost(host: Publisher.Data[?])(using ResolutionContext): Unit = define(hostUses(host))
  /** Inference is an overapproximation: even a never-called body may already
    * have contributed inputs to a live helper. Preserve those inputs' defining
    * code as well as static callees; opaque callbacks can still refer to it.
    */
  def close(reachability: ResolutionReachability): Unit =
    var changed = true
    while changed do
      changed = false
      val uses = tables.iterator.flatMap(_.uses) ++ hosts.iterator.map(_.retentionUses.nn)
      val needed = uses.filter(_.needed(reachability.keeps)).flatMap(_.writers).toSet
      needed.foreach: symbol =>
        if !reachability.keeps(symbol) then
          reachability.include(symbol)
          changed = true
  def finish(reachable: AnyDefinitionSymbol => Bool): Unit =
    tables.foreach(_.finish(reachable))
    hosts.foreach: host =>
      host.retainListeners(code => code.forall(symbol => !(symbol.getState is owner) || reachable(symbol)),
        host.retentionUses.nn.needed(reachable))
      host.retentionUses = null
