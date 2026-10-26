package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*


object ResolutionWorkspace:
  /** A pending source summary is a one-shot computation, not an inference
    * edge. Observers are detached once it completes. No importer inherits these
    * continuations.
    */
  final class PendingDependencies:
    private val listeners = mutable.ArrayBuffer.empty[(ResolutionContext, ShapeListener[Set[VarSymbol]])]
    val watched = mutable.Set.empty[TypeResolution]
    private val detach = mutable.ArrayBuffer.empty[() => Unit]
    private var completed = false
    def listen(listener: ShapeListener[Set[VarSymbol]])(using context: ResolutionContext): Unit =
      // Preserve the graph and substitution used to register each continuation.
      listeners += ((context, listener))
    def observe(cancel: () => Unit): Unit =
      if completed then cancel() else detach += cancel
    def isPending: Bool = !completed
    def cancel(): Unit =
      completed = true
      detach.foreach(_())
      detach.clear()
      watched.clear()
      listeners.clear()
    def complete(binders: Set[VarSymbol]): Unit =
      val callbacks = listeners.toList
      cancel()
      callbacks.foreach: (context, listener) =>
        listener(binders)(using context)
