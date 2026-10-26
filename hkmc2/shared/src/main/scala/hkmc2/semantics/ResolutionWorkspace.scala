package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*


object ResolutionWorkspace:
  enum DependencyMode:
    case Bindings, UnguardedBindings, Instances

  /** Recomputable summaries never establish graph identity or install an edge.
    * Keep only the consumer's observations: inheriting a memoized answer is an
    * optimization, not a condition of observing the imported graph correctly.
    */
  final class Memo[K, V]:
    private val entries = mutable.Map.empty[(ResolutionContext.Graph, K), V]
    def get(key: K)(using context: ResolutionContext): Opt[V] = entries.get((context.graph, key))
    def update(key: K, value: V)(using context: ResolutionContext): Unit = entries((context.graph, key)) = value
    def getOrElseUpdate(key: K, value: => V)(using context: ResolutionContext): V =
      entries.getOrElseUpdate((context.graph, key), value)

  /** A pending source summary is a one-shot computation, not an inference
    * edge. Observers are detached once it completes, or when the unit ends with
    * an unresolved source error. No importer inherits these continuations.
    */
  final class PendingDependencies:
    private val listeners = mutable.ArrayBuffer.empty[(ResolutionContext, ShapeListener[Set[VarSymbol]])]
    val watched = mutable.Set.empty[TypeResolution]
    private val detach = mutable.ArrayBuffer.empty[() => Unit]
    private var completed = false
    def listen(listener: ShapeListener[Set[VarSymbol]])(using context: ResolutionContext): Unit =
      // Equal inference contexts can belong to different bodies. Preserve each
      // continuation's owner so its resulting edges have the correct retention.
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

/** The mutable work of the current compilation. No graph node or listener may
  * capture this object: callbacks obtain the active consumer's workspace through
  * ResolutionContext. Compiled artifacts release it after erasure and lowering.
  */
private[hkmc2] final class ResolutionWorkspace(owner: Elaborator.State):
  import ResolutionWorkspace.*
  val retention = new ResolutionRetention(owner)
  val pendingDependencies = mutable.Map.empty[(ResolutionContext.Graph, TypeResolution), PendingDependencies]
  val contexts = mutable.Map.empty[ResolutionContext.Graph, ResolutionContext.Graph]
  var reporter: Raise | Null = null
  var traceLogger: TraceLogger = TraceLogger.silent(using new DebugPrinter(S(owner)))
  val exposureInputs = mutable.LinkedHashMap.empty[(ShapeIdentity.Key, ResolutionContext.Graph), InterfaceExposure.Input]
  val pending = mutable.Map.empty[Identity[Publisher[?]], Publisher.Data[?]]
  val resolutionProblems =
    mutable.LinkedHashMap.empty[Identity[NewSel | App], mutable.ListBuffer[() => Ls[(Message, Opt[Loc])]]]
  // The references, selections, and instantiations written in this unit's current block,
  // in elaboration order, with the lexical scope in which each is written (see
  // ResolutionContext.checkAccess). Its references without explicit bindings are also
  // the worklist of NewResolver.settleUnboundReferences, which runs before checkAccess.
  val accessSites = mutable.ArrayBuffer.empty[(NewResolvable | New, SrcScope)]
  // What flow has revealed about the implicit namespaces of this unit's references
  // (see NewResolver.unresolvedRef). Unlike the block-local tables, this outlives the
  // reference's block: a later worksheet block can still reveal a namespace, which
  // must be diagnosed against the settled reference.
  val implicitNamespaces = mutable.HashMap.empty[Identity[UnresolvedRef], ImplicitNamespaces]
  val errors = mutable.Set.empty[Identity[PossiblyErroneous]]
  val substitutions = mutable.HashMap.empty[TypeSubstitution, TypeSubstitution]
  val typeReferences = new DeclaredType.References(substitutions)
  val membersCache = new Memo[(TermShape, MemberKey), MemberLookup]
  val dependencySummaries = new Memo[(TypeResolution, DependencyMode), Opt[Set[VarSymbol]]]
  val regularTypes = new Memo[TypeResolution, Bool]
