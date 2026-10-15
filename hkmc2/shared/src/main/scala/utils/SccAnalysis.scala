package hkmc2.utils

import scala.annotation.tailrec
import scala.collection.mutable.{Stack as MutStack, LinkedHashMap, Set as MutSet, Map as MutMap, ListBuffer}

import hkmc2.utils.shorthands.*


/**
  * Methods to implement:
  * - [[successors]]: The successors of each node
  * - [[handleScc]]: Every node reachable from any query is visited at most once, and each SCC is reported
  * exactly once to [[handleScc]]. By the time `handleScc(scc)` runs, every SCC reachable from `scc` other than `scc`
  * itself has already been handled. [[handleScc]] must not itself start a query.
  * The `sccId` uniquely identifies the SCC and starts from 0.
  * It stays unique across queries but an SCC handled later does not necessarily get a larger id.
  * - [[isHandled]]: Whether a node's SCC has already been handled. Must become true for every member of an
  * SCC after [[handleScc]] is done.
  * The implementations must use a node identity that is consistent with `==`/`##`
  */
abstract class SccAnalysis[A]:
  
  // The out-edges of `node`.
  protected def successors(node: A): IterableOnce[A]
  
  // Whether `node`'s SCC has already been handled
  protected def isHandled(node: A): Bool
  
  // Called once per SCC; `members` is never empty.
  protected def handleScc(members: Ls[A], sccId: Int): Unit
  
  final def query(root: A): Unit =
    if !isHandled(root) then run(root)
  
  final def queryAll(roots: IterableOnce[A]): Unit =
    roots.iterator.foreach(query)
  
  // The stack for tarjan's algorithm
  private val stack = LinkedHashMap.empty[A, Int]
  private var counter = 0
  
  // The dfs call stack frame
  private final class Frame(val node: A, val idx: Int, val succs: Iterator[A]):
    var low: Int = idx
  private val frames = MutStack.empty[Frame]
  
  
  private def run(from: A): Unit =
    
    def enter(node: A): Unit =
      val idx = counter
      counter += 1
      stack(node) = idx
      frames.push(Frame(node, idx, successors(node).iterator))
    end enter
    
    def closeScc(rootIdx: Int): Unit =
      @tailrec def go(acc: Ls[A]): Ls[A] =
        val (n, idx) = stack.last
        stack.remove(n)
        if idx == rootIdx then n :: acc else go(n :: acc)
      handleScc(go(Nil), rootIdx)
    end closeScc
    
    assert(frames.isEmpty)
    assert(stack.isEmpty)
    
    enter(from)
    while frames.nonEmpty do
      val f = frames.top
      if f.succs.hasNext then
        val w = f.succs.next()
        if isHandled(w) then () // an edge into an already closed SCC, do nothing
        else stack.get(w) match
          case S(iw) => f.low = f.low.min(iw) // back edge: `w` is still on the stack
          case N => enter(w) // tree edge: descend
      else
        frames.pop()
        if f.low == f.idx then closeScc(f.idx)
        if frames.nonEmpty then
          val parent = frames.top
          parent.low = parent.low.min(f.low)
  
  end run

end SccAnalysis


object SccAnalysis:
  
  trait NoopHandling[A] extends SccAnalysis[A]:
    protected def handleScc(members: List[A], sccId: Int): Unit = ()
  
  trait CachingComputedSccValue[A, ComputedValuePerNodeType, ComputedValuePerSccType] extends SccAnalysis[A]:
    val computed = MutMap.empty[A, ComputedValuePerNodeType]
    
    protected def computeValuePerScc(members: Ls[A], sccId: Int): ComputedValuePerSccType
    
    protected def computeValuePerNode(node: A, members: Ls[A], computedValueForScc: ComputedValuePerSccType, sccId: Int): ComputedValuePerNodeType
    
    final protected def isHandled(node: A): Bool =
      computed.contains(node)
    
    abstract override protected def handleScc(members: Ls[A], sccId: Int): Unit =
      val sccValue = computeValuePerScc(members, sccId)
      for m <- members do
        computed(m) = computeValuePerNode(m, members, sccValue, sccId)
      super.handleScc(members, sccId)
  
  trait CachingComputedNodeValue[A, ComputedValueType] extends CachingComputedSccValue[A, ComputedValueType, ComputedValueType]:
    final protected def computeValuePerNode(
      node: A,
      members: Ls[A],
      computedValueForScc: ComputedValueType,
      sccId: Int
    ): ComputedValueType = computedValueForScc
  
  trait Caching[A] extends SccAnalysis[A]:
    val handled = MutSet.empty[A]
    
    final protected def isHandled(node: A): Bool =
      handled.contains(node)
    
    abstract override protected def handleScc(members: Ls[A], sccId: Int): Unit =
      handled.addAll(members)
      super.handleScc(members, sccId)
  
  trait Collecting[A] extends SccAnalysis[A]:
    val collected = ListBuffer.empty[Ls[A]]
    
    abstract override protected def handleScc(members: Ls[A], sccId: Int): Unit =
      collected.addOne(members)
      super.handleScc(members, sccId)
  
  
  def sccsFrom[A](succs: A => IterableOnce[A], roots: IterableOnce[A]): Ls[Ls[A]] =
    object traversal extends NoopHandling[A] with Caching[A] with Collecting[A]:
      protected def successors(node: A): IterableOnce[A] = succs(node)
    
    traversal.queryAll(roots)
    traversal.collected.toList

end SccAnalysis
