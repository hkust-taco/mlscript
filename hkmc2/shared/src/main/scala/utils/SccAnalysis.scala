package hkmc2.utils

import scala.annotation.tailrec
import scala.collection.mutable.{Stack as MutStack, LinkedHashMap, Set as MutSet, ListBuffer}

import hkmc2.utils.shorthands.*


/**
  * Methods to override:
  * - [[successors]]: The succesors of each node
  * - [[handleScc]]: Every node reachable from any query is visited at most once, and each SCC is reported
  * exactly once to [[handleScc]]. By the time `handleScc(scc)` runs, every SCC reachable from `scc` other than `scc`
  * itself has already been handled. [[handleScc]] must not itself start a query.
  * - [[isHandled]]: Whether a node's SCC has already been handled. Must become true for every member of an
  * SCC after [[handleScc]] is done.
  * The overridden methods must use a node identity that is consistent with `==`/`##`
  */
abstract class SccAnalysis[A]:
  
  // The out-edges of `node`.
  protected def successors(node: A): IterableOnce[A]
  
  // Whether `node`'s SCC has already been handled
  protected def isHandled(node: A): Bool
  
  // Called once per SCC; `members` is never empty.
  protected def handleScc(members: Ls[A]): Unit
  
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
      handleScc(go(Nil))
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
  
  trait DefaultNoopHandling[A] extends SccAnalysis[A]:
    override protected def handleScc(members: List[A]): Unit = ()
  
  trait DefaultCaching[A] extends SccAnalysis[A]:
    val handled = MutSet.empty[A]
    
    final override protected def isHandled(node: A): Bool =
      handled.contains(node)
    
    abstract override protected def handleScc(members: Ls[A]): Unit =
      handled.addAll(members)
      super.handleScc(members)
  
  trait DefaultCollecting[A] extends SccAnalysis[A]:
    val collected = ListBuffer.empty[Ls[A]]
    
    abstract override protected def handleScc(members: Ls[A]): Unit =
      collected.addOne(members)
      super.handleScc(members)
  
  abstract class SccFromSuccFun[A](succs: A => IterableOnce[A]) extends SccAnalysis[A]:
    final override protected def successors(node: A) = succs(node)
    
  
  def sccsFrom[A](succs: A => IterableOnce[A], roots: IterableOnce[A]): Ls[Ls[A]] =
    object traversal extends
      SccFromSuccFun[A](succs)
      with DefaultNoopHandling[A]
      with DefaultCaching[A]
      with DefaultCollecting[A]
    
    traversal.queryAll(roots)
    traversal.collected.toList

end SccAnalysis
