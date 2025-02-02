package mlscript.utils

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap
import scala.collection.mutable.ArrayBuffer


object algorithms {
  final class CyclicGraphError(message: String) extends Exception(message)

  /**
    * Sort a graph topologically.
    *
    * @param edges edges (target, source) in the directed acyclic graph
    * @param nodes provide if you want to include some isolated nodes in the result
    * @return
    */
  def topologicalSort[A: Ordering](edges: Iterable[(A, A)], nodes: Iterable[A] = Nil): Iterable[A] = {
    @tailrec
    def sort(toPreds: SortedMap[A, Set[A]], done: Iterable[A]): Iterable[A] = {
      val (noPreds, hasPreds) = toPreds.partition { _._2.isEmpty }
      if (noPreds.isEmpty) {
        if (hasPreds.isEmpty) done else throw new CyclicGraphError(hasPreds.toString)
      } else {
        val found = noPreds.map { _._1 }
        sort(SortedMap.from(hasPreds.view.mapValues(_ -- found)), done ++ found)
      }
    }
    val toPred = edges.foldLeft(SortedMap.from(nodes.map { _ -> Set.empty[A] })) { (acc, e) => 
      acc + (e._1 -> (acc.getOrElse(e._1, Set()) + e._2)) + (e._2 -> acc.getOrElse(e._2, Set()))
    }
    sort(toPred, Seq())
  }

  private case class SccNode[A](
    val node: A,
    val num: Int, 
    var lowlink: Int = -1,
    var visited: Boolean = false,
    var processed: Boolean = false
  ) 

  /**
    * Partitions a graph into its strongly connected components. The input type must be able to
    * be hashed efficiently as it will be used as a key.
    *
    * @param edges The edges of the graph.
    * @param nodes Any additional nodes that are not necessarily in the edges list.
    * @return A list of strongly connected components of the graph.
    */
  def partitionScc[A](edges: Iterable[(A, A)], nodes: Iterable[A]): List[List[A]] = {
    // pre-process: assign each node an id
    val edgesSet = edges.toSet
    val nodesUniq = (edgesSet.flatMap { case (a, b) => Set(a, b) } ++ nodes.toSet).toList
    val nodesN = nodesUniq.zipWithIndex.map { case (node, idx) => SccNode(node, idx) }
    val nodeToIdx = nodesN.map(node => node.node -> node.num).toMap
    val nodesIdx = nodeToIdx.map { case (node, idx) => idx -> SccNode(node, idx) }

    val neighbours = edges
      .map { case (a, b) => (nodeToIdx(a), nodesIdx(nodeToIdx(b))) }
      .groupBy(_._1)
      .map { case (a, b) => a -> b.map(_._2) }
    
    var stack: List[SccNode[A]] = List.empty
    var sccs: List[List[A]] = List.empty
    var i = 0

    def dfs(node: SccNode[A]): Unit = {
      node.lowlink = node.num
      node.visited = true
      stack = node :: stack      
      i += 1
      for (n <- neighbours(node.num)) {
        if (!n.visited) {
          dfs(n)
          node.lowlink = n.lowlink.min(node.lowlink)
        } else if (!n.processed) {
          node.lowlink = n.num.min(node.lowlink)
        } 
      }
      node.processed = true
      if (node.lowlink == node.num) {
        var scc: List[A] = List.empty
        var cur = stack.head
        stack = stack.tail
        while (cur.num != node.num) {
          scc = node.node :: scc
          cur = stack.head
          stack = stack.tail
        }
        sccs = scc :: sccs
      }
    }

    for (n <- nodesN) {
      if (!n.visited) dfs(n)
    }
    sccs
  }
  
  // TODO
  def sscsWithInfo[A](edges: Iterable[(A, A)], nodes: Iterable[A]): List[List[A]] = {
    ???
  }
}
