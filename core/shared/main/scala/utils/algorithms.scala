package mlscript.utils

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap


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

  /**
    * Partitions a graph into its strongly connected components. The input type must be able to
    * be hashed efficiently as it will be used as a key.
    *
    * @param edges The edges of the graph.
    * @param nodes Any additional nodes that are not necessarily in the edges list. (Overlap is fine)
    * @return A list of strongly connected components of the graph.
    */
  def partitionScc[A](edges: Iterable[(A, A)], nodes: Iterable[A]): List[List[A]] = {
    case class SccNode[A](
      val node: A,
      val id: Int,
      var num: Int = -1, 
      var lowlink: Int = -1,
      var visited: Boolean = false,
      var onStack: Boolean = false
    )

    // pre-process: assign each node an id
    val edgesSet = edges.toSet
    val nodesUniq = (edgesSet.flatMap { case (a, b) => Set(a, b) } ++ nodes.toSet).toList
    val nodesN = nodesUniq.zipWithIndex.map { case (node, idx) => SccNode(node, idx) }
    val nodeToIdx = nodesN.map(node => node.node -> node.id).toMap
    val nodesIdx = nodesN.map { case node => node.id -> node }.toMap

    val neighbours = edges
      .map { case (a, b) => (nodeToIdx(a), nodesIdx(nodeToIdx(b))) }
      .groupBy(_._1)
      .map { case (a, b) => a -> b.map(_._2) }
      .withDefault(_ => Nil)

    // Tarjan's algorithm

    var stack: List[SccNode[A]] = List.empty
    var sccs: List[List[A]] = List.empty
    var i = 0

    def dfs(node: SccNode[A], depth: Int = 0): Unit = {
      def printlnsp(s: String) = {
        println(s)
      }
      
      node.num = i
      node.lowlink = node.num
      node.visited = true
      stack = node :: stack
      i += 1
      for (n <- neighbours(node.id)) {
        if (!n.visited) {
          dfs(n, depth + 1)
          node.lowlink = n.lowlink.min(node.lowlink)
        } else if (!n.onStack) {
          node.lowlink = n.num.min(node.lowlink)
        } 
      }
      if (node.lowlink == node.num) {
        var scc: List[A] = List.empty
        var cur = stack.head
        stack = stack.tail
        cur.onStack = true
        while (cur.id != node.id) {
          scc = cur.node :: scc
          cur = stack.head
          stack = stack.tail
          cur.onStack = true
        }
        scc = cur.node :: scc
        sccs = scc :: sccs
      }
    }

    for (n <- nodesN) {
      if (!n.visited) dfs(n)
    }
    sccs
  }
  

  /**
    * Info about a graph partitioned into its strongly-connected sets. The input type must be able to
    * be hashed efficiently as it will be used as a key.
    *
    * @param sccs The strongly connected sets.
    * @param edges The edges of the strongly-connected sets. Together with `sccs`, this forms an acyclic graph.
    * @param inDegs The in-degrees of the above described graph.
    * @param outDegs The out-degrees of the above described graph.
    */
  case class SccsInfo[A](
    sccs: Map[Int, List[A]],
    edges: Map[Int, Iterable[Int]],
    inDegs: Map[Int, Int],
    outDegs: Map[Int, Int],
  )

  /**
    * Partitions a graph into its strongly connected components and returns additional information
    * about the partition. The input type must be able to be hashed efficiently as it will be used as a key.
    *
    * @param edges The edges of the graph.
    * @param nodes Any additional nodes that are not necessarily in the edges list. (Overlap is fine)
    * @return The partitioned graph and info about it.
    */
  def sccsWithInfo[A](edges: Iterable[(A, A)], nodes: Iterable[A]): SccsInfo[A] = {
    val sccs = partitionScc(edges, nodes)
    val withIdx = sccs.zipWithIndex.map(_.swap).toMap
    val lookup = (
      for {
        (id, scc) <- withIdx
        node <- scc
      } yield node -> id
    ).toMap

    val notInSccEdges = edges.map {
      case (a, b) => (lookup(a), lookup(b))
    }.filter {
      case (a, b) => a != b
    }

    val outs = notInSccEdges.groupBy {
      case (a, b) => a
    }

    val sccEdges = withIdx.map {
      case (a, _) => a -> Nil // add default case
    } ++ outs.map {
      case (a, edges) => a -> edges.map(_._2)
    }.toMap
    
    val inDegs = notInSccEdges.groupBy {
      case (a, b) => b
    }.map {
      case (b, edges) => b -> edges.size
    }

    val outDegs = outs.map {
      case (a, edges) => a -> edges.size
    }

    SccsInfo(withIdx, sccEdges, inDegs, outDegs)
  }
}
