package hkmc2.utils

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap


object algorithms:
  final class CyclicGraphError(message: String) extends Exception(message)

  /**
    * Sort a graph topologically.
    *
    * @param edges edges (target, source) in the directed acyclic graph
    * @param nodes provide if you want to include some isolated nodes in the result
    * @return
    */
  def topologicalSort[A: Ordering](edges: Iterable[(A, A)], nodes: Iterable[A] = Nil): Iterable[A] =
    @tailrec
    def sort(toPreds: SortedMap[A, Set[A]], done: Iterable[A]): Iterable[A] =
      val (noPreds, hasPreds) = toPreds.partition { _._2.isEmpty }
      if noPreds.isEmpty then
        if hasPreds.isEmpty then done else throw new CyclicGraphError(hasPreds.toString)
      else
        val found = noPreds.map { _._1 }
        sort(SortedMap.from(hasPreds.view.mapValues(_ -- found)), done ++ found)
    val toPred = edges.foldLeft(SortedMap.from(nodes.map { _ -> Set.empty[A] })) { (acc, e) => 
      acc + (e._1 -> (acc.getOrElse(e._1, Set()) + e._2)) + (e._2 -> acc.getOrElse(e._2, Set()))
    }
    sort(toPred, Seq())

  /**
    * Partitions a graph into its strongly connected components. The input type must be able to
    * be hashed efficiently as it will be used as a key.
    *
    * @param edges The edges of the graph.
    * @param nodes Any additional nodes that are not necessarily in the edges list. (Overlap is fine)
    * @return A list of strongly connected components of the graph.
    */
  def partitionScc[A](edges: Iterable[(A, A)], nodes: Iterable[A]): List[List[A]] =
    val neighbours = edges.groupMap(_._1)(_._2)
    // pre-process: collect the nodes, endpoints of `edges` first, in encounter order
    val nodesUniq =
      val seen = collection.mutable.LinkedHashSet.empty[A]
      for (a, b) <- edges do { seen.add(a); seen.add(b) }
      for n <- nodes do seen.add(n)
      seen
    // `sccsFrom` yields successors first; reverse for topological order w.r.t. edge direction
    SccAnalysis.sccsFrom(a => neighbours.getOrElse(a, Nil), nodesUniq).reverse


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
  def sccsWithInfo[A](edges: Iterable[(A, A)], nodes: Iterable[A]): SccsInfo[A] =
    val sccs = partitionScc(edges, nodes)
    val withIdx = sccs.zipWithIndex.map(_.swap).toMap
    val lookup = (
      for
        (id, scc) <- withIdx
        node <- scc
      yield node -> id
    ).toMap

    val notInSccEdges = edges.map {
      case (a, b) => (lookup(a), lookup(b))
    }.filter:
      case (a, b) => a != b

    val outs = notInSccEdges.groupBy:
      case (a, b) => a

    val sccEdges = withIdx.map {
      case (a, _) => a -> Nil // add default case
    } ++ outs.map {
      case (a, edges) => a -> edges.map(_._2)
    }.toMap
    
    val inDegs = notInSccEdges.groupBy {
      case (a, b) => b
    }.map:
      case (b, edges) => b -> edges.size

    val outDegs = outs.map:
      case (a, edges) => a -> edges.size

    SccsInfo(withIdx, sccEdges, inDegs, outDegs)
