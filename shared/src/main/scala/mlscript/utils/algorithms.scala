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
}