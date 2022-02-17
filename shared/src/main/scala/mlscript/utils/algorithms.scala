package mlscript.utils

import scala.annotation.tailrec
import scala.collection.immutable.SortedMap

object algorithms {
  final class CyclicGraphError(message: String) extends Exception(message)

  def topologicalSort[A: Ordering](relations: List[(A, A)]): Iterable[A] = {
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
    val toPred = relations.foldLeft(SortedMap[A, Set[A]]()) { (acc, e) => 
      acc + (e._1 -> acc.getOrElse(e._1, Set())) + (e._2 -> (acc.getOrElse(e._2, Set()) + e._1))
    }
    sort(toPred, Seq())
  }
}