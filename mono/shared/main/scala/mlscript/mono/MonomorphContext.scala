package mlscript.mono

import mlscript.mono.debug.DebugOutput
import scala.collection.immutable.SeqMap
import mlscript.mono.debug.Printable

class MonomorphContext(context: List[Map[String, DataType]]) extends Printable:
  def +(entry: (String, DataType)): MonomorphContext =
    MonomorphContext(context match {
      case Nil => Nil
      case head :: tail => (head + entry) :: tail
    })

  def :+(entry: (String, DataType)): MonomorphContext =
    MonomorphContext((Map.empty + entry) :: context)

  def unary_+(): MonomorphContext =
    MonomorphContext(Map.empty :: context)

  def get(key: String): Option[DataType] =
    context.iterator.flatMap(_.get(key)).nextOption()

  def getDebugOutput: DebugOutput =
    DebugOutput.Map(context.foldRight(SeqMap.empty[String, String]) { (entries, map) =>
      entries.foldLeft(map) { (map, entry) =>
        map + (entry._1 -> entry._2.toString)
      }
    }.toList)


object MonomorphContext:
  def empty: MonomorphContext = MonomorphContext(Nil)