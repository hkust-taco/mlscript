package hkmc2
package bbml
import scala.collection.mutable.{Set => MutSet, ListBuffer}

class PrettyPrinter(output: String => Unit):
  def print(ty: GeneralType): Unit =
    output(s"Type: ${ty}")
    val bounds = PrettyPrinter.collectBounds(ty).distinct
    if !bounds.isEmpty then
      output("Where:")
      bounds.foreach {
        case (lhs, rhs) => output(s"  $lhs <: $rhs")
      }

object PrettyPrinter:
  def apply(output: String => Unit): PrettyPrinter = new PrettyPrinter(output)

  type Bound = (Type, Type) // * Type <: Type

  private def collectBounds(ty: GeneralType): List[Bound] =
    val res = ListBuffer[Bound]()
    val cache = MutSet[Uid[InfVar]]()
    object CollectBounds extends TypeTraverser:
      override def apply(pol: Boolean)(ty: GeneralType): Unit = ty match
        case v @ InfVar(_, uid, state, _) =>
          if cache.add(uid) then
            res ++= state.lowerBounds.map(bd => (bd, v))
            res ++= state.upperBounds.map(bd => (v, bd))
            super.apply(pol)(ty)
        case _ => super.apply(pol)(ty)
    CollectBounds(true)(ty)
    res.toList
