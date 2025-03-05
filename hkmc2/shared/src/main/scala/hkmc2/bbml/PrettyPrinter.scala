package hkmc2
package bbml
import scala.collection.mutable.{Set => MutSet, ListBuffer}
import utils.Scope

class PrettyPrinter(output: String => Unit)(using Scope):
  def print(ty: GeneralType): Unit =
    output(s"Type: ${ty.show}")
    val bounds = PrettyPrinter.collectBounds(ty).distinct
    if !bounds.isEmpty then
      output("Where:")
      bounds.foreach {
        case (lhs, rhs) => output(s"  ${lhs.show} <: ${rhs.show}")
        case ((x, y), z, w) =>
          val g = s"${x.show}#${y.show} ∨ "
          val h = z.iterator.map { case (x, y) => s"${x.show}#${y.show} ∨ "}.mkString
          val b = w.iterator.map { case (x, y) => s"${x.show}<:${y.show}"}.mkString(" ∧ ")
          output(s"  $g$h$b}")
      }

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope): PrettyPrinter = new PrettyPrinter(output)

  type Bound = (Type, Type) // * Type <: Type
  type DisjBound=(Bound,List[Bound],List[Bound])

  private def collectBounds(ty: GeneralType): List[Bound|DisjBound] =
    val res = ListBuffer[Bound|DisjBound]()
    val cache = MutSet[Uid[InfVar]]()
    object CollectBounds extends TypeTraverser:
      override def apply(pol: Boolean)(ty: GeneralType): Unit = ty match
        case v @ InfVar(_, uid, state, _) =>
          if cache.add(uid) then
            res ++= state.lowerBounds.map: bd =>
              apply(true)(bd)
              (bd, v)
            res ++= state.upperBounds.map: bd =>
              apply(false)(bd)
              (v, bd)
            res ++= state.disjsub.map: d =>
              val ds = d.disjoint.iterator
              val k = ds.next()
              (k, ds.toList, d.cs.toList)
            super.apply(pol)(ty)
        case _ => super.apply(pol)(ty)
    CollectBounds(true)(ty)
    res.toList
