package hkmc2
package bbml
import scala.collection.mutable.{Set => MutSet, ListBuffer}
import utils.Scope

class PrettyPrinter(output: String => Unit)(using Scope):
  def showDisjSub(ds: DisjSub): String = ds match
    case DisjSub(d, dss, cs) =>
      val g = d.iterator.map { case (x, y) => s"${x.show}#${y.show} ∨ " }.mkString
      val h = dss.iterator.map("(" + showDisjSub(_) + ")").mkString(" ∧ ")
      val b = cs.map { case (x, y) => s" ∧ ${x.simp.show}<:${y.simp.show}"}.mkString
      s"  $g$h$b"
  def print(ty: GeneralType): Unit =
    output(s"Type: ${ty.show}")
    val bounds = PrettyPrinter.collectBounds(ty).distinct
    if !bounds.isEmpty then
      output("Where:")
      bounds.foreach {
        case (lhs, rhs) => output(s"  ${lhs.show} <: ${rhs.show}")
        case ds: DisjSub => output(showDisjSub(ds))
      }

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope): PrettyPrinter = new PrettyPrinter(output)

  type Bound = (Type, Type) // * Type <: Type

  private def collectBounds(ty: GeneralType): List[Bound | DisjSub] =
    val res = ListBuffer[Bound | DisjSub]()
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
            res ++= state.disjsub
            val (p, n) = state.disjsub.map(_.children()).unzip
            p.flatten.foreach(apply(true))
            n.flatten.foreach(apply(false))
            super.apply(pol)(ty)
        case _ => super.apply(pol)(ty)
    CollectBounds(true)(ty)
    res.toList
