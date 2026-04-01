package hkmc2
package invalml
import scala.collection.mutable.{Set => MutSet, ListBuffer}
import utils.Scope

class PrettyPrinter(output: String => Unit)(using Scope, InvalCtx):
  def print(ty: GeneralType)(using Raise): Unit =
    ty.show match
    case "()" =>
    case tyStr =>
      output(s"Type: ${tyStr}")
    val bounds = PrettyPrinter.collectBounds(ty).distinct
    if !bounds.isEmpty then
      output("Where:")
      bounds.foreach {
        case (lhs, rhs) => output(s"  ${lhs.show} <: ${rhs.show}")
      }

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope, InvalCtx): PrettyPrinter = new PrettyPrinter(output)

  type Bound = (Type, Type) // * Type <: Type

  private def collectBounds(ty: GeneralType): List[Bound] =
    val res = ListBuffer[Bound]()
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
            super.apply(pol)(ty)
        case _ => super.apply(pol)(ty)
    CollectBounds(true)(ty)
    res.toList
