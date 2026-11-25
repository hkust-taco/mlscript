package hkmc2
package typing
package logicsub
import scala.collection.mutable.{Set => MutSet, ListBuffer}
import semantics.*
import hkmc2.utils.*, shorthands.*

class PrettyPrinter(output: String => Unit)(using Scope, InfCtx):
  def print(ty: InfType)(using Raise): Unit =
    ty.show match
      case "()" =>
      case tyStr => output(s"Type: ${tyStr}")
    val cs = PrettyPrinter.collectConstraints(ty).distinct
    if cs.nonEmpty then
      output("Where:")
      cs.foreach(k => output(s"  ${PrettyPrinter.showConstraint(k)}"))

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope, InfCtx): PrettyPrinter = new PrettyPrinter(output)
  private def showConstraint(k: SubOr)(using Scope, InfCtx, Raise): String =
    val p = s"${k.x.show} <: ${k.y.show}"
    k.cs match
      case N => p
      case S(cs) =>
        val ds = cs.map(showConstraint).mkString(" ∧ ")
        s"$p ∨ ($ds)"
  private def collectConstraints(ty: InfType)
      (using infCtx: InfCtx, scope: Scope, raise: Raise)
      (using cache: MutSet[InfVarSymbol] = MutSet.empty)
      : List[SubOr] =
    val res = ListBuffer[SubOr]()
    object CollectConstraints extends TypeTraverser:
      override def apply(pol: Boolean)(t: Type): Unit =
        t.toBasic match
          case v @ InfVar(_, sym, _) =>
            if cache.add(sym) then
              val varSt = infCtx.varSt.get(sym)
              varSt.foreach: st =>
                st.lowerBounds.foreach(lb => res += SubOr(lb, v))
                st.upperBounds.foreach:
                  case (ub, cs) => res += SubOr(v, ub, cs)
          case _ => super.apply(pol)(t)
    ty match
      case t: Type => CollectConstraints(true)(t)
      case PolyFunType(args, ret, eff) => (args ++ List(ret, eff)).flatMap(collectConstraints)
      case PolyType(_, _, _, t) => collectConstraints(t)
    res.toList

