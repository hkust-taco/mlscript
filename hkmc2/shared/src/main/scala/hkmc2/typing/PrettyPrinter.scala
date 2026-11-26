package hkmc2
package typing
package logicsub
import scala.collection.mutable.LinkedHashSet
import hkmc2.utils.*, shorthands.*

class PrettyPrinter(output: String => Unit)(using printScope: Scope, ctx: InfCtx):
  def print(ty: InfType)(using Raise): Unit =
    given names: Scope = printScope.nest
    val bounds = LinkedHashSet.empty[SubOr]
    object Collect extends BoundTraverser:
      override def visitVariable(v: InfVar): Unit =
        // Quantifiers print their bodies in a nested scope. Reserve each name
        // here so that it denotes the same variable in the separate Where clause.
        names.allocateOrGetName(v.sym, v.sym.hint)
        super.visitVariable(v)
      override def visitBound(c: SubOr): Unit =
        if bounds.add(c) then super.visitBound(c)
    Collect.visitType(ty)
    ty.show match
      case "()" =>
      case tyStr => output(s"Type: ${tyStr}")
    if bounds.nonEmpty then
      output("Where:")
      bounds.foreach(k => output(s"  ${PrettyPrinter.showConstraint(k)}"))

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope, InfCtx): PrettyPrinter = new PrettyPrinter(output)
  private def showConstraint(k: SubOr)(using Scope, InfCtx, Raise): String =
    val p = s"${k.x.show} <: ${k.y.show}"
    k.cs match
      case N => p
      case S(cs) =>
        val ds = cs.map(showConstraint).mkString(" ∧ ")
        s"$p ∨ ($ds)"

