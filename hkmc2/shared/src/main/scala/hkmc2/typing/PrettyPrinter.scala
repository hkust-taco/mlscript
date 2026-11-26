package hkmc2
package typing
package logicsub
import hkmc2.utils.*, shorthands.*

class PrettyPrinter(output: String => Unit)(using printScope: Scope, ctx: InfCtx):
  def print(ty: InfType)(using Raise): Unit =
    render("Type", TypeSimplifier.forDisplay(TypeSimplifier.snapshot(ty)))

  def printRaw(ty: InfType)(using Raise): Unit = render("Raw type", TypeSimplifier.snapshot(ty))

  private def render(label: String, view: TypeSimplifier.Result)(using Raise): Unit =
    given names: Scope = printScope.nest
    object Names extends BoundTraverser:
      override def visitVariable(v: InfVar): Unit =
        // The body and its Where clause must use the same names across binders.
        names.allocateOrGetName(v.sym, v.sym.hint)
    Names.visitType(view.body)
    view.bounds.foreach(b => Names.visitBound(b.c))
    view.body.show match
      case "()" =>
      case tyStr => output(s"$label: $tyStr")
    if view.bounds.nonEmpty then
      output("Where:")
      view.bounds.foreach(b => output(s"  ${PrettyPrinter.showConstraint(b.c)}"))

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope, InfCtx): PrettyPrinter = new PrettyPrinter(output)
  private def showConstraint(k: SubOr)(using Scope, InfCtx, Raise): String =
    val p = s"${k.x.show} <: ${k.y.show}"
    k.cs match
      case N => p
      case S(cs) =>
        val ds = cs.map(showConstraint).mkString(" ∧ ")
        s"$p ∨ ($ds)"

