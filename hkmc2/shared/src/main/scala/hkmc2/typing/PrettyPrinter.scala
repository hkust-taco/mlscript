package hkmc2
package typing
package logicsub
import scala.collection.mutable
import hkmc2.utils.*, shorthands.*

class PrettyPrinter(output: String => Unit)(using printScope: Scope, ctx: InfCtx):
  def print(ty: InfType)(using Raise): Unit =
    val view = TypeSimplifier.forDisplay(TypeSimplifier.snapshot(ty))
    render("Type", view.body, PrettyPrinter.factor(view.bounds.iterator.map(_.c)), implications = true)

  def printRaw(ty: InfType)(using Raise): Unit =
    val view = TypeSimplifier.snapshot(ty)
    render("Raw type", view.body, view.bounds.map(_.c), implications = false)

  private def render(label: String, body: InfType, bounds: Ls[SubOr], implications: Bool)(using Raise): Unit =
    given names: Scope = printScope.nest
    object Names extends BoundTraverser:
      override def visitVariable(v: InfVar): Unit =
        // The body and its Where clause must use the same names across binders.
        names.allocateOrGetName(v.sym, v.sym.hint)
    Names.visitType(body)
    bounds.foreach(Names.visitBound)
    body.show match
      case "()" =>
      case tyStr => output(s"$label: $tyStr")
    if bounds.nonEmpty then
      output("Where:")
      renderBounds(bounds, 2, implications)

  /** Each line at the same indentation is a conjunct. A disjunction can
    * continue on one line until its fallback has several conjuncts. */
  private def renderBounds(bounds: Ls[SubOr], indent: Int, implications: Bool)(using Scope, Raise): Unit =
    bounds.foreach: bound =>
      val premises = new StringBuilder
      val alternatives = new StringBuilder
      def alternative(text: Str): Unit =
        if alternatives.nonEmpty then alternatives ++= " ∨ "
        alternatives ++= text
      def emit(branching: Bool): Unit =
        val line = new StringBuilder(" " * indent)
        if premises.nonEmpty then
          line ++= premises
          line ++= " =>"
          if alternatives.nonEmpty then line += ' '
        line ++= alternatives
        if branching && alternatives.nonEmpty then line ++= " ∨"
        output(line.result())
      @scala.annotation.tailrec
      def disjunction(c: SubOr): Unit =
        // On a single disjunctive path, A ∨ (¬P ∨ B) is P => A ∨ B.
        // Stop collecting premises at a conjunction so that each guard
        // keeps its scope over exactly the alternatives in this branch.
        c.y.toBasic match
          case Neg(t) if implications && c.cs.isDefined =>
            if premises.nonEmpty then premises ++= " => "
            premises ++= s"${c.x.show} >:< ${t.show}"
          case _ => alternative(s"${c.x.show} <: ${c.y.show}")
        c.cs match
          case None => emit(branching = false)
          case Some(Nil) =>
            alternative("⊤")
            emit(branching = false)
          case Some(next :: Nil) => disjunction(next)
          case Some(cs) =>
            emit(branching = true)
            renderBounds(cs, indent + 4, implications)
      disjunction(bound)

object PrettyPrinter:
  def apply(output: String => Unit)(using Scope, InfCtx): PrettyPrinter = new PrettyPrinter(output)

  /** Moves exclusions from a lower intersection to the upper union, using
    * A & ¬B <: C iff A <: C | B. Only top-level conjuncts can move. */
  private[logicsub] def displayBound(x: Type, y: Type): (Type, Type) = x.toBasic match
    case _: Inter =>
      val positive = mutable.ListBuffer.empty[Type]
      val excluded = mutable.ListBuffer.empty[Type]
      def collect(t: Type): Unit = t.toBasic match
        case Inter(l, r) =>
          collect(l)
          collect(r)
        case Neg(n) => excluded += n
        case _ => positive += t
      collect(x)
      if excluded.isEmpty || positive.isEmpty then x -> y
      else
        val upper = mutable.LinkedHashSet.empty[Type]
        def include(t: Type): Unit = t.toBasic match
          case Union(l, r) =>
            include(l)
            include(r)
          case Bot => ()
          case atom => upper += atom
        include(y)
        excluded.foreach(include)
        val rhs = if upper.contains(Top) then Top else upper.iterator.reduceOption[Type](Union.apply).getOrElse(Bot)
        positive.iterator.reduceLeft(Inter.apply) -> rhs
    case _ => x -> y

  /** Factors equal heads within each conjunction, in first-occurrence order.
    * P ∨ B and P ∨ C share the fallback B ∧ C. A bare P absorbs both. */
  private def factor(bounds: IterableOnce[SubOr]): Ls[SubOr] =
    val groups = mutable.LinkedHashMap.empty[(Type, Type), Opt[mutable.ListBuffer[SubOr]]]
    bounds.iterator.foreach: c =>
      val head = displayBound(c.x, c.y)
      c.cs match
        case None => groups.update(head, None)
        case Some(cs) => groups.getOrElseUpdate(head, Some(mutable.ListBuffer.empty)).foreach(_ ++= cs)
    groups.iterator.map { case ((x, y), cs) => SubOr(x, y, cs.map(factor)) }.toList

