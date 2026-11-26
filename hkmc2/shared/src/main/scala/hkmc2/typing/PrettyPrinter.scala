package hkmc2
package typing
package logicsub
import scala.collection.mutable
import hkmc2.utils.*, shorthands.*

class PrettyPrinter(output: String => Unit)(using printScope: Scope, ctx: InfCtx):
  def print(ty: InfType)(using Raise): Unit =
    val (body, bounds) = TypeSimplifier.forDisplay(TypeSimplifier.snapshot(ty))
    render("Type", body, bounds, implications = true)

  def printRaw(ty: InfType)(using Raise): Unit =
    val view = TypeSimplifier.snapshot(ty)
    render("Raw type", view.body, DisplayBounds(view.bounds.map(_.c), Map.empty), implications = false)

  private def render(label: String, body: InfType, bounds: DisplayBounds, implications: Bool)(using Raise): Unit =
    given names: Scope = printScope.nest
    object Names extends BoundTraverser:
      override def visitVariable(v: InfVar): Unit =
        // The body and its Where clause must use the same names across binders.
        bounds.joins.get(v) match
          case None => names.allocateOrGetName(v.sym, v.sym.hint)
          case Some(paths) => for path <- paths; test <- path do
            visitType(test.x)
            visitType(test.y)
    Names.visitType(body)
    bounds.clauses.foreach(Names.visitBound)
    body.show match
      case "()" =>
      case tyStr => output(s"$label: $tyStr")
    if bounds.clauses.nonEmpty then
      output("Where:")
      renderBounds(bounds.clauses, 2, if implications then bounds.premise else _ => None)

  /** Each line at the same indentation is a conjunct. A disjunction can
    * continue on one line until its fallback has several conjuncts. */
  private def renderBounds(bounds: Ls[SubOr], indent: Int, premise: SubOr => Opt[Str])(using Scope, Raise): Unit =
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
        val guard = if c.cs.isDefined then premise(c) else None
        guard match
          case Some(text) =>
            if premises.nonEmpty then premises ++= " ∧ "
            premises ++= text
          case None => alternative(s"${c.x.show} <: ${c.y.show}")
        c.cs match
          case None => emit(branching = false)
          case Some(Nil) =>
            alternative("⊤")
            emit(branching = false)
          case Some(next :: Nil) => disjunction(next)
          case Some(cs) =>
            emit(branching = true)
            renderBounds(cs, indent + 4, premise)
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

