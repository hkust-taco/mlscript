package hkmc2
package typing
package logicsub

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*

/** Factored Where clauses with optional inline premises for single-use joins.
  * Each path to a join holds subtype tests that must all fail to reach it.
  * Any one of its paths suffices. */
private[logicsub] final case class DisplayBounds(clauses: Ls[SubOr], joins: Map[InfVar, Ls[Ls[SubOr]]]):
  import DisplayBounds.Head

  /** Uses a premise when failing every test on one path gives positive
    * overlaps. Other heads express the subtype conditions for skipping the fallback. */
  def head(c: SubOr, implications: Bool)(using Scope, InfCtx, Raise): Head =
    def subtype(test: SubOr): Str = s"${test.x.show} <: ${test.y.show}"
    def overlapType(test: SubOr): Opt[Type] = test.y.toBasic match
      case Neg(t) if !t.toBasic.isInstanceOf[Neg] && t.toBasic != Top && t.toBasic != Bot => Some(t)
      case _ => None
    def overlap(test: SubOr): Opt[Str] = overlapType(test).map(t => s"${test.x.show} >:< ${t.show}")
    if !implications || c.cs.isEmpty then Head.Disjunct(subtype(c))
    else (c.x, c.y) match
      case (v: InfVar, Bot) if joins.contains(v) =>
        val paths = joins(v)
        paths match
          case path :: Nil if path.forall(overlapType(_).isDefined) =>
            Head.Premise(path.iterator.flatMap(overlap).mkString(" ∧ "))
          case _ =>
            // The join is empty when every incoming path has a successful
            // subtype test. Keep that conjunction factored over the fallback.
            val empty = paths.iterator.map: path =>
              val tests = path.iterator.map(subtype)
              if paths.tail.nonEmpty && path.tail.nonEmpty then tests.mkString("(", " ∨ ", ")")
              else tests.mkString(" ∨ ")
            Head.Disjunct(empty.mkString(" ∧ "))
      case _ => overlap(c).fold[Head](Head.Disjunct(subtype(c)))(Head.Premise.apply)

private[logicsub] object DisplayBounds:
  enum Head:
    case Premise(text: Str)
    case Disjunct(text: Str)

  /** Factors equal heads within each conjunction, in first-occurrence order.
    * P ∨ B and P ∨ C share the fallback B ∧ C. A bare P absorbs both. */
  private def factor(bounds: IterableOnce[SubOr]): Ls[SubOr] =
    val groups = mutable.LinkedHashMap.empty[(Type, Type), Opt[mutable.ListBuffer[SubOr]]]
    bounds.iterator.foreach: c =>
      val head = PrettyPrinter.displayBound(c.x, c.y)
      c.cs match
        case None => groups.update(head, None)
        case Some(cs) => groups.getOrElseUpdate(head, Some(mutable.ListBuffer.empty)).foreach(_ ++= cs)
    groups.iterator.map { case ((x, y), cs) => SubOr(x, y, cs.map(factor)) }.toList

  /** Projects a local variable out of the printed constraints if its only
    * definitions force it to Top on incoming paths and its only use tests
    * emptiness at one continuation. Outside those paths Bottom is a witness.
    * The caller excludes variables observable in the type or another scope. */
  def project(bounds: IterableOnce[SubOr], local: Set[InfVar]): DisplayBounds =
    val clauses = factor(bounds)
    if local.isEmpty then return DisplayBounds(clauses, Map.empty)
    val paths = mutable.LinkedHashMap.empty[InfVar, mutable.ListBuffer[Ls[SubOr]]]
    val used = mutable.HashSet.empty[InfVar]
    val blocked = mutable.HashSet.empty[InfVar]
    object Observe extends TypeTraverser:
      override protected def invariant(pol: Bool, t: Type): Unit = apply(pol)(t)
      override def apply(pol: Bool)(t: Type): Unit = t.toBasic match
        case v: InfVar if local(v) => blocked += v
        case _ => super.apply(pol)(t)

    clauses.foreach: root =>
      var definitions: Ls[(InfVar, Ls[SubOr])] = Nil
      def visit(c: SubOr, prefix: Ls[SubOr]): Unit =
        (c.x, c.y) match
          case (Top, v: InfVar) if local(v) && c.cs.isEmpty && prefix.nonEmpty =>
            definitions = (v -> prefix) :: definitions
          case (v: InfVar, Bot) if local(v) && c.cs.exists(_.nonEmpty) =>
            if !used.add(v) then blocked += v
          case _ =>
            Observe(true)(c.x)
            Observe(false)(c.y)
        c.cs.foreach: children =>
          val next = c :: prefix
          children.foreach(visit(_, next))
      visit(root, Nil)
      // Moving several definitions out of one factored clause could copy a
      // long shared prefix into each premise. Move at most one path per root,
      // so the total number of moved tests is bounded by the factored input.
      definitions match
        case (v, prefix) :: Nil =>
          paths.getOrElseUpdate(v, mutable.ListBuffer.empty) += prefix.reverse
          // A join tested on an incoming path must stay named in that premise.
          // This also leaves cyclic definitions intact.
          prefix.foreach:
            case SubOr(u: InfVar, Bot, _) => blocked += u
            case _ => ()
        case many => many.foreach((v, _) => blocked += v)

    val joins = paths.iterator.collect { case (v, ps) if used(v) && !blocked(v) => v -> ps.toList }.toMap
    if joins.isEmpty then DisplayBounds(clauses, joins)
    else
      def keep(c: SubOr): Opt[SubOr] = c match
        case SubOr(Top, v: InfVar, None) if joins.contains(v) => None
        case SubOr(_, _, Some(cs)) if cs.nonEmpty =>
          val rest = cs.flatMap(keep)
          // Removing every conjunct makes the fallback true.
          Option.when(rest.nonEmpty)(c.copy(cs = Some(rest)))
        case _ => Some(c)
      DisplayBounds(clauses.flatMap(keep), joins)
