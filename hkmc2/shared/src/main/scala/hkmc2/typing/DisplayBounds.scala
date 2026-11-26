package hkmc2
package typing
package logicsub

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*

/** Factored Where clauses with optional inline premises for single-use joins.
  * Each path to a join holds subtype tests that must all fail to reach it.
  * Any one of its paths suffices. */
private[logicsub] final case class DisplayBounds(clauses: Ls[SubOr], joins: Map[InfVar, Ls[Ls[SubOr]]]):
  def premise(c: SubOr)(using Scope, InfCtx, Raise): Opt[Str] = (c.x, c.y.toBasic) match
    case (v: InfVar, Bot) => joins.get(v).map: paths =>
      val alternatives = paths.iterator.map: path =>
        val overlaps = path.iterator.map: test =>
          val rhs = test.y.toBasic match
            case Neg(t) => t
            case Bot => Top
            case t => Neg(t)
          s"${test.x.show} >:< ${rhs.show}"
        val conjunction = overlaps.mkString(" ∧ ")
        if paths.tail.nonEmpty && path.tail.nonEmpty then s"($conjunction)" else conjunction
      if paths.tail.isEmpty then alternatives.next() else alternatives.mkString("(", " ∨ ", ")")
    case (_, Neg(t)) => Some(s"${c.x.show} >:< ${t.show}")
    case _ => None

private[logicsub] object DisplayBounds:
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
