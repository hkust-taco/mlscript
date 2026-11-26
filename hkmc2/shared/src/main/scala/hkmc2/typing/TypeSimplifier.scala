package hkmc2
package typing
package logicsub

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import semantics.{Elaborator, InfVarSymbol}

/** Simplifies inferred types together with the subtype obligations that give
  * their variables meaning. All rewrites operate on a snapshot. A bound in a
  * disjunction can disappear only when the remaining formula is equivalent. */
private[logicsub] object TypeSimplifier:
  /** The owner identifies bounds that instantiation copies with a quantified
    * variable. Other obligations must be replayed in the caller's context. */
  final case class Bound(c: SubOr, owner: Opt[InfVar])
  final case class Result(body: InfType, bounds: Ls[Bound])

  // False inside a disjunction. The solver diagnoses an unconditional failure.
  private val impossible = SubOr(Top, Bot)

  private def plainTag(t: ClassLikeType): Bool = t.args.isEmpty && t.refinement.isEmpty

  // These are sufficient local proofs. In particular, a variable can denote
  // bottom, so distinct heads in two tests on a variable do not prove failure.
  private def distinctTags(a: ClassLikeType, b: ClassLikeType): Bool =
    a.sym != b.sym && !a.sym.isLiteralOf(b.sym) && !b.sym.isLiteralOf(a.sym)

  private def subtype(x: Type, y: Type): Bool = x === y || x === Bot || y === Top || ((x, y) match
    case (a: ClassLikeType, b: ClassLikeType) if plainTag(b) =>
      a.sym === b.sym || a.sym.isLiteralOf(b.sym)
    case (a: ClassLikeType, Neg(b: ClassLikeType)) => distinctTags(a, b)
    case (Union(a, b), Union(c, d)) if a === d && b === c => true
    case (Inter(l, r), _) => l === y || r === y
    case (_, Union(l, r)) => x === l || x === r
    case _ => false)

  private def disjoint(x: Type, y: Type): Bool = (x, y) match
    case (a: ClassLikeType, b: ClassLikeType) => distinctTags(a, b)
    case (Neg(a), b) => subtype(b, a)
    case (a, Neg(b)) => subtype(a, b)
    case _ => false

  private def union(x: Type, y: Type): Type =
    if subtype(x, y) then y else if subtype(y, x) then x
    else (x, y) match
      case (Neg(a), b) if subtype(a, b) => Top
      case (a, Neg(b)) if subtype(b, a) => Top
      case _ => Union(x, y)

  private def inter(x: Type, y: Type): Type =
    if subtype(x, y) then x else if subtype(y, x) then y
    else if disjoint(x, y) then Bot else Inter(x, y)

  private class Rewrite(sub: collection.Map[InfVar, Type]) extends TypeMap:
    override def applyArg(pol: Bool)(a: TypeArg): TypeArg = a match
      case t: Type => apply(pol)(t)
      case Wildcard(in, out) if in eq out =>
        // Substitution is independent of polarity. Preserve the shared operand.
        val t = apply(pol)(in)
        Wildcard(t, t)
      case w: Wildcard => super.applyArg(pol)(w)
    override def apply(pol: Bool)(t: Type): Type = t.toBasic match
      case v: InfVar => sub.getOrElse(v, v)
      case Union(l, r) => union(apply(pol)(l), apply(pol)(r))
      case Inter(l, r) => inter(apply(pol)(l), apply(pol)(r))
      case Neg(n) => apply(!pol)(n) match
        case Top => Bot
        case Bot => Top
        case Neg(v) => v
        case v => Neg(v)
      case t => super.apply(pol)(t)
    def body(t: InfType): InfType = t match
      case t: Type => apply(true)(t)
      case PolyFunType(args, ret, eff) => PolyFunType(args.map(body), body(ret), apply(true)(eff))
      case p: PolyType => p // Nested quantifiers have their own scope.

  private def visitBody(t: InfType, pol: Bool, scan: TypeTraverser): Unit = t match
    case t: Type => scan(pol)(t)
    case PolyFunType(args, ret, eff) =>
      args.foreach(visitBody(_, !pol, scan))
      visitBody(ret, pol, scan)
      scan(pol)(eff)
    case _: PolyType => ()

  private def variables(f: TypeTraverser => Unit): Set[InfVar] =
    val vs = Set.newBuilder[InfVar]
    object Scan extends TypeTraverser:
      override protected def invariant(pol: Bool, t: Type): Unit = apply(pol)(t)
      override def apply(pol: Bool)(t: Type): Unit = t.toBasic match
        case v: InfVar => vs += v
        case _ => super.apply(pol)(t)
    f(Scan)
    vs.result()

  /** Simplifies A ∨ (B₁ ∧ … ∧ Bₙ). In the fallback we know A failed.
    * Only unconditional bounds from the enclosing conjunction supply facts
    * about other branches. No distribution or search is needed. */
  private def simplifyGuards(bounds: Ls[Bound]): Ls[Bound] =
    val facts = bounds.iterator.collect { case Bound(SubOr(x, y, None), _) => x -> y }.toList
    val upper = facts.groupMap(_._1)(_._2)
    val lower = facts.groupMap(_._2)(_._1)
    type Failed = Map[Type, Ls[Type]]
    def go(c: SubOr, failed: Failed, nested: Bool): Ls[SubOr] =
      val SubOr(x, y, suffix) = c
      // A top-level fact cannot justify removing itself.
      val implied = (nested || suffix.isDefined) && (
        upper.get(x).exists(_.exists(subtype(_, y))) || lower.get(y).exists(_.exists(subtype(x, _))))
      if subtype(x, y) || implied then Nil
      else
        val refuted = failed.get(x).exists(_.exists(subtype(y, _))) || ((x, y) match
          case (Top, Bot) => true
          case (a: ClassLikeType, Bot) => plainTag(a)
          case (a: ClassLikeType, b: ClassLikeType) => plainTag(a) && disjoint(a, b)
          case _ => false)
        suffix match
          case None => (if refuted then impossible else c) :: Nil
          case Some(cs) =>
            val next = failed.updated(x, y :: failed.getOrElse(x, Nil))
            val tail = cs match
              case k :: Nil => go(k, next, true)
              case ks => ks.flatMap(go(_, next, true)).distinct
            if tail.contains(impossible) then (if refuted then impossible else SubOr(x, y)) :: Nil
            else if refuted || tail.isEmpty then tail
            else SubOr(x, y, Some(tail)) :: Nil
    bounds.flatMap(b => go(b.c, Map.empty, false).map(c => b.copy(c = c))).distinct

  private def rewrite(view: Result, sub: collection.Map[InfVar, Type], removed: SubOr => Bool): Result =
    val f = Rewrite(sub)
    val bounds = view.bounds.iterator.filterNot(b => removed(b.c)).map(b => b.copy(c = f(b.c))).toList
    Result(f.body(view.body), simplifyGuards(bounds))

  /** Eliminates one polarity at a time. For a positive variable the least
    * solution is its union of lower bounds, provided every other occurrence
    * prefers a smaller type. The dual uses the intersection of upper bounds.
    * An operand inside a fallback is a use, never a defining bound. */
  private def eliminate(view: Result, eligible: Set[InfVar], positive: Bool): Result =
    val blocked = mutable.HashSet.empty[InfVar]
    val uses = mutable.HashMap.empty[InfVar, Int]
    val defs = mutable.LinkedHashMap.empty[InfVar, mutable.LinkedHashSet[Type]]
    object Scan extends TypeTraverser:
      override protected def invariant(pol: Bool, t: Type): Unit =
        blocked ++= variables(_(pol)(t))
      override def apply(pol: Bool)(t: Type): Unit = t.toBasic match
        case v: InfVar if eligible(v) =>
          if pol != positive then blocked += v
          else uses.update(v, uses.getOrElse(v, 0) + 1)
        case _ => super.apply(pol)(t)
    visitBody(view.body, true, Scan)
    def definition(c: SubOr): Opt[(InfVar, Type)] =
      val (v, t) = if positive then (c.y, c.x) else (c.x, c.y)
      v match
        case v: InfVar if c.cs.isEmpty && eligible(v) => Some(v -> t)
        case _ => None
    view.bounds.foreach: b =>
      definition(b.c) match
        case Some((v, t)) =>
          defs.getOrElseUpdate(v, mutable.LinkedHashSet.empty) += t
          Scan(positive)(t)
        case None => Scan(b.c)

    val candidates = eligible -- blocked
    val deps = candidates.iterator.map: v =>
      v -> variables(scan => defs.get(v).foreach(_.foreach(scan(positive)))).intersect(candidates)
    .toMap
    val sub = mutable.HashMap.empty[InfVar, Type]
    val f = Rewrite(sub)
    // Process dependencies first. A compound replacement may move into one
    // use. Keeping a variable at a fan-out prevents a shared DAG expanding
    // exponentially in the printed type or a stored scheme.
    SccAnalysis.sccsFrom(deps, candidates).foreach:
      case v :: Nil if !deps(v)(v) =>
        val ts = defs.get(v).iterator.flatMap(_.iterator).map(f(positive))
        val replacement = if positive then ts.foldLeft[Type](Bot)(union) else ts.foldLeft[Type](Top)(inter)
        val atomic = replacement match
          case _: InfVar | Bot | Top => true
          case t: ClassLikeType => plainTag(t)
          case _ => false
        if atomic || uses.getOrElse(v, 0) <= 1 then sub += v -> replacement
      case _ => () // A structural recursive bound has no finite unfolding here.
    if sub.isEmpty then view
    else rewrite(view, sub, c => definition(c).exists(p => sub.contains(p._1)))

  private def simplify(raw: Result, eligible: Set[InfVar]): Result =
    val clean = rewrite(raw, Map.empty, _ => false)
    // Mutual unconditional subtype edges prove equality, even for variables
    // that occur in both polarities. A guarded edge gives no such equality.
    val edges = clean.bounds.iterator.collect:
      case Bound(SubOr(a: InfVar, b: InfVar, None), _) if eligible(a) && eligible(b) && a.lvl === b.lvl => a -> b
    .toList.groupMap(_._1)(_._2)
    val aliases = SccAnalysis.sccsFrom((v: InfVar) => edges.getOrElse(v, Nil), edges.keys)
      .iterator.flatMap: group =>
        val repr = group.minBy(_.sym.uid)
        group.iterator.filterNot(_ === repr).map(_ -> repr)
    .toMap
    val merged = if aliases.isEmpty then clean else rewrite(clean, aliases, _ => false)
    val local = eligible -- aliases.keys
    val lower = eliminate(merged, local, true)
    val result = eliminate(lower, local.intersect(live(lower)), false)
    // Error recovery can retain both 1 <: v and v <: Str after reporting the
    // failed check. Keep the conflicting bounds as evidence for that error.
    if result.bounds.exists(_.c === impossible) then raw else result

  private def live(view: Result): Set[InfVar] = variables: scan =>
    visitBody(view.body, true, scan)
    view.bounds.foreach(b => scan(b.c))

  private def bind(p: PolyType, view: Result, used: Set[InfVar]): InfType =
    val tvs = p.tvs.filter(used)
    val outer = p.outer.filter(used)
    if tvs.isEmpty && outer.isEmpty then view.body
    else PolyType(tvs, outer, Nil, view.body)

  /** Collects the bounds of an inferred type without changing the live
    * constraint graph. The raw view also serves debug printing. */
  def snapshot(t: InfType)(using InfCtx): Result =
    val bounds = mutable.LinkedHashSet.empty[SubOr]
    object Collect extends BoundTraverser:
      override def visitBound(c: SubOr): Unit = if bounds.add(c) then super.visitBound(c)
    Collect.visitType(t)
    Result(t, bounds.iterator.map(Bound(_, None)).toList)

  /** Simplifies the outermost inferred type for display and retains any
    * variables that a nested quantifier can observe. */
  def forDisplay(raw: Result)(using InfCtx): (InfType, DisplayBounds) =
    val (body, quantified, outerBinder) = raw.body match
      case p: PolyType => (p.body, Some(p.tvs.toSet), p.outer)
      case t => (t, None, None)
    val view = raw.copy(body = body)
    // A nested scheme may capture variables from this type at either polarity.
    // Keep its whole reachable graph opaque to elimination in this scope.
    val protectedVars = mutable.HashSet.empty[InfVar]
    val innerBounds = mutable.HashSet.empty[SubOr]
    object Protect extends BoundTraverser:
      override def visitBound(c: SubOr): Unit = if innerBounds.add(c) then super.visitBound(c)
      override def visitVariable(v: InfVar): Unit =
        protectedVars += v
        super.visitVariable(v)
    def nested(t: InfType): Unit = t match
      case p: PolyType => Protect.visitType(p)
      case PolyFunType(args, ret, _) =>
        args.foreach(nested)
        nested(ret)
      case _: Type => ()
    nested(body)
    val eligible = quantified.getOrElse(live(view)).filterNot(v => v.isSkolem || protectedVars(v))
    // A nested forall's bounds cannot justify erasing guards outside its binder.
    val (inner, outer) = raw.bounds.partition(b => innerBounds(b.c))
    val scoped = simplify(view.copy(bounds = outer), eligible)
    val result = scoped.copy(bounds = scoped.bounds ::: inner)
    val visible = variables(visitBody(result.body, true, _))
    val bounds = DisplayBounds.project(result.bounds.iterator.map(_.c), eligible -- visible -- outerBinder)
    val displayed = raw.body match
      case p: PolyType => bind(p, result, (live(result) ++ protectedVars) -- bounds.joins.keys)
      case _ => result.body
    displayed -> bounds

  /** Builds a private template for an inferred function. Only its quantified
    * flexible variables are candidates for elimination. Captured variables
    * continue to denote the enclosing bindings at their original levels. */
  def scheme(body: Type, tvs: Ls[InfVar], outer: Opt[InfVar], extruded: Ls[SubOr])
      (using ctx: InfCtx, state: Elaborator.State): PolyType =
    require(tvs.forall(!_.isSkolem))
    val bounds = tvs.flatMap: v =>
      ctx.varSt.get(v.sym).toList.flatMap: st =>
        st.lowerBounds.map(t => Bound(SubOr(t, v), Some(v))) :::
          st.upperBounds.map((t, cs) => Bound(SubOr(v, t, cs), Some(v)))
    val raw = Result(body, bounds ::: extruded.map(Bound(_, None)))
    val view = simplify(raw, tvs.toSet)
    val used = live(view)
    val vars = tvs.filter(used)
    val fresh = vars.iterator.map(v => v -> InfVar(v.lvl, InfVarSymbol(v.sym.origin, v.sym.hint), v.isSkolem)).toMap
    val rename = Rewrite(fresh)
    val extra = List.newBuilder[SubOr]
    // A rewrite can remove the endpoint that originally owned a bound.
    // Replay such obligations on instantiation, like the extruded constraints.
    view.bounds.reverseIterator.foreach: b =>
      val c = rename(b.c)
      b.owner.flatMap(fresh.get) match
        case Some(v) if c.x === v =>
          val st = ctx.varSt.getOrElseUpdate(v.sym, new InfVarState)
          st.upperBounds = (c.y -> c.cs) :: st.upperBounds
        case Some(v) if c.y === v && c.cs.isEmpty =>
          val st = ctx.varSt.getOrElseUpdate(v.sym, new InfVarState)
          st.lowerBounds = c.x :: st.lowerBounds
        case _ => extra += c
    PolyType(vars.map(fresh), outer.filter(used), extra.result().reverse, rename.body(view.body))
