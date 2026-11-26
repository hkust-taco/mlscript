package hkmc2
package typing
package logicsub

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import semantics.*, Term.SimpleRef
import utils.*

/** The joint condition on scrutinee values that reach a point in a split.
  * Conjunction keeps enclosing tests in scope. Disjunction joins failures
  * that lead to the same continuation. */
private[logicsub] enum MatchCtx:
  case Always, Never
  case Test(subject: MatchCtx.Subject, pattern: ClassLikeType, positive: Bool)
  case Both(left: MatchCtx, right: MatchCtx)
  case Either(left: MatchCtx, right: MatchCtx)

  def and(that: MatchCtx): MatchCtx = (this, that) match
    case (Never, _) | (_, Never) => Never
    case (Always, r) => r
    case (l, Always) => l
    case (l, r) if l === r => l
    case _ => Both(this, that)
  def or(that: MatchCtx): MatchCtx = (this, that) match
    case (Always, _) | (_, Always) => Always
    case (Never, r) => r
    case (l, Never) => l
    case (l, r) if l === r => l
    case _ => Either(this, that)

  lazy val tests: Vector[Test] = this match
    case t: Test => Vector.single(t)
    case Both(l, r) => l.tests ++ r.tests
    case Either(l, r) => l.tests ++ r.tests
    case Always | Never => Vector.empty

  private lazy val subjects = tests.iterator.map(_.subject).toSet

  private def decide(s: MatchCtx.Subject, accepts: ClassLikeType => Bool): MatchCtx = this match
    case Test(`s`, p, pos) => if accepts(p) === pos then Always else Never
    case Both(l, r) => l.decide(s, accepts).and(r.decide(s, accepts))
    case Either(l, r) => l.decide(s, accepts).or(r.decide(s, accepts))
    case _ => this

  /** Partitions one scrutinee's domain and leaves the condition on the others
    * attached to each part. Class and literal tests inspect nominal tags, so
    * each value has a most specific matching tag or misses every test. */
  def partition(s: MatchCtx.Subject)(using ctx: InfCtx): Ls[(Type, MatchCtx)] =
    val patterns = tests.iterator.collect { case Test(`s`, p, _) => p }.distinct.toVector
    def sub(p: ClassLikeType, q: ClassLikeType) = ctx.asSubcls(p, q.sym).isDefined
    val parts = mutable.LinkedHashMap.empty[MatchCtx, Type]
    def add(r: Type, rest: MatchCtx): Unit = if rest != Never then
      parts.update(rest, parts.getOrElse(rest, Bot) | r)
    for p <- patterns do
      val narrower = patterns.iterator.filter(q => q != p && sub(q, p)).foldLeft[Type](Bot)(_ | _)
      add(p & ~narrower, decide(s, sub(p, _)))
    add(~patterns.foldLeft[Type](Bot)(_ | _), decide(s, _ => false))
    parts.iterator.map((rest, r) => r -> rest).toList

private[logicsub] object MatchCtx:
  /** All tests on a binding use the same scrutinee and its original type. */
  final class Subject(val ref: SimpleRef, val tpe: Type)

  /** Interprets match conditions for a returning if and its nested arms. A shared reachability
    * variable receives Top when any alternative can reach a join. Guards on
    * that variable let each subsequent constraint use the whole disjunction
    * without distributing its fallback over every incoming path. */
  final class SplitTyping(using Elaborator.State, TL, Raise):
    private val subjects = mutable.HashMap.empty[Symbol, Subject]
    // A join introduced inside a polymorphic definition belongs to that
    // definition's constraint store and must be instantiated with its scheme.
    private val guards = mutable.HashMap.empty[(InfCtx, MatchCtx), Opt[Ls[SubOr]]]

    def subject(ref: SimpleRef, tpe: => Type): Subject =
      subjects.getOrElseUpdate(ref.sym, Subject(ref, tpe))

    /** Returns emptiness checks whose disjunction proves that the arm is
      * unreachable, or None when the pattern tests already rule out the arm. */
    private def guard(path: MatchCtx)(using ctx: InfCtx, cc: CCtx): Opt[Ls[SubOr]] =
      guards.getOrElseUpdate(ctx -> path, path match
        case Always => S(Nil)
        case Never => N
        case Test(s, p, pos) => S(SubOr(s.tpe, if pos then ~p else p) :: Nil)
        // Independent sets of scrutinees admit a joint assignment whenever
        // each side admits one. Shared scrutinees need a common refinement.
        case Both(l, r) if !l.subjects.exists(r.subjects) =>
          for
            a <- guard(l)
            b <- guard(r)
          yield a ::: b
        case _ =>
          val s = path.tests.head.subject
          val edges = path.partition(s).flatMap: (r, tail) =>
            guard(tail).map(rest => if r === Top then rest else SubOr(s.tpe, ~r) :: rest)
          edges match
            case Nil => N
            case edge :: Nil => S(edge)
            case alternatives =>
              val reached = InfVar(ctx.lvl, InfVarSymbol(TempSymbol(S(s.ref), N, "reach")), false)
              alternatives.foreach(edge => ctx.constrain(edge.foldRight(SubOr(Top, reached))(_.or(_))))
              S(SubOr(reached, Bot) :: Nil)
      )

    private[MatchCtx] def constrain(path: MatchCtx, c: SubOr)(using ctx: InfCtx, cc: CCtx): Unit =
      guard(path).foreach(edge => ctx.constrain(edge.foldRight(c)(_.or(_))))

    def under(path: MatchCtx, lexical: InfCtx)(using CCtx): InfCtx =
      if path === Always then lexical else
        val active = Arm(this, path, lexical.arm)(using lexical.unguarded)
        new ThenCtx(lexical.unguarded, lexical, active):
          override def get(sym: Symbol): Opt[InfType] =
            active.binding(sym).orElse(super.get(sym))

  /** The lexical refinements and guarded constraints of one arm. Nested splits
    * extend its path before computing reachability, so they can reuse facts
    * about the same runtime values even when several paths enter the arm. */
  final class Arm(val split: SplitTyping, val path: MatchCtx, outer: Opt[Arm])
      (using base: InfCtx, cc: CCtx, state: Elaborator.State, tl: TL, raise: Raise):
    private val bindings = mutable.HashMap.empty[Symbol, InfType]
    private val projections = mutable.HashMap.empty[InfVarSymbol, Subject]
    private def projection(v: InfVarSymbol): Opt[Subject] =
      projections.get(v).orElse(outer.flatMap(_.projection(v)))
    private def hasProjections: Bool = projections.nonEmpty || outer.exists(_.hasProjections)

    def binding(sym: Symbol): Opt[InfType] =
      path.tests.find(_.subject.ref.sym === sym).map: t =>
        val s = t.subject
        bindings.getOrElseUpdate(sym, path.partition(s) match
          case Nil => Bot
          case (r, _) :: Nil => s.tpe & r
          case alternatives =>
            // A lexical binding can capture the projection beyond this scope.
            // Its bounds retain the possible values after the arm has returned.
            val value = InfVar(base.lvl, InfVarSymbol(s.ref.sym), false)
            alternatives.foreach: (r, rest) =>
              val bound = SubOr(s.tpe & r, value)
              split.constrain(rest, bound)
            projections += value.sym -> s
            value
        )

    /** Enforces a bound for each feasible combination of the scrutinees it uses.
      * The remaining condition guards the bound once across incoming paths. */
    def enforce(c: SubOr, target: InfCtx)(using cc: CCtx): Unit =
      val used = mutable.LinkedHashMap.empty[Subject, Set[InfVarSymbol]]
      object Scan extends TypeTraverser:
        override def apply(pol: Bool)(t: Type): Unit = t.toBasic match
          case v: InfVar => projection(v.sym).foreach: s =>
            used.update(s, used.getOrElse(s, Set.empty) + v.sym)
          case _ => super.apply(pol)(t)
      if hasProjections then Scan(c)

      def emit(path: MatchCtx, refs: Ls[(Subject, Set[InfVarSymbol])], c: SubOr): Unit = refs match
        case Nil => split.constrain(path, c)(using target, cc)
        case (s, vars) :: vs =>
          path.partition(s).foreach: (r, rest) =>
            object Replace extends TypeMap:
              override def apply(pol: Bool)(t: Type): Type = t.toBasic match
                case i: InfVar if vars.contains(i.sym) => s.tpe & r
                case _ => super.apply(pol)(t)
            val bound = Replace(c)
            emit(rest, vs, if r === Top then bound else SubOr(s.tpe, ~r).or(bound))
      emit(path, used.toList, c)
