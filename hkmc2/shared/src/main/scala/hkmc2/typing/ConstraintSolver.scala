package hkmc2
package typing
package logicsub

import scala.collection.mutable
import syntax.*
import semantics.*
import hkmc2.utils.*, shorthands.*
import utils.*
import utils.Scope

/** Subtype checks visited during one constraint, including the fallback to enforce on failure. */
type Cache = mutable.HashSet[(KCtx, (Type, Type))]
type ExtrudeCache = mutable.HashMap[(InfVarSymbol, Bool), InfVar]

case class CCtx(cache: Cache, parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])(using Scope):
  def err(using ctx: KCtx)(using TL, Raise) = 
    given CCtx = this
    ctx.err(parents, origin, exp)
  def cached(sub: (Type, Type))(using ctx: KCtx): Bool = cache.contains(ctx -> sub)
  def nest(sub: (Type, Type))(using ctx: KCtx): CCtx =
    cache += ctx -> sub
    copy(parents = parents match
      case `sub` :: _ => parents
      case _ =>  sub :: parents
    )
object CCtx:
  inline def init(origin: Term, exp: Opt[InfType])(using Scope) =
    CCtx(mutable.HashSet.empty, Nil, origin, exp)

object ConstraintSolver:
  private def log(msg: => Any, noIndent: Bool = false)(using tl: TL) = tl.log(msg, noIndent)

  private def constrainConj(conj: Conj)(using ctx: KCtx, cctx:CCtx)(using TL, Raise): Unit =
  tl.trace(s"Constraining ${conj.showDbg}"):
    conj match
      case Conj(i, u, S(v), S(w), xs, ys) if w.lvl > v.lvl =>
        val rest = Conj(i, u, S(v), N, xs, ys)
        val nc = rest.toDnf // always cache the normal form to avoid unexpected cache misses
        log(s"New bound: ${v.showDbg} >: ${nc.showDbg}")
        cctx.nest(nc -> w.toDnf) givenIn:
          ctx.addlb(nc, w)
      case Conj(i, u, S(v), w, xs, ys) =>
        val rest = Conj(i, u, N, w, xs, ys)
        val nc = (~rest).toDnf // always cache the normal form to avoid unexpected cache misses
        log(s"New bound: ${v.showDbg} <: ${nc.showDbg}")
        cctx.nest(v.toDnf -> nc) givenIn:
          ctx.addub(v, nc)
      case Conj(i, u, N, S(v), xs,ys) =>
        val rest = Conj(i, u, N,N,xs,ys)
        val c = rest.toDnf // always cache the normal form to avoid unexpected cache misses
        log(s"New bound: ${v.showDbg} :> ${c.showDbg}")
        cctx.nest(c -> v.toDnf) givenIn:
          ctx.addlb(c, v)
      case Conj(NF.Inter(x :: Nil), NF.Union(Nil), N,N,_,_) =>
        val da = x.args.iterator.zip(x.congr).collect:
          case (t, true) => t.posPart
        val d = (x.refinement.values ++ da).toList
        if d.isEmpty then cctx.err
        else ctx.constrain(d.map(SubOr(_, Bot)).reduce(_.or(_)))
      case Conj(NF.Inter(x :: Nil), NF.Union(y :: Nil), N,N,_,_) =>
        val da = x.args.iterator.zip(x.congr).collect:
          case (t, true) => t.posPart
        val d = (x.refinement.values ++ da).toList
        val xrm = x.refinement.toMap
        val yrm = y.refinement.toMap
        val sp = ctx.asSubcls(x,y.sym)
        if sp.isEmpty || !yrm.keySet.subsetOf(xrm.keySet) then
          if d.isEmpty then cctx.err
          else ctx.constrain(d.map(SubOr(_, Bot)).reduce(_.or(_)))
        else
          val x = sp.get
          val u = x.args.zip(y.args).flatMap(ctx.subArg)
          val w = y.refinement.map:
            case (a,b) => SubOr(xrm(a), b)
          val ds = x.refinement.filterNot(f => yrm.contains(f._1)).map:
            case (_,t) => SubOr(t,Bot)
          (u++w).foreach: k =>
            ctx.constrain((ds ++ Ls(k)).reduce(_.or(_)))
      case Conj(NF.Inter(xs @ (x :: _)), NF.Union(y :: Nil), N,N,_,_) =>
        if x.sym === y.sym then
          val k = x.ov.get
          val u = xs.map(_.args(k).negPart.discriminator)
          val w = u.reduce[Type](_|_)
          val in = y.args(k)
          ctx.constrain(SubOr(in.negPart, w))
          u.lazyZip(xs).foreach: (p, c) =>
            val d = SubOr(in.negPart, ~p)
            val r = y.copy(args = y.args.updated(k, Wildcard(p & in.negPart, in.posPart)))
            val s = SubOr(c, r)
            ctx.constrain(d.or(s))
        else cctx.err
      case Conj(k @ NF.Inter(x :: _), NF.Union(ys @ (_ :: _)), N,N,ws,zs) =>
        def h(y: ClassLikeType) =
          val wildcards = y.args.map(_ => Wildcard.empty)
          require(y.args.length === y.congr.length)
          val args = y.args.iterator.zip(y.congr).zipWithIndex.collect:
            case ((arg, true), i) =>
              y.copy(args = wildcards.updated(i, Wildcard.out(~arg.posPart)), refinement = Nil)
          val fields = y.refinement.iterator.map: (label, ty) =>
            y.copy(args = wildcards, refinement = (label, ~ty) :: Nil)
          (args ++ fields).toList
        // A value with this tag cannot inhabit unrelated union alternatives.
        // Keeping them can send the identical conjunction back into this rule.
        val (ps,t) = ys.filter(y => ctx.asSubcls(x, y.sym).isDefined).partition(_.partialpattern)
        val xrs = x.refinement.keys.toSet
        val qs = ps.filter: p =>
          p.refinement.keys.forall(xrs.contains)
        val ks = qs.foldLeft(Ls(k)): (ks, y) =>
          ks.flatMap(k => h(y).map(c => k.merge(NF.Inter(Ls(c))).get))
        if t.length === ys.length then cctx.err
        else ks.foreach(k => constrainConj(Conj(k, NF.Union(t),N,N,ws,zs)))
      case _ =>
        // The caller may be trying this constraint as one alternative of a guard.
        // Report the subtype error only after its fallbacks have failed.
        cctx.err

  // private class SkolemBoundsInliner(using ctx: KCtx) extends TypeMap:
  //   val cache: mutable.HashSet[InfVarSymbol] = mutable.HashSet.empty
  //   override def apply(pol: Bool)(t: Type) = t.toBasic match
  //     case v @ InfVar(_, s, true) if !cache(s) =>
  //       cache += s
  //       apply(pol)(if pol
  //         then ctx.ubs(s).foldLeft[Type](v)(_ & _)
  //         else ctx.lbs(s).foldLeft[Type](v)(_ | _))
  //     case _: ClassLikeType | _: InfVar => t
  //     case t => super.apply(pol)(t)
  private def inlineSkolemBounds(ty: Type)(using KCtx): Type = ty // TODO
  //   (new SkolemBoundsInliner)(true)(ty)

  def constrainImpl(lhs: Type, rhs: Type)
      (using ctx: KCtx, cctx:CCtx)(using TL, Raise)
      : Unit =
    val p = lhs.toDnf -> rhs.toDnf
    if cctx.cached(p) then log(s"Cached!")
    else tl.trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
      cctx.nest(p) givenIn:
        val disj = inlineSkolemBounds(lhs & ~rhs).toDnf
        disj.cs.foreach(constrainConj(_))

  def constrain(lhs: Type, rhs: Type)(using ctx: KCtx, cctx:CCtx)(using TL, Raise): Unit =
    val (ps, ts) = rhs.disjuncts.toList.partition(_.partialpattern)
    if ts.length > 1 then
      val p = lhs.toDnf -> rhs
      if cctx.cached(p) then log(s"Cached!")
      else tl.trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
        cctx.nest(p) givenIn:
          val u = ps.foldLeft(lhs)((x, y) => x & ~y)
          val qs = ts.map(_.discriminator)
          constrainImpl(u, qs.reduce(_ | _))
          qs.zip(ts).foreach((q, y) => constrainImpl(q & u, y))
    else
      constrainImpl(lhs, rhs)
