package hkmc2
package typing
package logicsub

import scala.collection.mutable
import syntax.*
import semantics.*
import Message.MessageContext
import hkmc2.utils.*, shorthands.*
import utils.*
import utils.Scope

type Cache = mutable.HashSet[(Type, Type)]
type ExtrudeCache = mutable.HashMap[(InfVarSymbol, Bool), InfVar]

case class CCtx(cache: Cache, parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])(using Scope):
  def err(using raise: Raise, ctx: InfCtx, tl: TL) =
    ctx.err(ErrorReport(
        msg"Type error in ${origin.describe}${exp match
            case S(ty) => msg" with expected type ${ty.show}"
            case N => msg""
          }" -> origin.toLoc
        :: parents.reverse.map(p =>
          msg"because: cannot constrain  ${p._1.show}  <:  ${p._2.show}" -> N
        )
      ))(using this)
  def nest(sub: (Type, Type)): CCtx =
    copy(cache = cache += sub, parents = parents match
      case `sub` :: _ => parents
      case _ =>  sub :: parents
    )
object CCtx:
  inline def init(origin: Term, exp: Opt[InfType])(using Scope) =
    CCtx(mutable.HashSet.empty, Nil, origin, exp)

object ConstraintSolver:
  private def log(msg: => Any, noIndent: Bool = false)(using tl: TL) = tl.log(msg, noIndent)

  private def constrainConj(conj: Conj)(using ctx: InfCtx, cctx:CCtx, tl: TL, raise: Raise): Unit =
  tl.trace(s"Constraining ${conj.showDbg}"):
    conj match
      case Conj(i, u, S(v), w, xs, ys) =>
        val rest = Conj(i, u, N, w, xs, ys)
        val bd = if v.lvl >= rest.lvl then rest else ??? // extrude(rest)(using v.lvl, true, mutable.HashMap.empty)
        val nc = (~bd).toDnf // always cache the normal form to avoid unexpected cache misses
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
        else ctx.constrain(d.tail.foldLeft(ctx.sub(d.head, Bot))((k, t) => ctx.subor(k, ctx.sub(t, Bot))))
      case Conj(NF.Inter(x :: Nil), NF.Union(y :: Nil), N,N,_,_) =>
        val da = x.args.iterator.zip(x.congr).collect:
          case (t, true) => t.posPart
        val d = (x.refinement.values ++ da).toList
        val xrm = x.refinement.toMap
        val yrm = y.refinement.toMap
        val sp = ctx.asSubcls(x,y.sym)
        if sp.isEmpty || !yrm.keySet.subsetOf(xrm.keySet) then
          if d.isEmpty then cctx.err
          else ctx.constrain(d.map(ctx.sub(_, Bot)).reduce(ctx.subor))
        else
          val x = sp.get
          val u = x.args.zip(y.args).flatMap(ctx.subArg)
          val w = y.refinement.map:
            case (a,b) => ctx.sub(xrm(a), b)
          val ds = x.refinement.filterNot(f => yrm.contains(f._1)).map:
            case (_,t) => ctx.sub(t,Bot)
          (u++w).foreach: k =>
            ctx.constrain((ds ++ Ls(k)).reduce(ctx.subor))
      case Conj(NF.Inter(xs @ (x :: _)), NF.Union(y :: Nil), N,N,_,_) =>
        if x.sym === y.sym then
          val k = x.ov.get
          val u = xs.map(_.args(k).negPart.discriminator)
          val w = u.reduce[Type](_|_)
          val in = y.args(k)
          ctx.constrain(ctx.sub(in.negPart, w))
          u.lazyZip(xs).foreach: (p, c) =>
            val d = ctx.sub(in.negPart, ~p)
            val r = y.copy(args = y.args.updated(k, Wildcard(p & in.negPart, in.posPart)))
            val s = ctx.sub(c, r)
            ctx.constrain(ctx.subor(d, s))
        else cctx.err
      case Conj(k @ NF.Inter(x :: _), NF.Union(ys @ (_ :: _)), N,N,ws,zs) =>
        def h(y: ClassLikeType) =
          def f(u: Ls[TypeArg], w: Ls[TypeArg], s: Ls[TypeArg], p:Ls[Bool])
              : Ls[ClassLikeType] = (w,p) match
            case (Nil, _) => Nil
            case (t::ws, true::ps) =>
              val a = u ++ (Wildcard.out(~t.posPart)::s)
              y.copy(args = a) :: f(s.head::u, ws, s.tail, ps)
            case (t::ws, false::ps) => f(s.head::u, ws, s.tail, ps)
            case _ => ???
          def g(u: Ls[(Tree.Ident, Type)]) =
            val w = y.args.map(_ => Wildcard.empty)
            y.refinement.map((a,t) => y.copy(args = w, refinement = (a,~t)::Nil))
          f(Nil, y.args, y.args.map(_ => Wildcard.empty), y.congr) ++ g(y.refinement)
        val (ps,t) = ys.partition(_.partialpattern)
        val xrs = x.refinement.keys.toSet
        val qs = ps.filter(p => ctx.asSubcls(x,p.sym).isDefined && p.refinement.keys.forall(xrs.contains))
        val ks = qs.foldLeft(Ls(k)): (ks, y) =>
          ks.flatMap(k => h(y).map(c => k.merge(NF.Inter(Ls(c))).get))
        ks.foreach(k => constrainConj(Conj(k, NF.Union(t),N,N,ws,zs)))
      case _ =>
        raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} ∧ ¬⊥" -> N :: Nil))
        cctx.err

  private def constrainArgs(lhs: TypeArg, rhs: TypeArg)(using ctx: InfCtx, cctx: CCtx, tl: TL, raise: Raise): Unit =
    ctx.constrain(ctx.sub(rhs.negPart, lhs.negPart))
    ctx.constrain(ctx.sub(lhs.posPart, rhs.posPart))

  private class SkolemBoundsInliner(using ctx: InfCtx) extends TypeMap:
    val cache: mutable.HashSet[InfVarSymbol] = mutable.HashSet.empty
    override def apply(pol: Bool)(t: Type) = t.toBasic match
      case v @ InfVar(_, s, true) if !cache(s) =>
        cache += s
        apply(pol)(if pol
          then ctx.ubs(s).foldLeft[Type](v)(_ & _)
          else ctx.lbs(s).foldLeft[Type](v)(_ | _))
      case _: ClassLikeType | _: InfVar => t
      case t => super.apply(pol)(t)
  private def inlineSkolemBounds(ty: Type)(using InfCtx): Type =
    (new SkolemBoundsInliner)(true)(ty)

  private def constrainImpl(lhs: Type, rhs: Type)(using ctx: InfCtx, cctx: CCtx, tl: TL, raise: Raise): Unit =
    val p = lhs.toDnf -> rhs.toDnf
    if cctx.cache(p) then log(s"Cached!")
    else tl.trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
      cctx.nest(p) givenIn:
        val disj = inlineSkolemBounds(lhs & ~rhs).toDnf
        disj.cs.foreach(constrainConj(_))

  def constrain(lhs: Type, rhs: Type)(using ctx: InfCtx, cctx: CCtx, tl: TL, raise: Raise): Unit =
    val (ps, ts) = rhs.disjuncts.toList.partition(_.partialpattern)
    if ts.length > 1 then
      val p = lhs.toDnf -> rhs
      if cctx.cache(p) then log(s"Cached!")
      else tl.trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
        cctx.nest(p) givenIn:
          val u = ps.foldLeft(lhs)((x, y) => x & ~y)
          val qs = ts.map(_.discriminator)
          constrainImpl(u, qs.reduce(_ | _))
          qs.zip(ts).foreach((q, y) => constrainImpl(q & u, y))
    else
      constrainImpl(lhs, rhs)
