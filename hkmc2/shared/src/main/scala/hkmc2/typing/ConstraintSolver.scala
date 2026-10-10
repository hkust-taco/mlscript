package hkmc2
package typing
package logicsub

import scala.collection.mutable

import semantics.*
import Message.MessageContext
import hkmc2.utils.*, shorthands.*
import utils.*
import utils.Scope

type Cache = mutable.HashSet[(Type, Type)]
type ExtrudeCache = mutable.HashMap[(InfVarSymbol, Bool), InfVar]

case class CCtx(cache: Cache, parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])(using Scope):
  def err(using Raise, InfCtx) =
    raise(ErrorReport(
      msg"Type error in ${origin.describe}${exp match
          case S(ty) => msg" with expected type ${ty.show}"
          case N => msg""
        }" -> origin.toLoc
      :: parents.reverse.map(p =>
        msg"because: cannot constrain  ${p._1.show}  <:  ${p._2.show}" -> N
      )
    ))
  def nest(sub: (Type, Type)): CCtx =
    copy(cache = cache += sub, parents = parents match
      case `sub` :: _ => parents
      case _ =>  sub :: parents
    )
object CCtx:
  inline def init(origin: Term, exp: Opt[InfType])(using Scope) =
    CCtx(mutable.HashSet.empty, Nil, origin, exp)

class ConstraintSolver(elState: Elaborator.State, tl: TraceLogger)(using Raise):
  import tl.{trace, log}

  private def constrainConj(conj: Conj)(using ctx: InfCtx, cctx:CCtx, tl: TL): Unit = trace(s"Constraining ${conj.showDbg}"):
    conj match
      case Conj(i, u, S(v), w, _, _) =>
        val rest = Conj(i, u, N, w, Nil,Nil)
        val bd = if v.lvl >= rest.lvl then rest else ??? // extrude(rest)(using v.lvl, true, mutable.HashMap.empty)
        val nc = (~bd).toDnf // always cache the normal form to avoid unexpected cache misses
        log(s"New bound: ${v.showDbg} <: ${nc.showDbg}")
        cctx.nest(v.toDnf -> nc) givenIn:
        //   v.state.upperBounds ::= nc
        //   v.state.lowerBounds.foreach(lb => constrain(lb, nc))
          ctx.addub(v, nc)
      case Conj(i, u, N, S(v), _,_) =>
        val rest = Conj(i, u, N,N,Nil,Nil)
        val bd = if v.lvl >= rest.lvl then rest else ??? // extrude(rest)(using v.lvl, true, mutable.HashMap.empty)
        val c = bd.toDnf // always cache the normal form to avoid unexpected cache misses
        log(s"New bound: ${v.showDbg} :> ${c.showDbg}")
        cctx.nest(c -> v.toDnf) givenIn:
        //   v.state.lowerBounds ::= c
        //   v.state.upperBounds.foreach(ub => constrain(c, ub))
          ctx.addlb(c, v)
      case Conj(NF.Inter(x :: Nil), NF.Union(Nil), N,N,_,_) =>
        val da = x.args.iterator.zip(x.out).collect:
          case (t, true) => t.posPart
        val d = (x.refinement.values ++ da).toList
        if d.isEmpty then cctx.err
        else ctx.constrain(this, d.tail.foldLeft(ctx.sub(d.head, Bot))((k, t) => ctx.subor(k, ctx.sub(t, Bot))))
      case Conj(NF.Inter(x :: Nil), NF.Union(ClassLikeType(y, yargs, yrefine, in, _) :: Nil), N,N,_,_) => ???
      case Conj(NF.Inter(x :: xs), NF.Union(ClassLikeType(y, yargs, yrefine, in, _) :: Nil), N,N,_,_) => ???
      case Conj(NF.Inter(x :: xs), NF.Union(y :: ys), N,N,_,_) => ???
//       case Conj(Ninter(S(ClassLikeType(c1, a1, r1, _))), Nunion(ClassLikeType(c2, a2, r2, _) :: rest), N, N) =>
//       case Conj(Ninter(S(c)), Nunion(d :: rest), N, N) =>
//         if c.sym === d.sym then
//           c.args.zip(d.args).foreach: (ta1, ta2) =>
//             constrainArgs(ta1, ta2)
//           // TODO
//         else constrainConj(Conj(conj.i, Nunion(rest), N, N))      case _ =>
        // raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} ∧ ¬⊥" -> N :: Nil))
        cctx.err

  private def constrainArgs(lhs: TypeArg, rhs: TypeArg)(using InfCtx, CCtx, TL): Unit =
    constrain(rhs.negPart, lhs.negPart)
    constrain(lhs.posPart, rhs.posPart)

  private class SkolemBoundsInliner(using ctx: InfCtx) extends TypeMapper:
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

  private def constrainImpl(lhs: Type, rhs: Type)(using ctx: InfCtx, cctx: CCtx, tl: TL): Unit =
    val p = lhs.toDnf -> rhs.toDnf
    if cctx.cache(p) then log(s"Cached!")
    else trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
      cctx.nest(p) givenIn:
        val disj = inlineSkolemBounds(lhs & ~rhs).toDnf
        disj.cs.foreach(constrainConj(_))

  def constrain(lhs: Type, rhs: Type)(using ctx: InfCtx, cctx: CCtx, tl: TL): Unit =
    val (ps, ts) = rhs.disjuncts.partition(_.partialpattern)
    if ts.length > 1 then
      val p = lhs.toDnf -> rhs
      if cctx.cache(p) then log(s"Cached!")
      else trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
        cctx.nest(p) givenIn:
          val u = ps.foldLeft(lhs)((x, y) => x & ~y)
          val qs = ts.map(_.discriminator)
          constrainImpl(u, qs.reduce(_ | _))
          qs.zip(ts).foreach((q, y) => constrainImpl(q & u, y))
    else
      constrainImpl(lhs, rhs)
