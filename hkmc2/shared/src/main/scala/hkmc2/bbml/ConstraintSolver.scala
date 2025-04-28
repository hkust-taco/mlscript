package hkmc2
package bbml

import scala.collection.mutable

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*
import utils.*
import utils.Scope

// * TODO use mutabnle cache instead for correct asymptotic complexity
type Cache = Set[(Type, Type)]
type ExtrudeCache = mutable.HashMap[(Uid[InfVar], Bool), InfVar]

case class CCtx(cache: Cache, parents: Ls[(Type, Type)], origin: Term, exp: Opt[GeneralType])(using Scope):
  def err(using Raise) =
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
    copy(cache = cache + sub, parents = parents match
      case `sub` :: _ => parents
      case _ =>  sub :: parents
    )
object CCtx:
  inline def init(origin: Term, exp: Opt[GeneralType])(using Scope) = CCtx(Set.empty, Nil, origin, exp)
def cctx(using CCtx): CCtx = summon

class ConstraintSolver(infVarState: InfVarUid.State, elState: Elaborator.State, tl: TraceLogger):
  import tl.{trace, log}

  import hkmc2.bbml.NormalForm.*

  private def freshXVar(lvl: Int, sym: Symbol, hint: Str): InfVar =
    InfVar(lvl, infVarState.nextUid, new VarState(), false)(InstSymbol(sym)(using elState), hint)

  def extrude(ty: Type)(using lvl: Int, pol: Bool, cache: ExtrudeCache, bbctx: BbCtx, cctx: CCtx, tl: TL): Type =
  trace[Type](s"Extruding[${printPol(pol)}] ${ty.showDbg}", r => s"~> ${r.showDbg}"):
    if ty.lvl <= lvl then ty else ty.toBasic/*TODO improve extrude directly*/ match
    case ClassLikeType(sym, targs) =>
      ClassLikeType(sym, targs.map {
        case Wildcard(in, out) =>
          Wildcard(extrude(in)(using lvl, !pol), extrude(out))
        case t: Type => Wildcard(extrude(t)(using lvl, !pol), extrude(t))
      })
    case v @ InfVar(_, uid, state, true) => // * skolem
      cache.getOrElse(uid -> pol, {
        val nv = freshXVar(lvl, v.sym, v.hint)
        cache += uid -> pol -> nv
        if pol then
          constrainImpl(state.upperBounds.foldLeft[Type](Top)(_ & _), nv)
        else
          constrainImpl(nv, state.lowerBounds.foldLeft[Type](Bot)(_ | _))
        nv
      })
    case v @ InfVar(_, uid, _, false) =>
      cache.getOrElse(uid -> pol, {
        val nv = freshXVar(lvl, v.sym, v.hint)
        cache += uid -> pol -> nv
        if pol then
          v.state.upperBounds ::= nv
          nv.state.lowerBounds = v.state.lowerBounds.map(extrude) // * propagate
        else
          v.state.lowerBounds ::= nv
          nv.state.upperBounds = v.state.upperBounds.map(extrude) // * propagate
          nv.state.disjsub ++= v.state.disjsub.map:
            case DisjSub(ds, dss, cs) =>
              val d = ds.mapKeys(v0 => if v === v0 then nv else v0)
              DisjSub(mutable.LinkedHashSet.from(d), dss, cs)
          nv.state.disjsub.foreach(_.commit())
        nv
      })
    case ft @ FunType(args, ret, eff) =>
      FunType(args.map(arg => extrude(arg)(using lvl, !pol)), extrude(ret), extrude(eff))
    case ComposedType(lhs, rhs, p) =>
      Type.mkComposedType(extrude(lhs), extrude(rhs), p)
    case NegType(ty) => Type.mkNegType(extrude(ty)(using lvl, !pol))
    case Top | Bot => ty

  private def constrainConj(conj: Conj)(using BbCtx, CCtx, TL): Unit = trace(s"Constraining ${conj.showDbg}"):
    conj match
      case Conj(i, u, (v, pol) :: tail) =>
        var rest = Conj(i, u, tail)
        if v.isSkolem then constrainConj(rest)
        else
          val bd = if v.lvl >= rest.lvl then rest else extrude(rest)(using v.lvl, true, mutable.HashMap.empty)
          if pol then
            val nc = Type.mkNegType(bd)
            log(s"New bound: ${v.showDbg} <: ${nc.showDbg}")
            cctx.nest(v -> nc) givenIn:
              v.state.upperBounds ::= nc
              v.state.lowerBounds.foreach(lb => constrainImpl(lb, nc))
          else
            log(s"New bound: ${v.showDbg} :> ${bd.showDbg}")
            cctx.nest(bd -> v) givenIn:
              v.state.lowerBounds ::= bd
              v.state.upperBounds.foreach(ub => constrainImpl(bd, ub))
              val (dss, cs) = v.state.disjsub.toList.map(_.check(Map(v -> bd))).unzip
              dss.flatten.foreach(_.commit())
              cs.flatten.foreach(u => constrainImpl(u._1, u._2))
      case Conj(i, u, Nil) => (conj.i, conj.u) match
        case (_, Union(N, Nil, Nil)) =>
          // raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} ∧ ¬⊥" -> N :: Nil))
          cctx.err
        case (Inter(S(ClassLikeType(cls1, targs1))), Union(f, ClassLikeType(cls2, targs2) :: rest, rcd)) =>
          if cls1.uid === cls2.uid then
            targs1.zip(targs2).foreach: (ta1, ta2) =>
              constrainArgs(ta1, ta2)
          else constrainConj(Conj(conj.i, Union(f, rest, rcd), Nil))
        case (int: Inter, Union(f, _ :: rest, rcd)) => constrainConj(Conj(int, Union(f, rest, rcd), Nil))
        case (Inter(S(RcdType(u))), Union(f, Nil, RcdType(w) :: Nil)) =>
          val um = u.toMap
          val wm = w.toMap
          val k = w.keys.toSet
          if k.subsetOf(um.keySet) then
            k.foreach(k => constrainImpl(um(k), wm(k)))
          else cctx.err
        case (Inter(S(u: RcdType)), Union(f, Nil, rs)) =>
          val us = u.fields.keys.toSet
          val ws = rs.filter(_.fields.keys.forall(us))
          if ws.isEmpty then cctx.err
          else
            val q = ws.foldLeft(Bot: Type): (q, w) =>
              val wq = Type.discriminant(w)
              Type.disjoint(wq, u) match
                case N => constrainImpl(u & wq, w)
                case S(k) => k.foreach(k => DisjSub(mutable.LinkedHashSet.from(k), Nil, Ls(wq -> w)).commit())
              q | wq
            Type.disjoint(q.!, u) match
              case N => constrainImpl(Top, Bot)
              case S(k) => k.foreach(k => DisjSub(mutable.LinkedHashSet.from(k), Nil, Ls(Top -> Bot)).commit())
        case (Inter(S(fs: Ls[FunType])), Union(S(FunType(args2, ret2, eff2)), Nil, Nil)) =>
          val k = args2.flatMap(x => Type.disjoint(x, x))
          if k.forall(_.nonEmpty) then
            val f = fs.filter(_.args.length === args2.length)
            if args2.isEmpty then
              if f.isEmpty then
                cctx.err
              else f.foreach: f =>
                constrainImpl(f.ret, ret2)
                constrainImpl(f.eff, eff2)
            else
              val args = f.map(x => RcdType(x.args.zipWithIndex.map(u => (s"${u._2}", u._1))))
              val args2r = args2.zipWithIndex.map(u => (s"${u._2}", u._1))
              val args2q = RcdType(args2r)
              val (cs, dss) = (args.iterator.map(Type.discriminant).zip(f).map:
                case (q, f) =>
                  val cs = (f.ret, ret2) :: (f.eff, eff2) :: Nil //rcs
                  Type.disjoint(q, args2q) match
                    case N => (cs, Nil)
                    case S(k) =>
                      (Nil, k.map(k => DisjSub(mutable.LinkedHashSet.from(k), Nil, cs)))).toList.unzip
              val c = (args2q, args.foldLeft(Bot: Type)(_ | _))
              if k.isEmpty then
                if f.isEmpty then
                  cctx.err
                else
                  dss.flatten.foreach(_.commit())
                  constrainImpl(c._1, c._2)
                  cs.flatten.foreach(u => constrainImpl(u._1, u._2))
              else
                val cs0 = c :: cs.flatten
                val dss0 = dss.flatten
                k.reduce((x, y) => y.flatMap(y => x.map(_ ++ y))).foreach: k =>
                  DisjSub(mutable.LinkedHashSet.from(k), dss0, cs0).commit()
        case _ =>
          // raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} <: ${conj.u.toString()}" -> N :: Nil))
          cctx.err

  private def constrainDNF(disj: Disj)(using BbCtx, CCtx, TL): Unit =
    disj.conjs.foreach(constrainConj(_))

  private def constrainArgs(lhs: TypeArg, rhs: TypeArg)(using BbCtx, CCtx, TL): Unit =
    constrainImpl(rhs.negPart, lhs.negPart)
    constrainImpl(lhs.posPart, rhs.posPart)

  private def inlineSkolemBounds(ty: Type, pol: Bool)(using cache: Set[Uid[InfVar]]): Type = ty.toBasic match
    case v @ InfVar(_, uid, state, skolem) if skolem && !cache(uid) =>
      given Set[Uid[InfVar]] = cache + uid
      inlineSkolemBounds(if pol then state.upperBounds.foldLeft[Type](v)(_ & _) else state.lowerBounds.foldLeft[Type](v)(_ | _), pol)
    case ComposedType(lhs, rhs, p) => ComposedType(inlineSkolemBounds(lhs, pol), inlineSkolemBounds(rhs, pol), p)
    case NegType(ty) => NegType(inlineSkolemBounds(ty, !pol))
    case _: ClassLikeType | _: FunType | _: RcdType |_: InfVar | Top | Bot => ty

  private def constrainImpl(lhs: Type, rhs: Type)(using BbCtx, CCtx, TL): Unit =
    if cctx.cache((lhs, rhs)) then log(s"Cached!")
    else trace(s"CONSTRAINT ${lhs.showDbg} <: ${rhs.showDbg}"):
      cctx.nest(lhs -> rhs) givenIn:
        val ty = dnf(inlineSkolemBounds(lhs & rhs.!, true)(using Set.empty)) 
        constrainDNF(ty)
  def constrain(lhs: Type, rhs: Type)(using BbCtx, CCtx, TL): Unit =
    constrainImpl(lhs, rhs)

