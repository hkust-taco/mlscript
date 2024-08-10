package hkmc2
package bbml

import scala.collection.mutable

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

// * TODO use mutabnle cache instead for correct asymptotic complexity
type Cache = Set[(Type, Type)]

case class CCtx(cache: Cache, parents: Ls[(Type, Type)], origin: Term, exp: Opt[GeneralType]):
  def err(using Raise) =
    raise(ErrorReport(
      msg"Type error in term ${origin.show}${exp match
          case S(ty) => msg" with expected type ${ty.toString}"
          case N => msg""
        }" -> origin.toLoc
      :: parents.reverse.map(p =>
        msg"because: cannot constrain  ${p._1.toString}  <:  ${p._2.toString}" -> N
      )
    ))
  def nest(sub: (Type, Type)): CCtx =
    copy(cache = cache + sub, parents = parents match
      case `sub` :: _ => parents
      case _ =>  sub :: parents
    )
object CCtx:
  inline def init(origin: Term, exp: Opt[GeneralType]) = CCtx(Set.empty, Nil, origin, exp)
def cctx(using CCtx): CCtx = summon

class ConstraintSolver(infVarState: InfVarUid.State, tl: TraceLogger):
  import tl.{trace, log}

  import hkmc2.bbml.NormalForm.*

  // TODO: cache x-fresh
  private def freshXVar(lvl: Int): InfVar = InfVar(lvl, infVarState.nextUid, new VarState(), false)

  def extrude(ty: Type)(using lvl: Int, pol: Bool): Type =
  trace[Type](s"Extruding[${printPol(pol)}] $ty", r => s"~> $r"):
    if ty.lvl <= lvl then ty else ty match
    case ClassType(sym, targs) =>
      ClassType(sym, targs.map {
        case Wildcard(in, out) =>
          Wildcard(extrude(in)(using lvl, !pol), extrude(out))
        case t: Type => Wildcard(extrude(t)(using lvl, !pol), extrude(t))
      })
    case v @ InfVar(_, uid, _, true) => // * skolem
      if pol then Top else Bot
    case v @ InfVar(_, uid, _, false) =>
      val nv = freshXVar(lvl)
      if pol then
        v.state.upperBounds ::= nv
        nv.state.lowerBounds = v.state.lowerBounds.map(extrude) // * propagate
      else
        v.state.lowerBounds ::= nv
        nv.state.upperBounds = v.state.upperBounds.map(extrude) // * propagate
      nv
    case FunType(args, ret, eff) =>
      FunType(args.map(arg => extrude(arg)(using lvl, !pol)), extrude(ret), extrude(eff))
    case ComposedType(lhs, rhs, p) =>
      Type.mkComposedType(extrude(lhs), extrude(rhs), p)
    case NegType(ty) => Type.mkNegType(extrude(ty)(using lvl, !pol))
    case Top | Bot => ty

  private def constrainConj(conj: Conj)(using Ctx, CCtx): Unit = trace(s"Constraining $conj"):
    conj match
      case Conj(i, u, (v, pol) :: tail) =>
        var rest = Conj(i, u, tail)
        if v.isSkolem then constrainConj(rest)
        else
          val comp = rest.simp
          val bd = if v.lvl >= comp.lvl then comp else extrude(comp)(using v.lvl, true)
          if pol then
            val nc = Type.mkNegType(bd)
            log(s"New bound: $v <: $nc")
            cctx.nest(v -> nc) in:
              v.state.upperBounds ::= nc
              v.state.lowerBounds.foreach(lb => constrainImpl(lb, nc))
          else
            log(s"New bound: $v :> $bd")
            cctx.nest(bd -> v) in:
              v.state.lowerBounds ::= bd
              v.state.upperBounds.foreach(ub => constrainImpl(bd, ub))
      case Conj(i, u, Nil) => (conj.i, conj.u) match
        case (_, Union(N, Nil)) =>
          // raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} ∧ ¬⊥" -> N :: Nil))
          cctx.err
        case (Inter(S(NormalClassType(cls1, targs1))), Union(f, NormalClassType(cls2, targs2) :: rest)) =>
          if cls1.uid == cls2.uid then
            targs1.zip(targs2).foreach {
              case ((in1, out1), (in2, out2)) =>
                constrainImpl(in2, in1)
                constrainImpl(out1, out2)
            }
          else constrainConj(Conj(conj.i, Union(f, rest), Nil))
        case (int: Inter, Union(f, _ :: rest)) => constrainConj(Conj(int, Union(f, rest), Nil))
        case (Inter(S(NormalFunType(args1, ret1, eff1))), Union(S(NormalFunType(args2, ret2, eff2)), Nil)) =>
          if args1.length != args2.length then
            // raise(ErrorReport(msg"Cannot constrain ${conj.i.toString()} <: ${conj.u.toString()}" -> N :: Nil))
            cctx.err
          else
            args1.zip(args2).foreach {
              case (a1, a2) => constrainImpl(a2, a1)
            }
            constrainImpl(ret1, ret2)
            constrainImpl(eff1, eff2)
        case _ =>
          // raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} <: ${conj.u.toString()}" -> N :: Nil))
          cctx.err

  private def constrainDNF(disj: Disj)(using Ctx, CCtx): Unit =
    disj.conjs.foreach(constrainConj(_))

  private def constrainImpl(lhs: Type, rhs: Type)(using Ctx, CCtx) =
    if cctx.cache((lhs, rhs)) then log(s"Cached!")
    else trace(s"CONSTRAINT $lhs <: $rhs"):
      cctx.nest(lhs -> rhs) in:
        constrainDNF(dnf(lhs & rhs.!)(using raise)) // TODO: inline skolem bounds
  def constrain(lhs: Type, rhs: Type)(using Ctx, CCtx): Unit =
    constrainImpl(lhs, rhs)

