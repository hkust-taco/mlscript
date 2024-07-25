package hkmc2
package bbml

import scala.collection.mutable

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

class ConstraintSolver(raise: Raise, infVarState: InfVarUid.State, tl: TraceLogger):
  import tl.{trace, log}

  import hkmc2.bbml.NormalForm.*
  type Cache = Set[(Type, Type)]

  private def freshXVar(lvl: Int): InfVar = InfVar(lvl, infVarState.nextUid, new VarState(), false)

  private def extrude(ty: Type)(using lvl: Int, pol: Bool): Type = if ty.lvl <= lvl then ty else ty match
    case ClassType(sym, targs) =>
      ClassType(sym, targs.map {
        case Wildcard(in, out) =>
          Wildcard(extrude(in)(using lvl, !pol), extrude(out))
        case t => ??? // TODO
      })
    case v @ InfVar(_, uid, _, true) =>
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

  private def constrainConj(conj: Conj)(using cache: Cache): Unit = trace(s"Constraining $conj"):
    conj.pick match
      case S((v, pol)) =>
        if v.isSkolem then constrainConj(conj.complement(v))
        else
          val comp = conj.complement(v).simp
          val bd = if v.lvl >= comp.lvl then comp else extrude(comp)(using v.lvl, true)
          if pol then
            val nc = Type.mkNegType(bd)
            given Cache = cache + (v -> nc)
            v.state.upperBounds ::= nc
            v.state.lowerBounds.foreach(lb => constrain(lb, nc))
          else
            given Cache = cache + (bd -> v)
            v.state.lowerBounds ::= bd
            v.state.upperBounds.foreach(ub => constrain(bd, ub))
      case _ => (conj.i, conj.u) match
        case (_, Union(N, Nil)) => raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} ∧ ¬⊥" -> N :: Nil))
        case (Inter(S(NormalClassType(cls1, targs1))), Union(f, NormalClassType(cls2, targs2) :: rest)) =>
          if cls1.uid == cls2.uid then
            targs1.zip(targs2).foreach {
              case ((in1, out1), (in2, out2)) =>
                constrain(in2, in1)
                constrain(out1, out2)
            }
          else constrainConj(Conj(conj.i, Union(f, rest), Nil))
        case (int: Inter, Union(f, _ :: rest)) => constrainConj(Conj(int, Union(f, rest), Nil))
        case (Inter(S(NormalFunType(args1, ret1, eff1))), Union(S(NormalFunType(args2, ret2, eff2)), Nil)) =>
          if args1.length != args2.length then
            raise(ErrorReport(msg"Cannot constrain ${conj.i.toString()} <: ${conj.u.toString()}" -> N :: Nil))
          else
            args1.zip(args2).foreach {
              case (a1, a2) => constrain(a2, a1)
            }
            constrain(ret1, ret2)
            constrain(eff1, eff2)
        case _ => raise(ErrorReport(msg"Cannot solve ${conj.i.toString()} <: ${conj.u.toString()}" -> N :: Nil))

  private def constrainDNF(disj: Disj)(using cache: Cache): Unit = disj.conjs.foreach(constrainConj(_))

  private def constrainImpl(lhs: Type, rhs: Type)(using cache: Cache) =
    if cache((lhs, rhs)) then log(s"Cached!")
    else trace(s"CONSTRAINT $lhs <: $rhs"):
      constrainDNF(dnf(lhs & rhs.!)(using raise)) // TODO: inline skolem bounds
  def constrain(lhs: Type, rhs: Type): Unit =
    constrainImpl(lhs, rhs)(using Set.empty)
