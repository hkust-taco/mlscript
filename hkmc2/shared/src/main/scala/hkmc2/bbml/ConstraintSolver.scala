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

  private def freshXVar(lvl: Int): Type.InfVar = Type.InfVar(lvl, infVarState.nextUid, new VarState())

  private def extrude(ty: Type)(using skolems: SkolemSet, lvl: Int, pol: Bool): Type = if ty.lvl <= lvl then ty else ty match
    case Type.ClassType(sym, targs) =>
      Type.ClassType(sym, targs.map {
        case Wildcard(in, out) =>
          Wildcard(extrude(in)(using skolems, lvl, !pol), extrude(out))
        case t => ??? // TODO
      })
    case v @ Type.InfVar(_, uid, _) if skolems(uid) =>
      if pol then Type.Top else Type.Bot
    case v @ Type.InfVar(_, uid, _) =>
      val nv = freshXVar(lvl)
      if pol then
        v.state.upperBounds ::= nv
        nv.state.lowerBounds = v.state.lowerBounds.map(extrude) // * propagate
      else
        v.state.lowerBounds ::= nv
        nv.state.upperBounds = v.state.upperBounds.map(extrude) // * propagate
      nv
    case Type.FunType(args, ret, eff) =>
      Type.FunType(args.map(arg => extrude(arg)(using skolems, lvl, !pol)), extrude(ret), extrude(eff))
    case Type.ComposedType(lhs, rhs, p) =>
      Type.mkComposedType(extrude(lhs), extrude(rhs), p)
    case Type.NegType(ty) => Type.mkNegType(extrude(ty)(using skolems, lvl, !pol))
    case Type.Top | Type.Bot => ty

  private def constrainConj(conj: Conj)(using cache: Cache, skolems: SkolemSet): Unit = trace(s"Constraining $conj"):
    conj.sort match
    case Conj.INU(i, u) => (i, u) match
      case (_, Union.Bot) => raise(ErrorReport(msg"Cannot solve ${i.toString()} ∧ ¬⊥" -> N :: Nil))
      case (Inter.Cls(NormalClassType(cls1, targs1)), Union.Uni(uni, NormalClassType(cls2, targs2))) =>
        if cls1.uid == cls2.uid then
          targs1.zip(targs2).foreach {
            case ((in1, out1), (in2, out2)) =>
              constrain(in2.toType, in1.toType)
              constrain(out1.toType, out2.toType)
          }
        else constrainConj(Conj.INU(i, uni))
      case (_, Union.Uni(uni, _)) => constrainConj(Conj.INU(i, uni))
      case (Inter.Fun(NormalFunType(args1, ret1, eff1)), Union.Fun(NormalFunType(args2, ret2, eff2))) =>
        args1.zip(args2).foreach { // TODO: check the length!
          case (a1, a2) => constrain(a2.toType, a1.toType)
        }
        constrain(ret1.toType, ret2.toType)
        constrain(eff1.toType, eff2.toType)
      case _ => raise(ErrorReport(msg"Cannot solve ${i.toString()} <: ${u.toString()}" -> N :: Nil))
    case Conj.CVar(_, v) if skolems(v.uid) =>
      raise(ErrorReport(msg"Cannot constrain skolem ${v.toString()}" -> N :: Nil))
    case Conj.CNVar(_, v) if skolems(v.uid) =>
      raise(ErrorReport(msg"Cannot constrain skolem ${v.toString()}" -> N :: Nil))
    case Conj.CVar(conj, v) if v.lvl >= conj.lvl =>
      val nc = Type.mkNegType(conj.toType)
      given Cache = cache + (v -> nc)
      v.state.upperBounds ::= nc
      v.state.lowerBounds.foreach(lb => constrain(lb, nc))
    case Conj.CNVar(conj, v) if v.lvl >= conj.lvl =>
      val c = conj.toType
      given Cache = cache + (c -> v)
      v.state.lowerBounds ::= c
      v.state.upperBounds.foreach(ub => constrain(c, ub))
    case Conj.CVar(conj, v) =>
      val nc = Type.mkNegType(extrude(conj.toType)(using skolems, v.lvl, true))
      given Cache = cache + (v -> nc)
      v.state.upperBounds ::= nc
      v.state.lowerBounds.foreach(lb => constrain(lb, nc))
    case Conj.CNVar(conj, v) =>
      val c = extrude(conj.toType)(using skolems, v.lvl, true)
      given Cache = cache + (c -> v)
      v.state.lowerBounds ::= c
      v.state.upperBounds.foreach(ub => constrain(c, ub))

  private def constrainDNF(disj: Disj)(using cache: Cache, skolems: SkolemSet): Unit = disj match
    case Disj.Bot => ()
    case Disj.Con(conj) => constrainConj(conj)
    case Disj.DC(disj, conj) =>
      constrainDNF(disj)
      constrainConj(conj)

  private def constrainImpl(lhs: Type, rhs: Type)(using cache: Cache, skolems: SkolemSet) =
    if cache((lhs, rhs)) then log(s"Cached!")
    else trace(s"CONSTRAINT $lhs <: $rhs"):
      constrainDNF(dnf(lhs & rhs.!)(using raise))
  def constrain(lhs: Type, rhs: Type)(using skolems: SkolemSet): Unit =
    constrainImpl(lhs, rhs)(using Set.empty, skolems)
