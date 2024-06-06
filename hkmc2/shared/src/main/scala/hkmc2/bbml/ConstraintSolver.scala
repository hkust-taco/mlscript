package hkmc2
package bbml

import scala.collection.mutable

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

type Cache = Set[(Type, Type)]
class ConstraintSolver(raise: Raise):

  import hkmc2.bbml.NormalForm.*

  // TODO: sort dnf
  private def constrainConj(conj: Conj)(using cache: Cache): Unit = conj match
    case Conj.INU(i, u) => (i, u) match
      case (_, Union.Bot) => raise(ErrorReport(msg"Can not solve ${i.toString()} <: ⊥" -> N :: Nil))
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
      case _ => raise(ErrorReport(msg"Can not solve ${i.toString()} <: ${u.toString()}" -> N :: Nil))
    case Conj.CVar(conj, v) => // TODO: extrude
      val nc = Type.NegType(conj.toType)
      given Cache = cache + (v -> nc)
      v.state.upperBounds ::= nc
      v.state.lowerBounds.foreach(lb => constrain(lb, nc))
    case Conj.CNVar(conj, v) =>
      val c = conj.toType
      given Cache = cache + (c -> v)
      v.state.lowerBounds ::= c
      v.state.upperBounds.foreach(ub => constrain(c, ub))

  private def constrainDNF(disj: Disj)(using cache: Cache): Unit = disj match
    case Disj.Bot => ()
    case Disj.Con(conj) => constrainConj(conj)
    case Disj.DC(disj, conj) =>
      constrainDNF(disj)
      constrainConj(conj)

  private def constrainImpl(lhs: Type, rhs: Type)(using cache: Cache) =
    if cache((lhs, rhs)) then () else constrainDNF(dnf(Type.ComposedType(lhs, Type.NegType(rhs), false))(using raise))
  def constrain(lhs: Type, rhs: Type): Unit =
    constrainImpl(lhs, rhs)(using Set.empty)
