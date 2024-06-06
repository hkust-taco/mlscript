package hkmc2
package bbml

import scala.annotation.tailrec

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

object NormalForm:
  // TODO: level
  final case class NormalClassType(cls: ClassSymbol, targs: List[(Disj, Disj)])
  final case class NormalFunType(args: List[Disj], ret: Disj, eff: Disj)
  enum Disj:
    case Bot
    case Con(conj: Conj)
    case DC(disj: Disj, conj: Conj)
  enum Conj:
    case INU(i: Inter, u: Union)
    case CVar(conj: Conj, v: Type.InfVar)
    case CNVar(conj: Conj, v: Type.InfVar)
  enum Inter:
    case Top
    case Fun(fun: NormalFunType)
    case Cls(cls: NormalClassType)
  enum Union:
    case Bot
    case Fun(fun: NormalFunType)
    case Uni(lhs: Union, rhs: NormalClassType)

  private lazy val topConj = Conj.INU(Inter.Top, Union.Bot)

  private def inter(lhs: Disj, rhs: Disj): Disj = Disj.Bot // TODO

  @tailrec
  private def union(lhs: Disj, rhs: Disj): Disj = rhs match
    case Disj.Bot => lhs
    case Disj.Con(conj) => Disj.DC(lhs, conj)
    case Disj.DC(disj, conj) => union(Disj.DC(lhs, conj), disj)

  private def neg(ty: Type)(using raise: Raise): Disj = ty match
    case Type.Top => Disj.Bot
    case Type.Bot => Disj.Con(topConj)
    case v: Type.InfVar => Disj.Con(Conj.CNVar(topConj, v))
    case Type.ClassType(cls, targs) =>
      Disj.Con(Conj.INU(Inter.Top, Union.Uni(Union.Bot, NormalClassType(cls, targs.map {
        case Wildcard(in, out) => (dnf(in), dnf(out))
        case ty: Type =>
          val res = dnf(ty)
          (res, res)
      }))))
    case Type.FunType(args, ret, eff) =>
      Disj.Con(Conj.INU(Inter.Top, Union.Fun(NormalFunType(
        args.map(dnf), dnf(ret), dnf(eff)
      ))))
    case Type.ComposedType(lhs, rhs, pol) =>
      if pol then inter(neg(lhs), neg(rhs)) else union(neg(lhs), neg(rhs))
    case Type.NegType(ty) => dnf(ty)
    case _: Type.PolymorphicType =>
      raise(ErrorReport(msg"Polymorphic type is not allowed." -> N :: Nil))
      Disj.Bot

  def dnf(ty: Type)(using raise: Raise): Disj = ty match
    case Type.Top => Disj.Con(topConj)
    case Type.Bot => Disj.Bot
    case v: Type.InfVar => Disj.Con(Conj.CVar(topConj, v))
    case Type.ClassType(cls, targs) =>
      Disj.Con(Conj.INU(Inter.Cls(NormalClassType(cls, targs.map {
        case Wildcard(in, out) => (dnf(in), dnf(out))
        case ty: Type =>
          val res = dnf(ty)
          (res, res)
      })), Union.Bot))
    case Type.FunType(args, ret, eff) =>
      Disj.Con(Conj.INU(Inter.Fun(NormalFunType(
        args.map(dnf), dnf(ret), dnf(eff)
      )), Union.Bot))
    case Type.ComposedType(lhs, rhs, pol) =>
      if pol then union(dnf(lhs), dnf(rhs)) else inter(dnf(lhs), dnf(rhs))
    case Type.NegType(ty) => neg(ty)
    case _: Type.PolymorphicType =>
      raise(ErrorReport(msg"Polymorphic type is not allowed." -> N :: Nil))
      Disj.Bot
