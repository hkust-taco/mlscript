package hkmc2
package bbml

import scala.annotation.tailrec

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

sealed trait NormalForm
final class Disj(val conjs: Ls[Conj]) extends ComposedType(conjs.foldLeft[Type](Bot)((res, c) => res | c), Bot, true) with NormalForm:
  lazy val isBot: Bool = conjs.isEmpty
object Disj:
  def apply(conjs: Ls[Conj]) = new Disj(conjs)
  def unapply(disj: Disj): Opt[Ls[Conj]] = S(disj.conjs)
  lazy val bot: Disj = Disj(Nil)
  lazy val top: Disj = Disj(Conj.empty :: Nil)
final class Conj(val i: Inter, val u: Union, val vars: Ls[(InfVar, Bool)]) extends ComposedType(i,
  vars.foldLeft(Type.mkNegType(u))((res, v) => if v._2 then res & v._1 else res & Type.mkNegType(v._1)), false
) with NormalForm:
  def merge(other: Conj): Option[Conj] = (this, other) match
    case (Conj(i1, u1, vars1), Conj(i2, u2, vars2)) => i1.merge(i2) match
      case S(i) =>
        val u = u1.merge(u2)
        val vars = (vars1 ++ vars2).sortWith {
          case ((InfVar(_, uid1, _, _), _), (InfVar(_, uid2, _, _), _)) => uid1 <= uid2
        }.foldLeft[Opt[Ls[(InfVar, Bool)]]](S(Nil))((res, p) => (res, p) match {
          case (N, _) => N
          case (S(Nil), p) => S(p :: Nil)
          case (S((InfVar(v, uid1, s, k), p1) :: tail), (InfVar(_, uid2, _, _), p2)) if uid1 == uid2 =>
            if p1 == p2 then S((InfVar(v, uid1, s, k), p1) :: tail) else N
          case (S(head :: tail), p) => S(p :: head :: tail)
        })
        vars match
          case S(vars) => S(Conj(i, u, vars))
          case _ => N
      case N => N
  def pick: Option[(InfVar, Bool)] = vars.foldLeft[Option[(InfVar, Bool)]](N)((res, p) => (res, p) match {
    case (S((InfVar(lv1, _, _, sk1), _)), (v @ InfVar(lv2, _, _, sk2), pol)) =>
      if sk1 || (!sk2 && lv1 < lv2) then S(v, pol)
      else res
    case (N, (v, p)) => S(v, p)
  })
  def complement(v: InfVar): Conj = Conj(i, u, vars.filterNot(p => p._1.uid == v.uid))
object Conj:
  def apply(i: Inter, u: Union, vars: Ls[(InfVar, Bool)]) = new Conj(i, u, vars)
  def unapply(conj: Conj): Opt[(Inter, Union, Ls[(InfVar, Bool)])] = S((conj.i, conj.u, conj.vars))
  lazy val empty: Conj = Conj(Inter.empty, Union.empty, Nil)
  def mkVar(v: InfVar, pol: Bool) = Conj(Inter.empty, Union.empty, (v, pol) :: Nil)
  def mkInter(inter: NormalClassType | NormalFunType) = Conj(Inter(S(inter)), Union.empty, Nil)
  def mkUnion(union: NormalClassType | NormalFunType) = Conj(Inter.empty, union match {
    case cls: NormalClassType => Union(N, cls :: Nil)
    case fun: NormalFunType => Union(S(fun), Nil)
  }, Nil)
final class Inter(val v: Opt[NormalClassType | NormalFunType]) extends ComposedType(v match {
  case S(c: NormalClassType) => c
  case S(f: NormalFunType) => f
  case _ => Top
}, Top, false) with NormalForm:
  def merge(other: Inter): Option[Inter] = (v, other.v) match
    case (S(NormalClassType(cls1, targs1)), S(NormalClassType(cls2, targs2))) if cls1.uid == cls2.uid =>
      S(Inter(S(NormalClassType(cls1, targs1.zip(targs2).map {
        case ((in1, out1), (in2, out2)) => (NormalForm.union(in1, in2), NormalForm.inter(out1, out2))
      }))))
    case (S(_: NormalClassType), S(_: NormalClassType)) => N
    case (S(NormalFunType(a1, r1, e1)), S(NormalFunType(a2, r2, e2))) =>
      S(Inter(S(NormalFunType(a1.zip(a2).map {
        case (a1, a2) => NormalForm.union(a1, a2)
      }, NormalForm.inter(r1, r2), NormalForm.inter(e1, e2)))))
    case (S(v), N) => S(Inter(S(v)))
    case (N, S(v)) => S(Inter(S(v)))
    case (N, N) => S(Inter(N))
    case _ => N
object Inter:
  def apply(v: Opt[NormalClassType | NormalFunType]) = new Inter(v)
  def unapply(i: Inter): Opt[Opt[NormalClassType | NormalFunType]] = S(i.v)
  lazy val empty: Inter = Inter(N)
final class Union(val fun: Opt[NormalFunType], val cls: Ls[NormalClassType]) extends ComposedType(fun.getOrElse(Bot),
  cls.foldLeft[Type](Bot)((res, c) => res | c), true
) with NormalForm:
  def merge(other: Union): Union = Union((fun, other.fun) match {
    case (S(NormalFunType(a1, r1, e1)), S(NormalFunType(a2, r2, e2))) =>
      S(NormalFunType(a1.zip(a2).map {
        case (a1, a2) => NormalForm.inter(a1, a2)
      }, NormalForm.union(r1, r2), NormalForm.union(e1, e2)))
    case (S(f), N) => S(f)
    case (N, S(f)) => S(f)
    case _ => N
  }, (cls ++ other.cls).sortWith {
    case (cls1, cls2) => cls1.cls.uid <= cls2.cls.uid
  }.foldLeft[Ls[NormalClassType]](Nil)((res, cls) => (res, cls) match {
    case (Nil, cls) => cls :: Nil
    case (NormalClassType(cls1, targs1) :: tail, NormalClassType(cls2, targs2)) if cls1.uid == cls2.uid => 
      NormalClassType(cls1, targs1.zip(targs2).map {
        case ((in1, out1), (in2, out2)) => (NormalForm.inter(in1, in2), NormalForm.union(out1, out2))
      }) :: tail
    case (head ::tail, cls) => cls :: head :: tail
  }))
object Union:
  def apply(fun: Opt[NormalFunType], cls: Ls[NormalClassType]) = new Union(fun, cls)
  def unapply(u: Union): Opt[(Opt[NormalFunType], Ls[NormalClassType])] = S(u.fun, u.cls)
  lazy val empty: Union = Union(N, Nil)

final class NormalClassType(val cls: ClassSymbol, val ntargs: List[(Disj, Disj)]) extends ClassType(cls, ntargs.map(p => Wildcard(p._1, p._2)))
object NormalClassType:
  def apply(cls: ClassSymbol, targs: List[(Disj, Disj)]) = new NormalClassType(cls, targs)
  def unapply(cls: NormalClassType): Opt[(ClassSymbol, List[(Disj, Disj)])] = S((cls.cls, cls.ntargs))
final class NormalFunType(val nargs: List[Disj], val nret: Disj, val neff: Disj) extends FunType(nargs, nret, neff)
object NormalFunType:
  def apply(args: List[Disj], ret: Disj, eff: Disj) = new NormalFunType(args, ret, eff)
  def unapply(fun: NormalFunType): Opt[(List[Disj], Disj, Disj)] = S((fun.nargs, fun.nret, fun.neff))

object NormalForm:
  def inter(lhs: Disj, rhs: Disj): Disj =
    if lhs.isBot || rhs.isBot then Disj.bot
    else Disj(lhs.conjs.flatMap(lhs => rhs.conjs.flatMap(rhs => lhs.merge(rhs) match {
      case S(conj) => conj :: Nil
      case _ => Nil
    })))

  def union(lhs: Disj, rhs: Disj): Disj = Disj(lhs.conjs ++ rhs.conjs)

  def neg(ty: Type)(using raise: Raise): Disj = ty match
    case Top => Disj.bot
    case Bot => Disj.top
    case v: InfVar => Disj(Conj.mkVar(v, false) :: Nil)
    case ClassType(cls, targs) => Disj(Conj.mkUnion(NormalClassType(cls, targs.map {
      case Wildcard(in, out) => (dnf(in), dnf(out))
      case ty: Type =>
        val res = dnf(ty)
        (res, res)
    })) :: Nil)
    case FunType(args, ret, eff) => Disj(Conj.mkUnion(NormalFunType(
      args.map(dnf), dnf(ret), dnf(eff)
    )) :: Nil)
    case ComposedType(lhs, rhs, pol) =>
      if pol then inter(neg(lhs), neg(rhs)) else union(neg(lhs), neg(rhs))
    case NegType(ty) => dnf(ty)

  def dnf(ty: Type)(using raise: Raise): Disj = ty match
    case Top => Disj.top
    case Bot => Disj.bot
    case v: InfVar => Disj(Conj.mkVar(v, true) :: Nil)
    case ClassType(cls, targs) => Disj(Conj.mkInter(NormalClassType(cls, targs.map {
      case Wildcard(in, out) => (dnf(in), dnf(out))
      case ty: Type =>
        val res = dnf(ty)
        (res, res)
    })) :: Nil)
    case FunType(args, ret, eff) => Disj(Conj.mkInter(NormalFunType(
      args.map(dnf), dnf(ret), dnf(eff)
    )) :: Nil)
    case ComposedType(lhs, rhs, pol) =>
      if pol then union(dnf(lhs), dnf(rhs)) else inter(dnf(lhs), dnf(rhs))
    case NegType(ty) => neg(ty)
