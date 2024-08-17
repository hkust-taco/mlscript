package hkmc2
package bbml

import scala.annotation.tailrec

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*

final case class Disj(conjs: Ls[Conj]) extends NormalForm:
  def toType: Type = ComposedType(conjs.foldLeft[Type](Bot)((res, c) => res | c.toType), Bot, true)
  def isBot: Bool = conjs.isEmpty
object Disj:
  val bot: Disj = Disj(Nil)
  val top: Disj = Disj(Conj.empty :: Nil)

sealed abstract case class Conj(i: Inter, u: Union, vars: Ls[(InfVar, Bool)]) extends NormalForm:
  def toType: Type = i.toType &
    vars.foldLeft(Type.mkNegType(u.toType))((res, v) => if v._2 then res & v._1 else res & Type.mkNegType(v._1))
  def merge(other: Conj): Option[Conj] =
    val Conj(i1, u1, vars1) = this
    val Conj(i2, u2, vars2) = other
    i1.merge(i2) match
      case S(i) =>
        val u = u1.merge(u2)
        val vars = (vars1 ++ vars2).sortWith {
          case ((InfVar(_, uid1, _, _), _), (InfVar(_, uid2, _, _), _)) => uid1 <= uid2
        }.foldLeft[Opt[Ls[(InfVar, Bool)]]](S(Nil))((res, p) => (res, p) match { // * None -> bot
          case (N, _) => N
          case (S(Nil), p) => S(p :: Nil)
          case (S((InfVar(v, uid1, s, k), p1) :: tail), (InfVar(_, uid2, _, _), p2)) if uid1 === uid2 =>
            if p1 === p2 then S((InfVar(v, uid1, s, k), p1) :: tail) else N
          case (S(head :: tail), p) => S(p :: head :: tail)
        })
        vars match
          case S(vars) => S(Conj(i, u, vars))
          case _ => N
      case N => N
object Conj:
  // * Conj objects cannot be created with `new` except in this file.
  // * This is because we want to sort the vars in the apply function.
  def apply(i: Inter, u: Union, vars: Ls[(InfVar, Bool)]) = new Conj(i, u, vars.sortWith {
    case ((InfVar(lv1, _, _, sk1), _), (InfVar(lv2, _, _, sk2), _)) => !(sk1 || !sk2 && lv1 <= lv2)
  }){}
  lazy val empty: Conj = Conj(Inter.empty, Union.empty, Nil)
  def mkVar(v: InfVar, pol: Bool) = Conj(Inter.empty, Union.empty, (v, pol) :: Nil)
  def mkInter(inter: ClassType | FunType) = Conj(Inter(S(inter)), Union.empty, Nil)
  def mkUnion(union: ClassType | FunType) = Conj(Inter.empty, union match {
    case cls: ClassType => Union(N, cls :: Nil)
    case fun: FunType => Union(S(fun), Nil)
  }, Nil)

// * Some(ClassType) -> C[in D_i out D_i], Some(FunType) -> D_1 ->{D_2} D_3, None -> Top
final case class Inter(v: Opt[ClassType | FunType]) extends NormalForm:
  def toType: Type = v.getOrElse(Top)
  def merge(other: Inter): Option[Inter] = (v, other.v) match
    case (S(ClassType(cls1, targs1)), S(ClassType(cls2, targs2))) if cls1.uid === cls2.uid =>
      S(Inter(S(ClassType(cls1, targs1.lazyZip(targs2).map(_ & _)))))
    case (S(_: ClassType), S(_: ClassType)) => N
    case (S(FunType(a1, r1, e1)), S(FunType(a2, r2, e2))) =>
      S(Inter(S(FunType(a1.lazyZip(a2).map(_ | _), r1 & r2, e1 & e2))))
    case (S(v), N) => S(Inter(S(v)))
    case (N, v) => S(Inter(v))
    case _ => N
object Inter:
  lazy val empty: Inter = Inter(N)

// * fun: Some(FunType) -> D_1 ->{D_2} D_3, None -> bot
final case class Union(fun: Opt[FunType], cls: Ls[ClassType]) extends NormalForm:
  def toType = fun.getOrElse(Bot) |
    cls.foldLeft[Type](Bot)(_ | _)
  def merge(other: Union): Union = Union((fun, other.fun) match {
    case (S(FunType(a1, r1, e1)), S(FunType(a2, r2, e2))) =>
      S(FunType(a1.lazyZip(a2).map(_ & _), r1 | r2, e1 | e2))
    case (S(f), N) => S(f)
    case (N, S(f)) => S(f)
    case (N, N) => N
  }, (cls ++ other.cls).sortWith { // * Merge the same classes
    case (cls1, cls2) => cls1.name.uid <= cls2.name.uid
  }.foldLeft[Ls[ClassType]](Nil)((res, cls) => (res, cls) match {
    case (Nil, cls) => cls :: Nil
    case (ClassType(cls1, targs1) :: tail, ClassType(cls2, targs2)) if cls1.uid === cls2.uid => 
      ClassType(cls1, targs1.lazyZip(targs2).map(_ | _)) :: tail
    case (head :: tail, cls) => cls :: head :: tail
  }))
object Union:
  val empty: Union = Union(N, Nil)

sealed abstract class NormalForm:
  def toType: Type

object NormalForm:
  def inter(lhs: Disj, rhs: Disj): Disj =
    if lhs.isBot || rhs.isBot then Disj.bot
    else Disj(lhs.conjs.flatMap(lhs => rhs.conjs.flatMap(rhs => lhs.merge(rhs) match {
      case S(conj) => conj :: Nil
      case N => Nil
    })))

  def union(lhs: Disj, rhs: Disj): Disj = Disj(lhs.conjs ++ rhs.conjs)

  def neg(ty: Type)(using raise: Raise): Disj = ty match
    case Top => Disj.bot
    case Bot => Disj.top
    case v: InfVar => Disj(Conj.mkVar(v, false) :: Nil)
    case ct: ClassType => Disj(Conj.mkUnion(ct) :: Nil)
    case ft: FunType => Disj(Conj.mkUnion(ft) :: Nil)
    case ComposedType(lhs, rhs, pol) =>
      if pol then inter(neg(lhs), neg(rhs)) else union(neg(lhs), neg(rhs))
    case NegType(ty) => dnf(ty)

  def dnf(ty: Type)(using raise: Raise): Disj = ty match
    case Top => Disj.top
    case Bot => Disj.bot
    case v: InfVar => Disj(Conj.mkVar(v, true) :: Nil)
    case ct: ClassType => Disj(Conj.mkInter(ct) :: Nil)
    case ft: FunType => Disj(Conj.mkInter(ft) :: Nil)
    case ComposedType(lhs, rhs, pol) =>
      if pol then union(dnf(lhs), dnf(rhs)) else inter(dnf(lhs), dnf(rhs))
    case NegType(ty) => neg(ty)

