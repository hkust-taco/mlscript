package hkmc2
package bbml

import scala.annotation.tailrec

import semantics.*
import Message.MessageContext
import mlscript.utils.*, shorthands.*
import utils.*

final case class Disj(conjs: Ls[Conj]) extends NormalForm with CachedBasicType:
  def isBot: Bool = conjs.isEmpty
  def mkBasic: BasicType =
    BasicType.union(conjs.map(_.toBasic))
  def toDnf(using TL): Disj = this
  override def toString: Str =
    if conjs.isEmpty then "D()"
    else s"D( ${conjs.mkString(" || ")} )"
object Disj:
  val bot: Disj = Disj(Nil)
  val top: Disj = Disj(Conj.empty :: Nil)

sealed abstract case class Conj(i: Inter, u: Union, vars: Ls[(InfVar, Bool)])
extends NormalForm with CachedBasicType:
  def merge(that: Conj)(using TL): Option[Conj] =
  tl.traceNot[Option[Conj]](s"merge $this and $that", r => s"= ${r}"):
    val Conj(i1, u1, vars1) = this
    val Conj(i2, u2, vars2) = that
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
  def mkBasic: BasicType =
    BasicType.inter(i.toBasic :: NegType(u.toBasic) :: vars.map{
      case (tv, true) => tv
      case (tv, false) => NegType(tv)
    })
  def toDnf(using TL): Disj = Disj(this :: Nil)
  override def toString: Str =
    ((i :: Nil).filterNot(_.isTop) :::
      (u :: Nil).filterNot(_.isBot).map("~{"+_+"}") :::
      vars.map:
        case (tv, true) => tv.toString
        case (tv, false) => "~" + tv.toString
    ).mkString(" && ")
object Conj:
  // * Conj objects cannot be created with `new` except in this file.
  // * This is because we want to sort the vars in the apply function.
  def apply(i: Inter, u: Union, vars: Ls[(InfVar, Bool)]) = new Conj(i, u, vars.sortWith {
    case ((InfVar(lv1, _, _, sk1), _), (InfVar(lv2, _, _, sk2), _)) => !(sk1 || !sk2 && lv1 <= lv2)
  }){}
  lazy val empty: Conj = Conj(Inter.empty, Union.empty, Nil)
  def mkVar(v: InfVar, pol: Bool) = Conj(Inter.empty, Union.empty, (v, pol) :: Nil)
  def mkInter(inter: ClassLikeType | FunType) =
    Conj(Inter(S(inter)), Union.empty, Nil)
  def mkUnion(union: ClassLikeType | FunType) =
    Conj(Inter.empty, union match {
      case cls: ClassLikeType => Union(N, cls :: Nil)
      case fun: FunType => Union(S(fun), Nil)
    }, Nil)

// * Some(ClassType) -> C[in D_i out D_i], Some(FunType) -> D_1 ->{D_2} D_3, None -> Top
final case class Inter(v: Opt[ClassLikeType | FunType]) extends NormalForm:
  def isTop: Bool = v.isEmpty
  def merge(other: Inter): Option[Inter] = (v, other.v) match
    case (S(ClassLikeType(cls1, targs1)), S(ClassLikeType(cls2, targs2))) if cls1.uid === cls2.uid =>
      S(Inter(S(ClassLikeType(cls1, targs1.lazyZip(targs2).map(_ & _)))))
    case (S(_: ClassLikeType), S(_: ClassLikeType)) => N
    case (S(FunType(a1, r1, e1)), S(FunType(a2, r2, e2))) =>
      S(Inter(S(FunType(a1.lazyZip(a2).map(_ | _), r1 & r2, e1 & e2))))
    case (S(v), N) => S(Inter(S(v)))
    case (N, v) => S(Inter(v))
    case _ => N
  def toBasic: BasicType = v.getOrElse(Top)
  def toDnf(using TL): Disj = Disj(Conj(this, Union(N, Nil), Nil) :: Nil)
  override def toString: Str =
    toBasic.toString
object Inter:
  lazy val empty: Inter = Inter(N)

// * fun: Some(FunType) -> D_1 ->{D_2} D_3, None -> bot
final case class Union(fun: Opt[FunType], cls: Ls[ClassLikeType])
extends NormalForm with CachedBasicType:
  def isBot = fun.isEmpty && cls.isEmpty
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
  }.foldLeft[Ls[ClassLikeType]](Nil)((res, cls) => (res, cls) match {
    case (Nil, cls) => cls :: Nil
    case (ClassLikeType(cls1, targs1) :: tail, ClassLikeType(cls2, targs2)) if cls1.uid === cls2.uid => 
      ClassLikeType(cls1, targs1.lazyZip(targs2).map(_ | _)) :: tail
    case (head :: tail, cls) => cls :: head :: tail
  }))
  def mkBasic: BasicType =
    BasicType.union(fun.toList ::: cls)
  def toDnf(using TL): Disj = NormalForm.neg(this)
  override def toString: Str =
    toType.toString
object Union:
  val empty: Union = Union(N, Nil)

sealed abstract class NormalForm extends TypeExt:
  def toBasic: BasicType
  
  lazy val lvl: Int = toBasic.lvl // TODO improve: avoid inefficient use of toBasic
  
  def subst(using map: Map[Uid[InfVar], InfVar]): ThisType =
    toBasic.subst

object NormalForm:
  def inter(lhs: Disj, rhs: Disj)(using TL): Disj =
  tl.traceNot[Disj](s"inter $lhs and $rhs", r => s"= ${r}"):
    if lhs.isBot || rhs.isBot then Disj.bot
    else Disj(lhs.conjs.flatMap(lhs => rhs.conjs.flatMap(rhs => lhs.merge(rhs) match {
      case S(conj) => conj :: Nil
      case N => Nil
    })))

  def union(lhs: Disj, rhs: Disj): Disj = Disj(lhs.conjs ++ rhs.conjs)

  def neg(ty: Type)(using TL): Disj =
  tl.traceNot[Disj](s"~DNF $ty ${ty.getClass} ${ty.toBasic}", r => s"= ${r}"):
    ty match
    case u: Union => Disj(Conj(Inter(N), u, Nil) :: Nil)
    case _ => ty.toBasic match
    case Top => Disj.bot
    case Bot => Disj.top
    case v: InfVar => Disj(Conj.mkVar(v, false) :: Nil)
    case ct: ClassLikeType => Disj(Conj.mkUnion(ct) :: Nil)
    case ft: FunType => Disj(Conj.mkUnion(ft) :: Nil)
    case ComposedType(lhs, rhs, pol) =>
      if pol then inter(neg(lhs), neg(rhs)) else union(neg(lhs), neg(rhs))
    case NegType(ty) => dnf(ty)

  def dnf(ty: Type)(using TL): Disj =
  tl.traceNot[Disj](s"DNF $ty ${ty.getClass}", r => s"= ${r}"):
    ty match
    case d: Disj => d
    case c: Conj => Disj(c :: Nil)
    case i: Inter => Disj(Conj(i, Union(N, Nil), Nil) :: Nil)
    case _ => ty.toBasic match
    case Top => Disj.top
    case Bot => Disj.bot
    case v: InfVar => Disj(Conj.mkVar(v, true) :: Nil)
    case ct: ClassLikeType => Disj(Conj.mkInter(ct.toNorm) :: Nil)
    case ft: FunType => Disj(Conj.mkInter(ft.toNorm) :: Nil)
    case ComposedType(lhs, rhs, pol) =>
      if pol then union(dnf(lhs), dnf(rhs)) else inter(dnf(lhs), dnf(rhs))
    case NegType(ty) => neg(ty)

