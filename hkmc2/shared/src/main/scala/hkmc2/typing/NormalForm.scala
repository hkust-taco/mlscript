package hkmc2
package typing
package logicsub

import scala.annotation.tailrec

import syntax.*
import semantics.*
import Message.MessageContext
import hkmc2.utils.*, shorthands.*
import utils.*
import utils.Scope

sealed abstract class NormalForm extends TypeExt

object NF:
  final case class Inter(v: Ls[ClassLikeType]) extends NormalForm:
    lazy val toBasic = v.foldLeft[Type](Top)(_ & _).toBasic
    def merge(other: Inter): Opt[Inter] =
      other.v.foldLeft(Opt(v))((r, w) => r.flatMap(w.merge(_))).map(Inter(_))

  final case class Union(v: Ls[ClassLikeType]) extends NormalForm:
    lazy val toBasic = v.foldLeft[Type](Bot)(_ | _).toBasic
    def merge(other: Union) = Union(v ++ other.v)

  object Inter:
    val empty = Inter(Nil)
  object Union:
    val empty = Union(Nil)

final case class Disj(cs: Ls[Conj]) extends NormalForm:
  lazy val toBasic = cs.foldLeft[Type](Bot)(_ | _).toBasic
  def isBot = cs.isEmpty

final case class Conj(
  i: NF.Inter, u: NF.Union,
  v1: Opt[InfVar], v2: Opt[InfVar],
  ps: Ls[InfVar], ns: Ls[InfVar]
) extends NormalForm:
  lazy val toBasic = (i.toBasic & ~u.toBasic & v1.getOrElse(Top) & v2.fold(Top)(~_)).toBasic
  def merge(that: Conj)(using TL): Opt[Conj] =
  tl.traceNot[Opt[Conj]](s"merge ${this.showDbg} and ${that.showDbg}", r => s"= ${r.map(_.showDbg)}"):
    val Conj(i1, u1, v1, w1, x1, y1) = this
    val Conj(i2, u2, v2, w2, x2, y2) = that
    val xs = x1 ++ x2
    val ys = y1 ++ y2
    if xs.intersect(ys).nonEmpty then N
    else i1.merge(i2) match
      case N => N
      case S(i) =>
        val u = u1.merge(u2)
        (v1.orElse(v2), w1.orElse(w2)) match
          case (S(v), S(w)) if v.sym === w.sym => N
          case (v,w) => S(Conj(i, u, v, w, xs, ys))

object Conj:
  val empty: Conj = Conj(NF.Inter.empty, NF.Union.empty, N, N, Nil, Nil)
  def mkVar(v: InfVar, pol: Bool) =
    if pol then
      Conj(NF.Inter.empty, NF.Union.empty, S(v), N, Nil, Nil)
    else Conj(NF.Inter.empty, NF.Union.empty, N, S(v), Nil, Nil)
  def mkInter(inter: ClassLikeType) =
    Conj(NF.Inter(Ls(inter)), NF.Union.empty, N, N, Nil, Nil)
  def mkUnion(union: ClassLikeType) =
    Conj(NF.Inter.empty, NF.Union(Ls(union)), N, N, Nil, Nil)
object Disj:
  val bot = Disj(Nil)
  val top = Disj(Ls(Conj.empty))
 
object NormalForm:
  def inter(lhs: Disj, rhs: Disj)(using TL): Disj =
  tl.traceNot[Disj](s"inter ${lhs.showDbg} and ${rhs.showDbg}", r => s"= ${r.showDbg}"):
    if lhs.isBot || rhs.isBot then Disj.bot
    else Disj(lhs.cs.flatMap(lhs => rhs.cs.flatMap(rhs => lhs.merge(rhs) match {
      case S(conj) => conj :: Nil
      case N => Nil
    })))

  def union(lhs: Disj, rhs: Disj): Disj = Disj(lhs.cs ++ rhs.cs)

  def neg(ty: Type)(using TL): Disj =
  tl.traceNot[Disj](s"~Disj ${ty.showDbg} ${ty.getClass} ${ty.toBasic.showDbg}", r => s"= ${r.showDbg}"):
    ty match
    case u: NF.Union => Disj(Ls(Conj(NF.Inter(Nil), u, N, N, Nil, Nil)))
    case v: InfVar => Disj(Ls(Conj.mkVar(v, false)))
    case ct: ClassLikeType => Disj(Ls(Conj.mkUnion(ct)))
    case _ => dnf(~(ty.toBasic))

  def dnf(ty: Type)(using TL): Disj =
  tl.traceNot[Disj](s"Disj ${ty.showDbg} ${ty.getClass}", r => s"= ${r.showDbg}"):
    ty match
    case d: Disj => d
    case c: Conj => Disj(Ls(c))
    case i: NF.Inter => Disj(Ls(Conj(i, NF.Union.empty, N, N, Nil, Nil)))
    case _ => ty.toBasic match
    case Top => Disj.top
    case Bot => Disj.bot
    case v: InfVar => Disj(Ls(Conj.mkVar(v, true)))
    case ct: ClassLikeType => Disj(Conj.mkInter(ct) :: Nil)
    case Inter(lhs, rhs) => inter(dnf(lhs), dnf(rhs))
    case Union(lhs, rhs) => union(dnf(lhs), dnf(rhs))
    case Neg(ty) => neg(ty)
