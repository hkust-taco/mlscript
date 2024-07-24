package hkmc2
package bbml

import mlscript.utils.*, shorthands.*
import syntax.*
import semantics.*, semantics.Term.*

// * General types include mono types (i.e., Type), forall quantified type, and poly function types
sealed abstract class GeneralType:
  // * Is this type polymorphic
  lazy val isPoly: Bool
  // * Polymorphic level
  lazy val lvl: Int
  def toString(): String
  // * Get the mono type, otherwise we return fallback
  def monoOr(fallback: => Type): Type

  // * The map function should not change the shape!
  protected type ThisType
  def map(f: ThisType => ThisType): ThisType

// * Types that can be used as class type arguments
sealed trait TypeArg:
  lazy val lvl: Int
  def map(f: Type => Type): TypeArg

case class Wildcard(in: Type, out: Type) extends TypeArg {
  override def map(f: Type => Type): Wildcard = Wildcard(f(in), f(out))

  override def toString(): String = s"in $in out $out"
  override lazy val lvl: Int = in.lvl.max(out.lvl)
}

object Wildcard:
  def in(ty: Type): Wildcard = Wildcard(ty, Top)
  def out(ty: Type): Wildcard = Wildcard(Bot, ty)
  def empty: Wildcard = Wildcard(Bot, Top)

abstract class Type extends GeneralType with TypeArg:
  override protected type ThisType = Type

  override def toString(): String = this match
    case ClassType(name, targs) =>
      if targs.isEmpty then s"${name.nme}" else s"${name.nme}[${targs.mkString(", ")}]"
    case InfVar(lvl, uid, _, isSkolem) => if isSkolem then s"<α>${uid}_$lvl" else s"α${uid}_$lvl"
    case FunType(args, ret, eff) => s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
    case ComposedType(lhs, rhs, pol) => s"(${lhs}) ${if pol then "∨" else "∧"} (${rhs})"
    case NegType(ty) => s"¬(${ty})"
    case Top => "⊤"
    case Bot => "⊥"

  lazy val lvl: Int = this match
    case ClassType(name, targs) =>
      targs.map(_.lvl).maxOption.getOrElse(0)
    case InfVar(lvl, _, _, _) => lvl
    case FunType(args, ret, eff) =>
      (ret :: eff :: args).map(_.lvl).max
    case ComposedType(lhs, rhs, _) =>
      lhs.lvl.max(rhs.lvl)
    case NegType(ty) => ty.lvl
    case Top | Bot => 0

  lazy val isPoly: Bool = false

  def & (that: Type): Type = this match
    case Top => that
    case Bot => Bot
    case _ => that match
      case Top => this
      case Bot => Bot
      case ComposedType(l, r, false) => this & l & r
      case _ => if this === that
        then this
        else ComposedType(this, that, false)
  def | (that: Type): Type = this match
    case Top => Top
    case Bot => that
    case _ => that match
      case Top => Top
      case Bot => this
      case ComposedType(l, r, true) => this | l | r
      case _ => if this === that
        then this
        else ComposedType(this, that, true)
  def ! : Type = this match
    case Top => Bot
    case Bot => Top
    case NegType(res) => res
    case ComposedType(l, r, true) => l.! & r.!
    case ComposedType(l, r, false) => l.! | r.!
    case _ => NegType(this)

  override def map(f: Type => Type): Type = this match
    case ClassType(name, targs) => ClassType(name, targs.map(_.map(f)))
    case _: InfVar => f(this)
    case FunType(args, ret, eff) => FunType(args.map(f), f(ret), f(eff))
    case ComposedType(lhs, rhs, pol) => Type.mkComposedType(f(lhs), f(rhs), pol)
    case NegType(ty) => Type.mkNegType(f(ty))
    case Top | Bot => f(this)
  def monoOr(fallback: => Type): Type = this

case class ClassType(name: ClassSymbol, targs: Ls[TypeArg]) extends Type
case class InfVar(vlvl: Int, uid: Uid[InfVar], state: VarState, isSkolem: Bool) extends Type
case class FunType(args: Ls[Type], ret: Type, eff: Type) extends Type
case class ComposedType(lhs: Type, rhs: Type, pol: Bool) extends Type // * Positive -> union
case class NegType(ty: Type) extends Type
object Top extends Type
object Bot extends Type

object Type:
  def mkComposedType(lhs: Type, rhs: Type, pol: Bool): Type = if pol
    then lhs | rhs
    else lhs & rhs
  def mkNegType(ty: Type): Type = ty.!

// TODO: bounds
// * Poly types can not be used as type arguments
case class PolyType(tv: Ls[InfVar], body: GeneralType) extends GeneralType:
  override protected type ThisType = GeneralType

  override lazy val isPoly: Bool = true
  override lazy val lvl: Int = (body :: tv).map(_.lvl).max
  override def toString(): String = s"forall ${tv.mkString(", ")}: $body"
  override def monoOr(fallback: => Type): Type = fallback
  override def map(f: GeneralType => GeneralType): PolyType = PolyType(tv, f(body))

// * Functions that accept/return a polymorphic type.
// * Note that effects are always monomorphic
// * Poly types can not be used as type arguments
case class PolyFunType(args: Ls[GeneralType], ret: GeneralType, eff: Type) extends GeneralType:
  override protected type ThisType = GeneralType

  lazy val isPoly: Bool = (ret :: args).exists(_.isPoly)
  lazy val lvl: Int = (ret :: eff :: args).map(_.lvl).max
  override def toString(): String = s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
  private lazy val mono: Option[FunType] = if isPoly then N else
    Some(FunType(args.map {
      case t: Type => t
      case pf: PolyFunType => pf.mono.get
    }, ret match {
      case t: Type => t
      case pf: PolyFunType => pf.mono.get
    }, eff))
  override def monoOr(fallback: => Type): Type = if isPoly then fallback else
    FunType(args.map {
      case t: Type => t
      case pt: PolyType => pt.monoOr(???) // * Must be mono
      case pf: PolyFunType => pf.monoOr(???) // * Must be mono
    }, ret match {
      case t: Type => t
      case pt: PolyType => pt.monoOr(???) // * Must be mono
      case pf: PolyFunType => pf.monoOr(???) // * Must be mono
    }, eff)
  override def map(f: GeneralType => GeneralType): PolyFunType = PolyFunType(args.map(f), f(ret), f(eff).monoOr(???)) // * Must be mono

class VarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil
