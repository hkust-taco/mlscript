package hkmc2
package bbml

import mlscript.utils.*, shorthands.*
import syntax.*
import semantics.*, semantics.Term.*
import utils.*
import scala.collection.mutable.{Set => MutSet}

// * General types include mono types (i.e., Type), forall quantified type, and poly function types
sealed abstract class GeneralType:
  // * Is this type polymorphic
  lazy val isPoly: Bool
  // * Polymorphic level
  def lvl: Int
  // * Return itself if it is actually monomorphic.
  // * Otherwise, evaluate fallback
  def monoOr(fallback: => Type): Type

  // * The map function should not change the shape!
  protected type ThisType <: GeneralType
  def map(f: ThisType => ThisType): ThisType
  def subst(using map: Map[Uid[InfVar], InfVar]): ThisType

// * Types that can be used as class type arguments
sealed trait TypeArg:
  def lvl: Int
  def mapArg(f: Type => Type): TypeArg
  def & (that: TypeArg): TypeArg = (this, that) match
    case (Wildcard(in1, out1), Wildcard(in2, out2)) => Wildcard(in1 | in2, out1 & out2)
    case (ty: Type, Wildcard(in2, out2)) => Wildcard(ty | in2, ty & out2)
    case (Wildcard(in1, out1), ty: Type) => Wildcard(in1 | ty, out1 & ty)
    case (ty1: Type, ty2: Type) => ty1 & ty2
  def | (that: TypeArg): TypeArg = (this, that) match
    case (Wildcard(in1, out1), Wildcard(in2, out2)) => Wildcard(in1 & in2, out1 | out2)
    case (ty: Type, Wildcard(in2, out2)) => Wildcard(ty & in2, ty | out2)
    case (Wildcard(in1, out1), ty: Type) => Wildcard(in1 & ty, out1 | ty)
    case (ty1: Type, ty2: Type) => ty1 | ty2
  def posPart: Type = this match
    case Wildcard(_, out) => out
    case ty: Type => ty
  def negPart: Type = this match
    case Wildcard(in, _) => in
    case ty: Type => ty

case class Wildcard(in: Type, out: Type) extends TypeArg {
  def mapArg(f: Type => Type): Wildcard = Wildcard(f(in), f(out))

  override def toString: Str = in match
    case `out` => in.toString
    case Bot =>
      out match
        case Top => "?"
        case _ => s"out $out"
    case _ =>
      out match
        case Top => s"in $in"
        case _ => s"in $in out $out"
  
  override lazy val lvl: Int = in.lvl.max(out.lvl)
}

object Wildcard:
  def in(ty: Type): Wildcard = Wildcard(ty, Top)
  def out(ty: Type): Wildcard = Wildcard(Bot, ty)
  def empty: Wildcard = Wildcard(Bot, Top)

trait CachedBasicType extends Type:
  override lazy val toBasic: BasicType = mkBasic
  def mkBasic: BasicType

abstract class TypeExt extends Type:
  override def hashCode: Int =
    toBasic.hashCode
  override def equals(that: Any): Bool =
    toBasic === that
  
sealed abstract class Type extends GeneralType with TypeArg:
  
  override protected type ThisType = Type
  
  def toBasic: BasicType
  def toDnf(using TL): Disj
  
  // * Remove redundant Top/Bot.
  // * e.g., Top & Int === Int
  lazy val simp: Type = this
  
  
  lazy val isPoly: Bool = false
  
  override def map(f: Type => Type): Type =
    toBasic.mapBasic(f) // TODO improve: map on all type constructors
  
  def mapArg(f: Type => Type): Type = f(this)
  
  def monoOr(fallback: => Type): Type = this
  
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
  
  protected[bbml] def paren: Str = toBasic match
    case _: InfVar | _: ClassLikeType | _: NegType | Top | Bot => toString
    case _: ComposedType | _: FunType => s"($toString)"

sealed abstract class BasicType extends Type:
  
  lazy val lvl: Int = this match
    case ClassLikeType(name, targs) =>
      targs.map(_.lvl).maxOption.getOrElse(0)
    case InfVar(lvl, _, _, _) => lvl
    case FunType(args, ret, eff) =>
      (ret :: eff :: args).map(_.lvl).max
    case ComposedType(lhs, rhs, _) =>
      lhs.lvl.max(rhs.lvl)
    case NegType(ty) => ty.lvl
    case Top | Bot => 0
  
  def mapBasic(f: Type => Type): Type = this match
    case ClassLikeType(name, targs) => ClassLikeType(name, targs.map(_.mapArg(f)))
    case FunType(args, ret, eff) => FunType(args.map(f), f(ret), f(eff))
    case ComposedType(lhs, rhs, pol) => Type.mkComposedType(f(lhs), f(rhs), pol)
    case NegType(ty) => Type.mkNegType(f(ty))
    case Top | Bot | _: InfVar => this
    
  override def toString: Str =
    def printEff(eff: Type) = eff match
      case Bot => ""
      // case ty if ty == allocSkolem => ""
      case _ => s"{$eff}"
    this match
    case ClassLikeType(name, targs) =>
      if targs.isEmpty then s"${name.nme}" else s"${name.nme}[${targs.mkString(", ")}]"
    case v @ InfVar(lvl, uid, _, isSkolem) =>
      val name = v.hint.getOrElse("α")
      if isSkolem then s"<$name>${uid}_$lvl" else s"$name${uid}_$lvl"
    case FunType(arg :: Nil, ret, eff) => s"${arg.paren} ->${printEff(eff)} ${ret.paren}"
    case FunType(args, ret, eff) => s"(${args.mkString(", ")}) ->${printEff(eff)} ${ret.paren}"
    case ComposedType(lhs, rhs, pol) => s"${lhs.paren} ${if pol then "∨" else "∧"} ${rhs.paren}"
    case NegType(ty) => s"¬${ty.paren}"
    case Top => "⊤"
    case Bot => "⊥"
  
  def toBasic: BasicType = this
  
  var _dnf: Disj = null
  def withDnf(d: Disj): this.type = // TODO: remove?
    assert(_dnf eq null)
    _dnf = d
    this
  def toDnf(using TL) =
    if _dnf eq null
    then
      val d = NormalForm.dnf(this)
      _dnf = d
      d
    else _dnf

trait CachedNorm[A <: AnyRef]:
  
  def mkNorm(using TL): A
  
  private var _norm: A = null.asInstanceOf
  final def hasNorm: Bool = !(_norm eq null)
  def withNorm(d: A): this.type = // TODO: remove?
    assert(!hasNorm)
    _norm = d
    this
  def toNorm(using TL) =
    if _norm eq null
    then
      val d = mkNorm
      _norm = d
      d
    else _norm
  

object BasicType:
  // TOOD dedup
  def union(tys: Ls[BasicType]): BasicType = tys match
    case Nil => Bot
    case ty :: Nil => ty
    case ty :: tys => ComposedType(ty, union(tys), true)
  def inter(tys: Ls[BasicType]): BasicType = tys match
    case Nil => Bot
    case ty :: Nil => ty
    case ty :: tys => ComposedType(ty, inter(tys), false)

case class ClassLikeType(name: TypeSymbol | ModuleSymbol, targs: Ls[TypeArg]) extends BasicType with CachedNorm[ClassLikeType]:
  def mkNorm(using TL): ClassLikeType =
    ClassLikeType(name,
      targs.map:
        case ty: Type => ty.toDnf
        case Wildcard(i, o) => Wildcard(i.toDnf, o.toDnf)
    )
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType =
    ClassLikeType(name, targs.map {
        case Wildcard(in, out) => Wildcard(in.subst, out.subst)
        case ty: Type => ty.subst
      })

final case class InfVar(vlvl: Int, uid: Uid[InfVar], state: VarState, isSkolem: Bool)(val hint: Option[Str]) extends BasicType:
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType = map.get(uid).getOrElse(this)

given Ordering[InfVar] = Ordering.by(_.uid)

case class FunType(args: Ls[Type], ret: Type, eff: Type) extends BasicType with CachedNorm[FunType]:
  def mkNorm(using TL): FunType =
    FunType(args.map(_.toDnf), ret.toDnf, eff.toDnf)
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType =
    FunType(args.map(_.subst), ret.subst, eff.subst)

case class ComposedType(lhs: Type, rhs: Type, pol: Bool) extends BasicType: // * Positive -> union
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType =
    Type.mkComposedType(lhs.subst, rhs.subst, pol)
  override lazy val simp: Type =
    Type.mkComposedType(lhs.simp, rhs.simp, pol)
  
final case class NegType(ty: Type) extends BasicType:
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType = NegType(ty.subst)
  override lazy val simp: Type = ty.simp.!

object Top extends BasicType:
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType = Top

object Bot extends BasicType:
  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType = Bot

object Type:
  def mkComposedType(lhs: Type, rhs: Type, pol: Bool): Type = if pol
    then lhs | rhs
    else lhs & rhs
  def mkNegType(ty: Type): Type = ty.!

// * Poly types can not be used as type arguments
case class PolyType(tvs: Ls[InfVar], body: GeneralType) extends GeneralType:
  override protected type ThisType = GeneralType

  override lazy val isPoly: Bool = true
  override lazy val lvl: Int = (body :: tvs).map(_.lvl).max
  override def toString: Str = s"forall ${tvs.mkString(", ")}: $body"
  override def monoOr(fallback: => Type): Type = fallback
  override def map(f: GeneralType => GeneralType): PolyType = PolyType(tvs, f(body))

  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType =
    PolyType(tvs.map {
      case v @ InfVar(lvl, uid, state, skolem) =>
        val newSt = new VarState()
        newSt.lowerBounds = state.lowerBounds.map(_.subst)
        newSt.upperBounds = state.upperBounds.map(_.subst)
        InfVar(lvl, uid, newSt, skolem)(v.hint)
    }, body.subst)

  // * This function will only return the body after substitution
  // * and \dom(map) should cover all tvs.
  // * This function is dedicated to `skolemize` and `instantiate`.
  private def substAndGetBody(using map: Map[Uid[InfVar], InfVar]): GeneralType =
    tvs.foreach:
      case InfVar(lvl, uid, state, skolem) =>
        val v = map(uid)
        v.state.lowerBounds = state.lowerBounds.map(_.subst)
        v.state.upperBounds = state.upperBounds.map(_.subst)
    body.subst

  def skolemize(nextUid: => Uid[InfVar], lvl: Int)(tl: TL) =
    // * Note that by this point, the state is supposed to be frozen/treated as immutable
    val map = tvs.map(v =>
      val sk = InfVar(lvl, nextUid, new VarState(), true)(v.hint)
      tl.log(s"skolemize $v ~> $sk")
      v.uid -> sk
    ).toMap
    substAndGetBody(using map)
  
  def instantiate(nextUid: => Uid[InfVar], lvl: Int)(tl: TL): GeneralType =
    val map = tvs.map(v =>
      val nv = InfVar(lvl, nextUid, new VarState(), false)(v.hint)
      tl.log(s"instantiate $v ~> $nv")
      v.uid -> nv
    ).toMap
    substAndGetBody(using map)

object PolyType:
  def generalize(ty: GeneralType, lvl: Int): PolyType =
    val tvs = MutSet[InfVar]()
    object CollectTVs extends TypeTraverser:
      override def apply(pol: Boolean)(ty: GeneralType): Unit = ty match
        case v @ InfVar(vlvl, _, state, _) if vlvl > lvl =>
          if tvs.add(v) then
            state.lowerBounds.foreach: bd =>
              apply(true)(bd)
            state.upperBounds.foreach: bd =>
              apply(false)(bd)
            super.apply(pol)(ty)
        case _ => super.apply(pol)(ty)
    CollectTVs(true)(ty)
    PolyType(tvs.toList.sorted, ty)

// * Functions that accept/return a polymorphic type.
// * Note that effects are always monomorphic
// * Poly types can not be used as type arguments
case class PolyFunType(args: Ls[GeneralType], ret: GeneralType, eff: Type) extends GeneralType:
  override protected type ThisType = GeneralType

  lazy val isPoly: Bool = (ret :: args).exists(_.isPoly)
  lazy val lvl: Int = (ret :: eff :: args).map(_.lvl).max
  override def toString: Str = s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
  private lazy val mono: Opt[FunType] = if isPoly then N else
    Some(FunType(args.map {
      case t: Type => t
      case pf: PolyFunType => pf.mono.get
      case _ => ??? // * Impossible
    }, ret match {
      case t: Type => t
      case pf: PolyFunType => pf.mono.get
      case _ => ??? // * Impossible
    }, eff))
  override def monoOr(fallback: => Type): Type = mono.getOrElse(fallback)
  override def map(f: GeneralType => GeneralType): PolyFunType =
    PolyFunType(args.map(f), f(ret), f(eff).monoOr(???)) // * Must be mono

  override def subst(using map: Map[Uid[InfVar], InfVar]): ThisType =
    PolyFunType(args.map(_.subst), ret.subst, eff.subst)

class VarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil
