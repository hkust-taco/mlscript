package hkmc2
package typing
package logicsub

import hkmc2.utils.*, shorthands.*
import syntax.*
import semantics.*, semantics.Term.*
import utils.*
import scala.collection.mutable.{Set => MutSet}
import utils.Scope, Scope.scope
import Elaborator.State


sealed abstract class InfType:
  def lvl: Int
  def show(using Scope, InfCtx, Raise): Str
  def showDbg: Str

sealed trait TypeArg:
  def lvl: Int
  def show(using Scope, InfCtx, Raise): Str
  def showDbg: Str
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

case class Wildcard(in: Type, out: Type) extends TypeArg:
  lazy val lvl = in.lvl.max(out.lvl)
  def show(using Scope, InfCtx, Raise): Str = in match
    case `out` => in.show
    case Bot =>
      out match
        case Top => "?"
        case _ => s"out ${out.show}"
    case _ =>
      out match
        case Top => s"in ${in.show}"
        case _ => s"in ${in.show} out ${out.show}"
  def showDbg: Str = s"in ${in.showDbg} out ${out.showDbg}"

object Wildcard:
  def in(ty: Type) = Wildcard(ty, Top)
  def out(ty: Type) = Wildcard(Bot, ty)
  def empty = Wildcard(Bot, Top)

case class PolyType(tvs: Ls[InfVar], outer: Opt[InfVar], body: InfType) extends InfType:
  lazy val lvl = (body :: tvs).map(_.lvl).max
  def show(using Scope, InfCtx, Raise) = showDbg //TODO
  def showDbg = ???

case class PolyFunType(args: Ls[InfType], ret: InfType, eff: Type) extends InfType:
  lazy val lvl = (ret :: eff :: args).iterator.map(_.lvl).max
  def show(using Scope, InfCtx, Raise) =
    s"(${args.map(_.show).mkString(", ")}) ->{${eff.show}} ${ret.show}"
  def showDbg = s"(${args.map(_.showDbg).mkString(", ")}) ->{${eff.showDbg}} ${ret.showDbg}"

sealed abstract class Type extends InfType with TypeArg:
  lazy val lvl = toBasic match
    case ClassLikeType(name, targs, refinement, i, o) =>
      val args = targs.iterator
      val refine = refinement.iterator.map(_._2)
      (args ++ refine).map(_.lvl).maxOption.getOrElse(0)
    case InfVar(lvl, _, _) => lvl
    case Top | Bot => 0
    case Union(lhs, rhs) => lhs.lvl.max(rhs.lvl)
    case Inter(lhs, rhs) => lhs.lvl.max(rhs.lvl)
    case Neg(ty) => ty.lvl
  def show(using Scope, InfCtx, Raise) = showDbg //TODO
  def showDbg: Str = toBasic match
    case ClassLikeType(name, targs, refinement, _,_) =>
      val cls = if targs.isEmpty then s"${name.nme}" else s"${name.nme}[${targs.map(_.showDbg).mkString(", ")}]"
      val r = refinement.map { case (l,t) => s"$l: ${t.showDbg}" }.mkString(", ")
      cls ++ (if refinement.isEmpty then "" else s" & {$r}")
    case v @ InfVar(lvl, sym, isSkolem) =>
      val name = if sym.hint.isEmpty then s"${sym.nme}" else s"${sym.nme}(${sym.hint})"
      if isSkolem then s"${name}${sym.uid}_${lvl}" else s"'${name}${sym.uid}_${lvl}"
    case Union(lhs, rhs) => s"${lhs.parenDbg} ∨ ${rhs.parenDbg}"
    case Inter(lhs, rhs) => s"${lhs.parenDbg} ∧ ${rhs.parenDbg}"
    case Neg(ty) => s"¬${ty.parenDbg}"
    case Top => "⊤"
    case Bot => "⊥"

  protected[logicsub] def paren(using Scope, InfCtx, Raise): Str = toBasic match
    case _: InfVar | _: ClassLikeType | _: Neg | Top | Bot => show
    case _ => s"($show)"

  protected[logicsub] def parenDbg: Str = toBasic match
    case _: InfVar | _: ClassLikeType | _: Neg | Top | Bot => showDbg
    case _ => s"($showDbg)"

  lazy val toBasic: BasicType
  lazy val discriminator = Discriminator(true)(this).simp
  lazy val partialpattern: Bool = simp match
    case _: InfVar => false
    case Top | Bot => true
    case ClassLikeType(s, args, refine,_,o) =>
      val p = args.iterator.zip(o).forall:
        case (t, true) => t.posPart.partialpattern
        case (t, false) => t is Wildcard.empty
      p && refine.values.forall(_.partialpattern)
    case Union(x,y) => x.partialpattern && y.partialpattern
    case Inter(x,y) => x.partialpattern && y.partialpattern
    case Neg(x) => x.partialpattern

  lazy val simp: BasicType = (toBasic match
    case Union(x,y) => x.simp | y.simp
    case Inter(x,y) => x.simp & y.simp
    case Neg(Union(x,y)) => Neg(x).simp & Neg(y).simp
    case Neg(Inter(x,y)) => Neg(x).simp | Neg(y).simp
    case Neg(Neg(x)) => x.simp
    case Neg(x) => ~x
    case x => x).toBasic

  def disjuncts: Ite[Type] = simp match
    case Union(x,y) => x.disjuncts ++ y.disjuncts
    case x => Ite(x)

  var _dnf: Disj = null
  def toDnf(using TL) = 
    if _dnf eq null then _dnf = NormalForm.dnf(this)
    _dnf

  def |(that: Type): Type = this match
    case Top => Top
    case Bot => that
    case _ => that match
      case Top => Top
      case Bot => this
      case Union(l, r) => this | l | r
      case _ => if this === that then this else Union(this, that)
  def &(that: Type): Type = this match
    case Top => that
    case Bot => Bot
    case _ => that match
      case Top => this
      case Bot => Bot
      case Inter(l, h) => this & l & h
      case _ => if this === that then this else Inter(this, that)
  def unary_~ : Type = toBasic match
    case Top => Bot
    case Bot => Top
    case Inter(x,y) => ~x | ~y
    case Union(x,y) => ~x & ~y
    case Neg(x) => x
    case _ => Neg(this)

abstract class TypeExt extends Type

sealed abstract class BasicType extends Type:
  lazy val toBasic = this
final case class InfVar(vlvl: Int, sym: InfVarSymbol, isSkolem: Bool) extends BasicType
object Bot extends BasicType
object Top extends BasicType
case class Union(lhs: Type, rhs: Type) extends BasicType
case class Inter(lhs: Type, rhs: Type) extends BasicType
case class Neg(t: Type) extends BasicType
case class ClassLikeType(
  sym: ClsTag, args: Ls[TypeArg],
  refinement: Ls[(Tree.Ident, Type)],
  in: Ls[Bool], out: Ls[Bool]
) extends BasicType:
  private def merge(u: Ls[TypeArg], r: Ls[Tree.Ident -> Type]) =
    val targs = args.lazyZip(u).map(_ & _)
    val rmap = mergeMap(refinement, r)(_ & _)
    val lbl = (refinement.iterator ++ r.iterator).map(_._1).distinct
    val refine = lbl.zip(lbl.map(rmap)).toList
    ClassLikeType(sym, targs, refine, in, out)
  def merge(cs: Ls[ClassLikeType]): Opt[Ls[ClassLikeType]] = cs match
    case Nil => S(Ls(this))
    case x :: _ if x.sym is sym =>
      S(Ls(cs.foldLeft(this)((x, y) => x.merge(y.args, y.refinement))))
    case _ => N    
type ClsTag = LitSymbol | TypeSymbol | ModuleOrObjectSymbol

object Discriminator extends TypeMapper:
  override def apply(pol: Bool)(t: Type) = t.simp match
    case _: InfVar => Top
    case c @ ClassLikeType(_: LitSymbol, _,_,_,_) => c
    case c @ ClassLikeType(s: (TypeSymbol | ModuleOrObjectSymbol), args, refine, i,o) =>
      // TODO flags in `s.defn.get.tparams`
      val a = args.iterator.zip(o).map:
        case (t, true) => apply(pol)(t.posPart) // TODO
        case _ => Wildcard.empty
      ClassLikeType(s, a.toList, refine.mapValues(apply(pol)), i,o)
    case t @ Neg(ClassLikeType(_, _, refine, _,_)) => if refine.isEmpty then t else Top
    case t => super.apply(pol)(t)
