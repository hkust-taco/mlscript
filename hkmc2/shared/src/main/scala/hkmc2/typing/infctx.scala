package hkmc2
package typing
package logicsub

import scala.collection.mutable.{HashSet, HashMap, ListBuffer}
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import utils.*

import Message.MessageContext
import semantics.*, Term.*
import Elaborator.Ctx
import syntax.*
import Tree.*
import utils.Scope
import scala.collection.mutable

final case class SubOr(x: Type, y: Type, cs: Opt[Ls[SubOr]] = N):
  def lvl: Int = x.lvl max y.lvl max cs.fold(0)(_.map(_.lvl).max)
  def or(k: SubOr): SubOr = cs match
    case N => SubOr(x, y, S(Ls(k)))
    case S(cs) => SubOr(x, y, S(cs.map(_.or(k))))

class InfVarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type -> Opt[Ls[SubOr]]] = Nil

trait KCtx(using val prim: PrimCtx):
  def subArg(x: TypeArg, y: TypeArg): Ls[SubOr] =
    SubOr(x.posPart,y.posPart) :: SubOr(y.negPart,x.negPart) :: Nil
  def constrain(c: SubOr)(using CCtx, TL, Raise) = c match
    case SubOr(x,y,N) => ConstraintSolver.constrain(x,y)(using this)
    case SubOr(x,y,S(Nil)) =>
    case SubOr(x,y,S(cs)) => ConstraintSolver.constrain(x,y)(using SuffixCtx(cs, this))
  def asSubcls(x: ClassLikeType, y: ClsTag): Opt[ClassLikeType] =
    if x.sym === y then S(x)
    else if x.sym.isLiteralOf(y) then S(InfCtx.mkTag(y))
    else N

  def addub(s: InfVar, ub: Type, cs: Opt[Ls[SubOr]] = N)(using CCtx, TL, Raise): Unit
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise): Unit
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
    (using CCtx, TL, Raise, Scope): Unit

class InfCtx(
  val lvl: Int,
  val parent: Option[InfCtx],
  val env: HashMap[Symbol, InfType],
  val outRegAcc: Type,
  val xbds: ListBuffer[SubOr]
)(using
    val varSt: HashMap[InfVarSymbol, InfVarState],
    prim: PrimCtx,
    val ctx: Ctx,
    val cfg: Config
) extends KCtx:
  def +=(p: Symbol -> InfType) = env += p
  def get(sym: Symbol): Opt[InfType] = env.get(sym) `orElse` parent.dlof(_.get(sym))(None)
  private[logicsub] def arm: Opt[MatchCtx.Arm] = N
  private[logicsub] def unguarded: InfCtx = this
  def nest: InfCtx = InfCtx(lvl, Some(this), HashMap.empty, outRegAcc, xbds)
  def nestWithOuter(outer: InfVar): InfCtx = InfCtx(lvl + 1, Some(this), HashMap.empty, outRegAcc | outer, ListBuffer.empty)
  def nextLevel: InfCtx = InfCtx(lvl + 1, Some(this), HashMap.empty, outRegAcc, ListBuffer.empty)

  def addub(s: InfVar, ub: Type, cs: Opt[Ls[SubOr]] = N)(using CCtx, TL, Raise) =
    val k = SubOr(s, ub, cs)
    if s.lvl < k.lvl then xbds += k
    else
      val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
      v.upperBounds = ub -> cs :: v.upperBounds
      v.lowerBounds.foreach(lb => constrain(SubOr(lb, ub, cs)))
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) =
   val k = SubOr(lb, s, N)
   if s.lvl < k.lvl then xbds += k
   else
     val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
     v.lowerBounds = lb :: v.lowerBounds
     v.upperBounds.foreach(p => constrain(SubOr(lb, p._1, p._2)))
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
     (using CCtx, TL, Raise, Scope) = 
   given InfCtx = this
   raise(ErrorReport(
       msg"Type error in ${origin.describe}${exp match
           case S(ty) => msg" with expected type ${ty.show}"
           case N => msg""
         }" -> origin.toLoc
       :: parents.reverse.map((lhs, rhs) =>
         val (x, y) = PrettyPrinter.displayBound(lhs, rhs)
         msg"because: cannot constrain  ${x.show}  <:  ${y.show}" -> N
       )
     ))
  // TODO
  def ubs(s: InfVarSymbol): Ls[Type] = varSt.getOrElseUpdate(s, new InfVarState).upperBounds.map(_._1)
  def lbs(s: InfVarSymbol): Ls[Type] = varSt.getOrElseUpdate(s, new InfVarState).lowerBounds
  // def withPrefix(x: Type, y: Type) = ???

class PrimCtx(using st: Elaborator.State, ctx: Elaborator.Ctx, cfg: Config):
  val objSym: ClsTag = ctx.get("Object").get.symbol.get.asTpe.get
  private val intSym = ctx.get("Int").get.symbol.get.asTpe.get
  private val strSym = ctx.get("Str").get.symbol.get.asTpe.get
  private val boolSym = ctx.get("Bool").get.symbol.get.asTpe.get
  val errSym: ClsTag = ctx.get("Error").get.symbol.get.asTpe.get
  val fnSym: ClsTag = ctx.get("Function").get.symbol.get.asTpe.get
  val arrSym: ClsTag = ctx.get("Array").get.symbol.get.asTpe.get
  def litTag(lit: syntax.Literal): LiteralTag =
    val base = lit match
      case _: IntLit => S(intSym)
      case _: StrLit => S(strSym)
      case _: BoolLit => S(boolSym)
      case _: DecLit | _: UnitLit => N
    LiteralTag(LitSymbol(lit), base)

object InfCtx:
  def init(using st: Elaborator.State, ctx: Elaborator.Ctx, tl: TL, cfg: Config): InfCtx =
    given PrimCtx = new PrimCtx
    InfCtx(1, N, HashMap.empty, Bot, ListBuffer.empty)(using HashMap.empty)
  def mkTag(s: ClsTag): ClassLikeType = ClassLikeType(s, Nil, Nil, Nil, N)
  def litTy(lit: Literal)(using ctx: InfCtx): ClassLikeType = mkTag(ctx.prim.litTag(lit))
  def objTy(using ctx: InfCtx): ClassLikeType = mkTag(ctx.prim.objSym)
  def funTy(args: Ls[Type], ret: Type, eff: Type)(using ctx: InfCtx): ClassLikeType =
    val u = tupTy(args)
    val w = Ls(Wildcard.in(u), Wildcard.out(ret), Wildcard.out(eff))
    val i = Ls(true, false, false)
    ClassLikeType(ctx.prim.fnSym, w, Nil, i, S(0))
  // def arrayTy(elem: Type)(using ctx: InfCtx) = ClassLikeType(ctx.prim.arrSym, Ls(elem), Nil, Nil)
  def tupTy(e: Ls[Type])(using ctx: InfCtx): ClassLikeType =
    // val refine = (Tree.Ident("size"): Tree.Ident, litTy(IntLit(e.length))) :: e.zipWithIndex.map:
    //   case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    // ClassLikeType(ctx.prim.arrSym, Ls(e.foldLeft[Type](Bot)(_ | _)), refine, Ls(true), N)
    val refine = e.zipWithIndex.map:
      case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    ClassLikeType(ctx.prim.arrSym, Nil, refine, Nil, N)
  def refinedObj(r: Ls[Tree.Ident -> Type])(using ctx: InfCtx): ClassLikeType =
    ClassLikeType(ctx.prim.objSym, Nil, r, Nil, N)

// A failed subtype check runs its suffix in cont. Both determine whether the solver
// can reuse a visit, including when propagation reconstructs the same fallback.
final case class SuffixCtx(suffix: Ls[SubOr], cont: KCtx)(using PrimCtx) extends KCtx:
  def addub(s: InfVar, ub: Type, cs: Opt[Ls[SubOr]] = N)(using CCtx, TL, Raise) = cs match
    case N => cont.addub(s, ub, S(suffix))
    case S(Nil) =>
    case S(cs) => cont.addub(s, ub, S(cs.flatMap(k => suffix.map(k.or))))
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) = ???
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
      (using CCtx, TL, Raise, Scope) =
    suffix.foreach(cont.constrain)

/** A lexical scope in a conditional arm. Constraints use the joint condition
  * of the arm and keep the level and extruded bounds of their lexical scope. */
private[logicsub] class ThenCtx(
  override val unguarded: InfCtx, enclosing: InfCtx, active: MatchCtx.Arm
) extends InfCtx(unguarded.lvl, S(enclosing), HashMap.empty, unguarded.outRegAcc, unguarded.xbds)
    (using unguarded.varSt, unguarded.prim, unguarded.ctx, unguarded.cfg):
  override def arm = S(active)
  override def nest: ThenCtx = ThenCtx(unguarded, this, active)
  override def nestWithOuter(outer: InfVar): ThenCtx = ThenCtx(unguarded.nestWithOuter(outer), this, active)
  override def nextLevel: ThenCtx = ThenCtx(unguarded.nextLevel, this, active)
  override def constrain(c: SubOr)(using CCtx, TL, Raise) = active.enforce(c, unguarded)
