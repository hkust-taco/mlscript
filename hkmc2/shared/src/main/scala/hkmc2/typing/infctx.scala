package hkmc2
package typing
package logicsub

import scala.collection.mutable.{HashSet, HashMap, ListBuffer}
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import utils.*

import Message.MessageContext
import semantics.*, Term.*, ucs.FlatPattern
import Elaborator.Ctx
import syntax.*
import Tree.*
import utils.Scope
import hkmc2.codegen.ErasedType.eraseSign

final case class DisjOr(p: Type, cs: Ls[K])
final case class K(x: Type, y: Type | DisjOr)

class InfVarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil
  var disjsub: Ls[DisjOr] = Nil

final case class InfCtx(
  val lvl: Int,
  val parent: Option[InfCtx],
  val env: HashMap[Symbol, InfType],
  val outRegAcc: Type,
  val prefix: Ls[Ls[Type->Type]],
  val suffix: Ls[K], // TODO mutable
)(using
    val varSt: HashMap[InfVarSymbol, InfVarState],
    val prim: PrimCtx,
    val ctx: Ctx,
    val cfg: Config
):
  def +=(p: Symbol -> InfType): Unit = env += p
  def get(sym: Symbol): Option[InfType] = env.get(sym) `orElse` parent.dlof(_.get(sym))(None)
  def nest: InfCtx = copy(parent = Some(this), env = HashMap.empty)
  def nestWithOuter(outer: InfVar): InfCtx= copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty, outRegAcc = outRegAcc | outer)
  def nextLevel: InfCtx= copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty)

  def withSuffix(x:Ls[K]) = copy(parent = S(this), suffix = x ++ suffix)
  def dropSuffix = copy(suffix = Nil)
  // def freshVar(origin: Symbol | Term, hint: Str = ""): InfVar

  def sub(x: Type, y: Type): K = K(x,y)
  def subArg(x: TypeArg, y: TypeArg): Ls[K] =
    K(x.posPart,y.posPart) :: K(y.negPart,x.negPart) :: Nil
  def subor(x: K, y: K): K = (x,y) match
    case (K(a, b: Type), y) => K(a, DisjOr(b, Ls(y)))
    case (K(a, DisjOr(b, cs)), y) => K(a, DisjOr(b, cs ++ Ls(y)))

  def constrain(c: K)(using CCtx, TL, Raise): Unit = c match
    case K(x,y: Type) => ConstraintSolver.constrain(x,y)(using this)
    case K(x,DisjOr(y, cs)) =>
      given InfCtx = withSuffix(cs)
      ConstraintSolver.constrain(x,y)

  def ubs(s: InfVarSymbol): Ls[Type] = varSt.getOrElseUpdate(s, new InfVarState).upperBounds
  def lbs(s: InfVarSymbol): Ls[Type] = varSt.getOrElseUpdate(s, new InfVarState).lowerBounds
  def addub(s: InfVar, ub: Type)(using CCtx, TL, Raise): Unit =
    if prefix.isEmpty && suffix.isEmpty then
      val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
      v.upperBounds = ub :: v.upperBounds
      v.lowerBounds.foreach(lb => constrain(sub(lb, ub)))
    else ???
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise): Unit =
    if prefix.isEmpty && suffix.isEmpty then
      val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
      v.lowerBounds = lb :: v.lowerBounds
      v.upperBounds.foreach(ub => constrain(sub(lb, ub)))
    else ???
  def disjor(p: Type, a: InfVar, cs: Ls[K]): Unit = ???

  def err(msg: Diagnostic)(using CCtx, Raise, TL): Unit =
    if suffix.isEmpty then raise(msg)
    else
      val nctx = dropSuffix
      suffix.foreach(k => nctx.constrain(k))

  def asSubcls(x: ClassLikeType, y: ClsTag): Opt[ClassLikeType] =
    if x.sym === y then S(x)
    else
      x.sym match
        case lit: LitSymbol =>
          lit.lit match
            case _: IntLit =>
              if prim.intSym === y then S(ClassLikeType(y, Nil, Nil, Nil, N)) else N
            case _: StrLit =>
              if prim.strSym === y then S(ClassLikeType(y, Nil, Nil, Nil, N)) else N
            case _: BoolLit =>
              if prim.boolSym === y then S(ClassLikeType(y, Nil, Nil, Nil, N)) else N
            case _ => N
        case _ => N

class PrimCtx(using st: Elaborator.State, ctx: Elaborator.Ctx, cfg: Config):
  val objSym = ctx.get("Object").get.symbol.get.asTpe.get
  val intSym = ctx.get("Int").get.symbol.get.asTpe.get
  val strSym = ctx.get("Str").get.symbol.get.asTpe.get
  val boolSym = ctx.get("Bool").get.symbol.get.asTpe.get
  val errSym = ctx.get("Error").get.symbol.get.asTpe.get
  val fnSym = ctx.get("Function").get.symbol.get.asTpe.get
  val arrSym = ctx.get("Array").get.symbol.get.asTpe.get
  def litSym(x: syntax.Literal) = LitSymbol(x)

object InfCtx:
  def init(using st: Elaborator.State, ctx: Elaborator.Ctx, tl: TL, cfg: Config): InfCtx =
    given PrimCtx = new PrimCtx
    InfCtx(1, N, HashMap.empty, Bot, Nil, Nil)(using HashMap.empty)
  def mkTag(s: ClsTag) = ClassLikeType(s, Nil, Nil, Nil, N)
  def litTy(lit: Literal)(using ctx: InfCtx) = mkTag(ctx.prim.litSym(lit))
  def objTy(using ctx: InfCtx) = mkTag(ctx.prim.objSym)
  def funTy(args: Ls[Type], ret: Type, eff: Type)(using ctx: InfCtx) =
    val u = tupTy(args)
    val w = Ls(Wildcard.in(u), Wildcard.out(ret), Wildcard.out(eff))
    val i = Ls(true, false, false)
    ClassLikeType(ctx.prim.fnSym, w, Nil, i, S(0))
  def asRefinedObj(t: Ls[Type])(using ctx: InfCtx) =
    val r = t.zipWithIndex.map:
      case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    ClassLikeType(ctx.prim.objSym, Nil, r, Nil, N)
  //  def arrayTy(elem: Type)(using ctx: InfCtx) = ClassLikeType(ctx.getCls("Array"), Ls(elem), Nil, Nil)
  def tupTy(e: Ls[Type])(using ctx: InfCtx) =
    // val refine = (Tree.Ident("size"): Tree.Ident, litTy(IntLit(e.length))) :: e.zipWithIndex.map:
    //   case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    // ClassLikeType(ctx.prim.arrSym, Ls(e.foldLeft[Type](Bot)(_ | _)), refine, Ls(true), N)
    val refine = e.zipWithIndex.map:
      case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    ClassLikeType(ctx.prim.arrSym, Nil, refine, Nil, N)
  def refinedObj(r: Ls[Tree.Ident -> Type])(using ctx: InfCtx) =
    ClassLikeType(ctx.prim.objSym, Nil, r, Nil, N)
