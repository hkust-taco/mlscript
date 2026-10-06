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
  val suffix: Ls[K]
)(using
    val prim: PrimCtx,
    val ctx: Ctx,
    val typeNames: HashSet[Str],
    val symbolCache: HashMap[Str, TypeSymbol],
    val varSt: HashMap[InfVarSymbol, InfVarState]
):
  def +=(p: Symbol -> InfType): Unit = env += p
  def get(sym: Symbol): Option[InfType] = env.get(sym) `orElse` parent.dlof(_.get(sym))(None)
  def getCls(name: Str): TypeSymbol= symbolCache.getOrElseUpdate(name,
    ctx.get(name).get.symbol.get.asTpe.get)
  def nest: InfCtx = copy(parent = Some(this), env = HashMap.empty)
  def nestWithOuter(outer: InfVar): InfCtx= copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty, outRegAcc = outRegAcc | outer)
  def nextLevel: InfCtx= copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty)

  def withTail(x:Ls[K]) = copy(parent = S(this), suffix = x)
  // def freshVar(origin: Symbol | Term, hint: Str = ""): InfVar

  def sub(x: Type, y: Type): K = K(x,y)
  def subor(x: K, y: K): K = (x,y) match
    case (K(a, b: Type), y) => K(a, DisjOr(b, Ls(y)))
    case (K(a, DisjOr(b, cs)), y) => K(a, DisjOr(b, cs ++ Ls(y)))

  def constrain(solver: ConstraintSolver, c: K)(using CCtx, TL): Unit= c match
    case K(x,y: Type) => solver.constrain(x,y)(using this)
    case K(x,DisjOr(y, cs)) =>
      given InfCtx = withTail(cs)
      solver.constrain(x,y)

  def ubs(s: InfVarSymbol): Ls[Type]= varSt(s).upperBounds
  def lbs(s: InfVarSymbol): Ls[Type]= varSt(s).lowerBounds
  def addub(s: InfVar, ub: Type): Unit=
    val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
    v.upperBounds = ub :: v.upperBounds
  def addlb(lb: Type, s: InfVar): Unit=
    val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
    v.lowerBounds = lb :: v.lowerBounds
  def disjor(p: Type, a: InfVar, cs: Ls[K]): Unit = ???

class PrimCtx(using st: Elaborator.State, ctx: Elaborator.Ctx):
  val objSym = ctx.get("Object").get.symbol.get.asTpe.get
  val intSym = ctx.get("Int").get.symbol.get.asTpe.get
  val strSym = ctx.get("Str").get.symbol.get.asTpe.get
  val errSym = ctx.get("Error").get.symbol.get.asTpe.get
  val fnSym = ctx.get("Function").get.symbol.get.asTpe.get
  def litSym(x: syntax.Literal) = LitSymbol(x)

object InfCtx:
  def init(using st: Elaborator.State, ctx: Elaborator.Ctx, tl: TL): InfCtx =
    val prim = new PrimCtx
    InfCtx(1, N, HashMap.empty, Bot, Nil, Nil)
      (using prim, ctx, HashSet.empty, HashMap.empty, HashMap.empty)
  def mkTag(s: ClsTag) = ClassLikeType(s, Nil, Nil, Nil, Nil)
  def litTy(lit: Literal)(using ctx: InfCtx) = mkTag(ctx.prim.litSym(lit))
  def objTy(using ctx: InfCtx) = mkTag(ctx.prim.objSym)
  def funTy(args: Ls[Type], ret: Type, eff: Type)(using ctx: InfCtx) =
    val args = Ls(Bot, Wildcard.out(ret), Wildcard.out(eff))
    val i = Ls(true, false, false)
    val o = Ls(false, false, false)
    ClassLikeType(ctx.prim.fnSym, args, Nil, i, o)
  def asRefinedObj(t: Ls[Type])(using ctx: InfCtx) =
    val r = t.zipWithIndex.map:
      case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    ClassLikeType(ctx.prim.objSym, Nil, r, Nil, Nil)
  //  def arrayTy(elem: Type)(using ctx: InfCtx) = ClassLikeType(ctx.getCls("Array"), Ls(elem), Nil, Nil)
  //  def tupTy(e: Ls[Type])(using ctx: InfCtx, s: Elaborator.State) =
  //    val refine = (Tree.Ident("size"): Tree.Ident, litTy(IntLit(e.length))) :: e.zipWithIndex.map:
  //      case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
  //    ClassLikeType(ctx.getCls("Array"), Ls(e.foldLeft[Type](Bot)(_ | _)), refine, Nil)
  def refinedObj(r: Ls[Tree.Ident -> Type])(using ctx: InfCtx) =
    ClassLikeType(ctx.prim.objSym, Nil, r, Nil, Nil)