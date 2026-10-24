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

final case class K(x: Type, y: Type, cs: Opt[Ls[K]]):
  def lvl: Int = x.lvl max y.lvl max cs.fold(0)(_.map(_.lvl).max)

class InfVarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type -> Opt[Ls[K]]] = Nil

trait KCtx(using val prim: PrimCtx):
  def sub(x: Type, y: Type): K = K(x,y,N)
  def subArg(x: TypeArg, y: TypeArg): Ls[K] =
    sub(x.posPart,y.posPart) :: sub(y.negPart,x.negPart) :: Nil
  def or(x: K, y: K): K = (x,y) match
    case (K(a, b, N), y) => K(a, b, S(Ls(y)))
    case (K(a, b, S(cs)), y) => K(a, b, S(cs.map(or(_,y))))
  def constrain(c: K)(using CCtx, TL, Raise): Unit = c match
    case K(x,y,N) => ConstraintSolver.constrain(x,y)(using this)
    case K(x,y,S(Nil)) =>
    case K(x,y,S(cs)) => ConstraintSolver.constrain(x,y)(using SuffixCtx(cs, this))
  def asSubcls(x: ClassLikeType, y: ClsTag) =
    if x.sym === y then S(x)
    else x.sym match
      case LitSymbol(_: IntLit) if prim.intSym === y => S(ClassLikeType(y, Nil, Nil, Nil, N))
      case LitSymbol(_: StrLit) if prim.strSym === y => S(ClassLikeType(y, Nil, Nil, Nil, N))
      case LitSymbol(_: BoolLit) if prim.boolSym === y => S(ClassLikeType(y, Nil, Nil, Nil, N))
      case _ => N

  def addub(s: InfVar, ub: Type, cs: Opt[Ls[K]] = N)(using CCtx, TL, Raise): Unit
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise): Unit
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
    (using CCtx, TL, Raise, Scope): Unit

final case class InfCtx(
  lvl: Int,
  parent: Option[InfCtx],
  env: HashMap[Symbol, InfType],
  outRegAcc: Type,
  prefix: Opt[Ls[K]] = N
)(using
    val varSt: HashMap[InfVarSymbol, InfVarState],
    val xbds: ListBuffer[K],
    prim: PrimCtx,
    val ctx: Ctx,
    val cfg: Config
) extends KCtx:
  def +=(p: Symbol -> InfType) = env += p
  def get(sym: Symbol): Option[InfType] = env.get(sym) `orElse` parent.dlof(_.get(sym))(None)
  def nest: InfCtx = copy(parent = Some(this), env = HashMap.empty)
  def nestWithOuter(outer: InfVar): InfCtx = copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty, outRegAcc = outRegAcc | outer)
  def nextLevel: InfCtx= copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty)

  def addub(s: InfVar, ub: Type, cs: Opt[Ls[K]] = N)(using CCtx, TL, Raise) =
    val k = K(s, ub, cs)
    if s.lvl < k.lvl then xbds += k
    else
      val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
      v.upperBounds = ub -> cs :: v.upperBounds
      v.lowerBounds.foreach(lb => constrain(sub(lb, ub)))
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) =
   val k = K(lb, s, N)
   if s.lvl < k.lvl then xbds += k
   else
     val v = varSt.getOrElseUpdate(s.sym, new InfVarState)
     v.lowerBounds = lb :: v.lowerBounds
     v.upperBounds.foreach(p => constrain(K(lb, p._1, p._2)))
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
     (using CCtx, TL, Raise, Scope) = 
   given InfCtx = this
   raise(ErrorReport(
       msg"Type error in ${origin.describe}${exp match
           case S(ty) => msg" with expected type ${ty.show}"
           case N => msg""
         }" -> origin.toLoc
       :: parents.reverse.map(p =>
         msg"because: cannot constrain  ${p._1.show}  <:  ${p._2.show}" -> N
       )
     ))
  // TODO
  def ubs(s: InfVarSymbol): Ls[Type] = varSt.getOrElseUpdate(s, new InfVarState).upperBounds.map(_._1)
  def lbs(s: InfVarSymbol): Ls[Type] = varSt.getOrElseUpdate(s, new InfVarState).lowerBounds
  // def withPrefix(x: Type, y: Type) = ???
  override def constrain(c: K)(using CCtx, TL, Raise) = prefix match
    case N => super.constrain(c)
    case S(Nil) =>
    case S(cs) => cs.foreach(k => super.constrain(or(k,c)))

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
    InfCtx(1, N, HashMap.empty, Bot)(using HashMap.empty, ListBuffer.empty)
  def mkTag(s: ClsTag) = ClassLikeType(s, Nil, Nil, Nil, N)
  def litTy(lit: Literal)(using ctx: InfCtx) = mkTag(ctx.prim.litSym(lit))
  def objTy(using ctx: InfCtx) = mkTag(ctx.prim.objSym)
  def funTy(args: Ls[Type], ret: Type, eff: Type)(using ctx: InfCtx) =
    val u = tupTy(args)
    val w = Ls(Wildcard.in(u), Wildcard.out(ret), Wildcard.out(eff))
    val i = Ls(true, false, false)
    ClassLikeType(ctx.prim.fnSym, w, Nil, i, S(0))
  // def arrayTy(elem: Type)(using ctx: InfCtx) = ClassLikeType(ctx.prim.arrSym, Ls(elem), Nil, Nil)
  def tupTy(e: Ls[Type])(using ctx: InfCtx) =
    // val refine = (Tree.Ident("size"): Tree.Ident, litTy(IntLit(e.length))) :: e.zipWithIndex.map:
    //   case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    // ClassLikeType(ctx.prim.arrSym, Ls(e.foldLeft[Type](Bot)(_ | _)), refine, Ls(true), N)
    val refine = e.zipWithIndex.map:
      case (elemTy, idx) => (Tree.Ident(idx.toString): Tree.Ident, elemTy)
    ClassLikeType(ctx.prim.arrSym, Nil, refine, Nil, N)
  def refinedObj(r: Ls[Tree.Ident -> Type])(using ctx: InfCtx) =
    ClassLikeType(ctx.prim.objSym, Nil, r, Nil, N)

class SuffixCtx(val suffix: Ls[K], val cont: KCtx)(using PrimCtx) extends KCtx:
  def addub(s: InfVar, ub: Type, cs: Opt[Ls[K]] = N)(using CCtx, TL, Raise) = cs match
    case N => cont.addub(s, ub, S(suffix))
    case S(Nil) =>
    case S(cs) => cont.addub(s, ub, S(cs.flatMap(k => suffix.map(or(k,_)))))
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) = ???
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
      (using CCtx, TL, Raise, Scope) =
    suffix.foreach(cont.constrain)

class MkPrefix(using PrimCtx) extends KCtx:
  var r = Opt(ListBuffer.empty[K])
  def addub(s: InfVar, ub: Type, cs: Opt[Ls[K]] = N)(using CCtx, TL, Raise) =
    r.foreach(_ += K(s, ub, cs))
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) = ???
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
      (using CCtx, TL, Raise, Scope) =
    r = N
  def apply(x: Type, y: Type)(using CCtx, TL, Raise): Opt[Ls[K]] =
    constrain(sub(x,y))
    r.map(_.toList)
