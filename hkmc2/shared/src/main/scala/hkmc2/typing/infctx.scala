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
  def subArg(x: TypeArg, y: TypeArg) =
    SubOr(x.posPart,y.posPart) :: SubOr(y.negPart,x.negPart) :: Nil
  def constrain(c: SubOr)(using CCtx, TL, Raise) = c match
    case SubOr(x,y,N) => ConstraintSolver.constrain(x,y)(using this)
    case SubOr(x,y,S(Nil)) =>
    case SubOr(x,y,S(cs)) => ConstraintSolver.constrain(x,y)(using SuffixCtx(cs, this))
  def asSubcls(x: ClassLikeType, y: ClsTag) =
    if x.sym === y then S(x)
    else x.sym match
      case LitSymbol(_: IntLit) if prim.intSym === y => S(ClassLikeType(y, Nil, Nil, Nil, N))
      case LitSymbol(_: StrLit) if prim.strSym === y => S(ClassLikeType(y, Nil, Nil, Nil, N))
      case LitSymbol(_: BoolLit) if prim.boolSym === y => S(ClassLikeType(y, Nil, Nil, Nil, N))
      case _ => N

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
  def get(sym: Symbol): Option[InfType] = env.get(sym) `orElse` parent.dlof(_.get(sym))(None)
  def nest = InfCtx(lvl, Some(this), HashMap.empty, outRegAcc, xbds)
  def nestWithOuter(outer: InfVar) = InfCtx(lvl + 1, Some(this), HashMap.empty, outRegAcc | outer, ListBuffer.empty)
  def nextLevel = InfCtx(lvl + 1, Some(this), HashMap.empty, outRegAcc, ListBuffer.empty)

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
       :: parents.reverse.map(p =>
         msg"because: cannot constrain  ${p._1.show}  <:  ${p._2.show}" -> N
       )
     ))
  // TODO
  def ubs(s: InfVarSymbol) = varSt.getOrElseUpdate(s, new InfVarState).upperBounds.map(_._1)
  def lbs(s: InfVarSymbol) = varSt.getOrElseUpdate(s, new InfVarState).lowerBounds
  // def withPrefix(x: Type, y: Type) = ???
  def thenCtx(env: HashMap[Symbol, InfType], prefix: Ls[SubOr]) =
    ThenCtx(lvl, S(this), env, outRegAcc, xbds, prefix)

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
  def init(using st: Elaborator.State, ctx: Elaborator.Ctx, tl: TL, cfg: Config) =
    given PrimCtx = new PrimCtx
    InfCtx(1, N, HashMap.empty, Bot, ListBuffer.empty)(using HashMap.empty)
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

class SuffixCtx(val suffix: Ls[SubOr], val cont: KCtx)(using PrimCtx) extends KCtx:
  def addub(s: InfVar, ub: Type, cs: Opt[Ls[SubOr]] = N)(using CCtx, TL, Raise) = cs match
    case N => cont.addub(s, ub, S(suffix))
    case S(Nil) =>
    case S(cs) => cont.addub(s, ub, S(cs.flatMap(k => suffix.map(k.or))))
  def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) = ???
  def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
      (using CCtx, TL, Raise, Scope) =
    suffix.foreach(cont.constrain)

class ThenCtx(
  lvl: Int, parent: Option[InfCtx],
  env: HashMap[Symbol, InfType], outRegAcc: Type,
  xbds: ListBuffer[SubOr], prefix: Ls[SubOr]
)(using HashMap[InfVarSymbol, InfVarState], PrimCtx, Ctx, Config)
extends InfCtx(lvl, parent, env, outRegAcc, xbds):
  override def nest = ThenCtx(lvl, Some(this), HashMap.empty, outRegAcc, xbds, prefix)
  override def nestWithOuter(outer: InfVar) =
    ThenCtx(lvl + 1, Some(this), HashMap.empty, outRegAcc | outer, ListBuffer.empty, prefix)
  override def nextLevel =
    ThenCtx(lvl + 1, Some(this), HashMap.empty, outRegAcc, ListBuffer.empty, prefix)
  // override def addub(s: InfVar, ub: Type, cs: Opt[Ls[SubOr]] = N)(using CCtx, TL, Raise) =
  //   cont.addub(s,ub,cs)
  // override def addlb(lb: Type, s: InfVar)(using CCtx, TL, Raise) = cont.addlb(lb,s)
  // override def err(parents: Ls[(Type, Type)], origin: Term, exp: Opt[InfType])
  //   (using CCtx, TL, Raise, Scope) = cont.err(parents, origin, exp)
  override def constrain(c: SubOr)(using CCtx, TL, Raise) =
   prefix.foreach(k => parent.get.constrain(k.or(c)))


class MatchCtx(
  val prefix: Opt[MatchCtx],
  val refine: Ls[Ls[Ref -> Type]],
  val svt: HashMap[Ref, InfVar -> Type]
):
  def end = if prefix.isEmpty then ???
  def pm(s: Ref, t: => Type, cp: FlatPattern.ClassLike)
      (using ctx: InfCtx, scope: Scope, st: Elaborator.State) =
    val sym = cp.constructor.symbol.get.asCls.get
    val params = sym.defn.get.tparams
    val patt = ClassLikeType(sym, params.map(_ => Wildcard.empty), Nil, params.map(_ => false), N) // TODO
    val (sv, st) = svt.get(s) match
      case N =>
        val vsym = new TempSymbol(S(s), erasedType = N, s.sym.nme)
        val v = InfVar(ctx.lvl, InfVarSymbol(vsym), false)
        svt += s -> (v , t)
        (v, t)
      case S(v, t) => (v, t)
    val nr = refine.map(s -> patt :: _)
    MatchCtx(S(this), nr, svt)
  def el = MatchCtx(prefix.get.prefix, pneg, svt)
  def thenCtx(using ctx: InfCtx)(using CCtx, TL, Raise): InfCtx =
    val c = prefix match
      case N => ctx
      case S(p) => p.thenCtx
    if refine.contains(Nil) then c
    else
      val p = refine.map: r =>
        val m = r.groupMapReduce(_._1)(_._2)(_&_)
        val ss = r.keys.distinct.toList
        ss.map(s => SubOr(svt(s)._2, ~m(s))).reduceRight(_.or(_))
      val tctx = c.thenCtx(env, p)
      refine.foreach: r =>
        val m = r.groupMapReduce(_._1)(_._2)(_&_)
        r.keys.distinct.foreach: s =>
          val (v, t) = svt(s)
          tctx.constrain(SubOr(m(s) & t, v))
      tctx
  def env: HashMap[Symbol, InfType] =
    val ss = refine.flatMap(_.keys).distinct
    // if refine.length == 1
    HashMap.from(ss.map(s => s.sym -> svt(s)._1))
  def cond(r: Ls[Ref -> Type]): SubOr =
    val m = r.groupMapReduce(_._1)(_._2)(_&_)
    r.keys.distinct.map(s => SubOr(svt(s)._2, ~m(s))).reduceRight(_.or(_))
  def pneg: Ls[Ls[Ref -> Type]] =
    refine.foldRight(Ls(Nil)): (r, ps) =>
      ps.flatMap(p => r.map((s, t) => (s, ~t) :: p))

object MatchCtx:
  def init: MatchCtx = MatchCtx(N, Ls(Nil), HashMap.empty)
