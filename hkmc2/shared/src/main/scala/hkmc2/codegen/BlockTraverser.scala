package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import os.write.over

// These all work like BlockTransformer and its derivatives, but do not rewrite the block. See BlockTransformer.scala.
// Please use this instead of BlockTransformer for static analysis.

class BlockTraverser(subst: SymbolSubst):
  
  given SymbolSubst = subst
  
  def applySubBlock(b: Block): Unit = applyBlock(b)
  
  def applyBlock(b: Block): Unit = b match
    case _: End => ()
    case Break(lbl) => applyLocal(lbl)
    case Continue(lbl) => applyLocal(lbl)
    case Return(res, implct) => applyResult(res)
    case Throw(exc) => applyResult(exc)
    case Match(scrut, arms, dflt, rst) =>
      val scrut2 = applyPath(scrut)
      arms.foreach: arm =>
        applyCase(arm._1); applySubBlock(arm._2)
      dflt.foreach(applySubBlock)
      applySubBlock(rst)
    case Label(lbl, bod, rst) => applyLocal(lbl); applySubBlock(bod); applySubBlock(rst)
    case Begin(sub, rst) => applySubBlock(sub); applySubBlock(rst)
    case TryBlock(sub, fin, rst) => applySubBlock(sub); applySubBlock(fin); applySubBlock(rst)
    case Assign(l, r, rst) => applyLocal(l); applyResult(r); applySubBlock(rst)
    case b @ AssignField(l, n, r, rst) =>
      applyPath(l); applyResult(r); applySubBlock(rst); b.symbol.foreach(_.subst)
    case Define(defn, rst) => applyDefn(defn); applySubBlock(rst)
    case HandleBlock(l, res, par, args, cls, hdr, bod, rst) =>
      applyLocal(l)
      applyLocal(res)
      applyPath(par)
      args.foreach(applyPath)
      hdr.foreach(applyHandler)
      applySubBlock(bod)
      applySubBlock(rst)
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      applyPath(lhs)
      applyResult(rhs)
      applyPath(fld)
      applySubBlock(rest)
  
  def applyResult(r: Result): Unit = r match
    case r @ Call(fun, args) => applyPath(fun); args.foreach(applyArg)
    case Instantiate(cls, args) =>; applyPath(cls); args.foreach(applyPath)
    case p: Path => applyPath(p)
  
  def applyPath(p: Path): Unit = p match
    case DynSelect(qual, fld, arrayIdx) =>
      applyPath(qual); applyPath(fld)
    case p @ Select(qual, name) =>
      applyPath(qual); p.symbol.foreach(_.subst)
    case v: Value => applyValue(v)
  
  def applyValue(v: Value): Unit = v match
    case Value.Ref(l) => l.subst
    case Value.This(sym) => sym.subst
    case Value.Lit(lit) => ()
    case v @ Value.Lam(params, body) => applyLam(v)
    case Value.Arr(elems) => elems.foreach(applyArg)
    case Value.Rcd(fields) => fields.foreach:
      case RcdArg(idx, value) => idx.foreach(applyPath); applyPath(value)
  
  def applyLocal(sym: Local): Unit = sym.subst
  
  def applyFunDefn(fun: FunDefn): Unit =
    fun.owner.foreach(_.subst)
    fun.sym.subst
    fun.params.foreach(applyParamList)
    applySubBlock(fun.body)
  
  def applyDefn(defn: Defn): Unit = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case ValDefn(owner, k, sym, rhs) => owner.foreach(_.subst); sym.subst; applyPath(rhs)
    case ClsLikeDefn(own, isym, sym, k, paramsOpt, auxParams, parentPath, methods, 
      privateFields, publicFields, preCtor, ctor) =>
      own.foreach(_.subst)
      isym.subst
      sym.subst
      paramsOpt.foreach(applyParamList)
      auxParams.foreach(applyParamList)
      parentPath.foreach(applyPath)
      methods.foreach(applyFunDefn)
      privateFields.foreach(_.subst)
      publicFields.foreach(applyTermDefinition)
      applySubBlock(preCtor)
      applySubBlock(ctor)
  
  def applyArg(arg: Arg): Unit =
    applyPath(arg.value)
  
  def applyParamList(pl: ParamList): Unit =
    pl.params.foreach(_.sym.subst)
    pl.restParam.foreach(_.sym.subst)
  
  def applyCase(cse: Case): Unit = cse match
    case Case.Lit(lit) => ()
    case Case.Cls(cls, path) =>
      cls.subst
      applyPath(path)
    case Case.Tup(len, inf) => ()
  
  def applyHandler(hdr: Handler): Unit =
    hdr.sym.subst
    hdr.resumeSym.subst
    hdr.params.foreach(applyParamList)
    applySubBlock(hdr.body)
  
  def applyLam(lam: Value.Lam): Unit =
    applyParamList(lam.params)
    applySubBlock(lam.body)
  
  def applyTermDefinition(td: TermDefinition): Unit =
    td.owner.foreach(_.subst)
    td.sym.subst
    td.params.foreach(applyParamList)
    td.resSym.subst

class BlockTraverserShallow(subst: SymbolSubst) extends BlockTraverser(subst):
  override def applyLam(lam: Value.Lam) = ()
  override def applyFunDefn(fun: FunDefn): Unit = ()
  override def applyDefn(defn: Defn): Unit = defn match
    case _: FunDefn | _: ClsLikeDefn => ()
    case _: ValDefn => super.applyDefn(defn)
  
  override def applyHandler(hdr: Handler): Unit = ()
  
  override def applyBlock(b: Block): Unit = b match
    case HandleBlock(l, res, par, args, cls, hdr, bod, rst) =>
      applyLocal(l)
      applyLocal(res)
      applyPath(par)
      args.foreach(applyPath)
      cls.subst
      hdr.foreach(applyHandler)
      applySubBlock(rst)
    case _ => super.applyBlock(b)

class BlockDataTraverser(subst: SymbolSubst) extends BlockTraverserShallow(subst):
  override def applySubBlock(b: Block): Unit = ()
