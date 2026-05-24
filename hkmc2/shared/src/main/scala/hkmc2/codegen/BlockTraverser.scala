package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*


// These all work like BlockTransformer and its derivatives, but do not rewrite the block. See BlockTransformer.scala.
// Please use this instead of BlockTransformer for static analysis.

class BlockTraverser:
  
  extension (sym: Symbol)
    inline def traverse: Unit = applySymbol(sym)
  
  
  def applyProgram(prog: Program): Unit =
    prog.imports.foreach(applyImport)
    applyBlock(prog.main)
  
  def applyImport(imp: Local -> Str): Unit =
    applyLocal(imp._1)
  
  
  def applySymbol(sym: Symbol): Unit = ()
  
  def applySubBlock(b: Block): Unit = applyBlock(b)
  
  def applyBlock(b: Block): Unit = b match
    case _: End | _: Unreachable => ()
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
    case Label(lbl, loop, bod, rst) => applyLocal(lbl); applySubBlock(bod); applySubBlock(rst)
    case Begin(sub, rst) => applySubBlock(sub); applySubBlock(rst)
    case TryBlock(sub, fin, rst) => applySubBlock(sub); applySubBlock(fin); applySubBlock(rst)
    case Assign(l, r, rst) => applyLocal(l); applyResult(r); applySubBlock(rst)
    case b @ AssignField(l, n, r, rst) =>
      applyPath(l); applyResult(r); applySubBlock(rst); b.symbol.foreach(_.traverse)
    case Define(defn, rst) => applyDefn(defn); applySubBlock(rst)
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      applyPath(lhs)
      applyResult(rhs)
      applyPath(fld)
      applySubBlock(rest)
    case Scoped(_, body) => applySubBlock(body)
  
  def applyResult(r: Result): Unit = r match
    case r @ Call(fun, argss) => applyPath(fun); argss.foreach(_.foreach(applyArg))
    case Instantiate(mut, cls, argss) => applyPath(cls); argss.foreach(_.foreach(applyArg))
    case l @ Lambda(params, body) => applyLam(l)
    case Tuple(mut, elems) => elems.foreach(applyArg)
    case Record(mut, fields) => fields.foreach:
      case RcdArg(idx, value) => idx.foreach(applyPath); applyPath(value)
    case p: Path => applyPath(p)
  
  def applyPath(p: Path): Unit = p match
    case DynSelect(qual, fld, arrayIdx) =>
      applyPath(qual); applyPath(fld)
    case p @ Select(qual, name) =>
      applyPath(qual); p.symbol.foreach(_.traverse)
    case v: Value => applyValue(v)
  
  def applyValue(v: Value): Unit = v match
    case Value.Ref(l, disamb) =>
      l.traverse
      disamb.foreach(_.traverse)
    case Value.This(sym) => sym.traverse
    case Value.Lit(lit) => ()
  
  def applyLocal(sym: Local): Unit = sym.traverse
  
  def applyFunDefn(fun: FunDefn): Unit =
    fun.owner.foreach(_.traverse)
    fun.sym.traverse
    fun.dSym.traverse
    fun.params.foreach(applyParamList)
    applySubBlock(fun.body)
  
  def applyValDefn(defn: ValDefn): Unit =
    val ValDefn(tsym, sym, rhs) = defn
    tsym.owner.foreach(_.traverse); sym.traverse; applyPath(rhs)
  
  def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
    val ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
      privateFields, publicFields, preCtor, ctor, mod, bufferable) = defn
    own.foreach(_.traverse)
    isym.traverse
    sym.traverse
    ctorSym.foreach(_.traverse)
    paramsOpt.foreach(applyParamList)
    auxParams.foreach(applyParamList)
    parentPath.foreach(applyPath)
    methods.foreach(applyFunDefn)
    privateFields.foreach(_.traverse)
    publicFields.foreach: f =>
      f._1.traverse; f._2.traverse
    applySubBlock(preCtor)
    applySubBlock(ctor)
    mod.foreach(applyCompanionModule)
  
  def applyDefn(defn: Defn): Unit = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case defn: ValDefn => applyValDefn(defn)
    case defn: ClsLikeDefn => applyClsLikeDefn(defn)
  
  def applyCompanionModule(b: ClsLikeBody): Unit =
    b.isym.traverse
    b.methods.foreach(applyFunDefn)
    b.privateFields.foreach(_.traverse)
    b.publicFields.foreach: f =>
      f._1.traverse; f._2.traverse
    applySubBlock(b.ctor)

  def applyArg(arg: Arg): Unit =
    applyPath(arg.value)
  
  def applyParamList(pl: ParamList): Unit =
    pl.params.foreach(_.sym.traverse)
    pl.restParam.foreach(_.sym.traverse)
  
  def applyCase(cse: Case): Unit = cse match
    case Case.Lit(lit) => ()
    case Case.Cls(cls, path) =>
      cls.traverse
      applyPath(path)
    case Case.Tup(len, inf) => ()
    case Case.Field(_, _) => ()
  
  def applyHandler(hdr: Handler): Unit =
    hdr.sym.traverse
    hdr.resumeSym.traverse
    hdr.params.foreach(applyParamList)
    applySubBlock(hdr.body)
  
  def applyLam(lam: Lambda): Unit =
    applyParamList(lam.params)
    applySubBlock(lam.body)
  
class BlockTraverserShallow extends BlockTraverser:
  override def applyLam(lam: Lambda) = ()
  override def applyFunDefn(fun: FunDefn): Unit = ()
  override def applyDefn(defn: Defn): Unit = defn match
    case _: FunDefn | _: ClsLikeDefn => ()
    case _: ValDefn => super.applyDefn(defn)
  
  override def applyHandler(hdr: Handler): Unit = ()

class BlockDataTraverser extends BlockTraverserShallow:
  override def applySubBlock(b: Block): Unit = ()

