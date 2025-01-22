package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import os.write.over


// Default implementation: nothing is transformed
class BlockTransformer(subst: SymbolSubst):
  
  given SymbolSubst = subst
  
  def applyBlock(b: Block): Block = b match
    case _: End => b
    case Break(lbl) =>
      val lbl2 = applyLocal(lbl)
      if lbl2 is lbl then b else Break(lbl2)
    case Continue(lbl) =>
      val lbl2 = applyLocal(lbl)
      if lbl2 is lbl then b else Continue(lbl2)
    case Return(res, implct) =>
      applyResult2(res): res2 =>
        if res2 is res then b else Return(res2, implct)
    case Throw(exc) =>
      applyResult2(exc): exc2 =>
        if exc2 is exc then b else Throw(exc2)
    case HandleBlockReturn(res) =>
      applyResult2(res): res2 =>
        if res2 is res then b else HandleBlockReturn(res2)
    case Match(scrut, arms, dflt, rst) =>
      val scrut2 = applyPath(scrut)
      val arms2 = arms.mapConserve: arm =>
        val cse2 = applyCase(arm._1)
        val blk2 = applyBlock(arm._2)
        if (cse2 is arm._1) && (blk2 is arm._2) then arm else (cse2, blk2)
      val dflt2 = dflt.mapConserve(applyBlock)
      val rst2 = applyBlock(rst)
      if (scrut2 is scrut) &&
          (arms2 is arms) &&
          (dflt2 is dflt) && (rst2 is rst)
        then b else Match(scrut2, arms2, dflt2, rst2)
    case Label(lbl, bod, rst) =>
      val lbl2 = applyLocal(lbl)
      val bod2 = applyBlock(bod)
      val rst2 = applyBlock(rst)
      if (lbl2 is lbl) && (bod2 is bod) && (rst2 is rst) then b else Label(lbl2, bod2, rst2)
    case Begin(sub, rst) =>
      val sub2 = applyBlock(sub)
      val rst2 = applyBlock(rst)
      if (sub2 is sub) && (rst2 is rst) then b else Begin(sub2, rst2)
    case TryBlock(sub, fin, rst) =>
      val sub2 = applyBlock(sub)
      val fin2 = applyBlock(fin)
      val rst2 = applyBlock(rst)
      if (sub2 is sub) && (fin2 is fin) && (rst2 is rst) then b else TryBlock(sub2, fin2, rst2)
    case Assign(l, r, rst) =>
      applyResult2(r): r2 =>
        val l2 = applyLocal(l)
        val rst2 = applyBlock(rst)
        if (l2 is l) && (r2 is r) && (rst2 is rst) then b else Assign(l2, r2, rst2)
    case b @ AssignField(l, n, r, rst) =>
      applyResult2(r): r2 =>
        val l2 = applyPath(l)
        val rst2 = applyBlock(rst)
        val sym = b.symbol.mapConserve(_.subst)
        if (l2 is l) && (r2 is r) && (rst2 is rst) && (sym is b.symbol)
          then b else AssignField(l2, n, r2, rst2)(sym)
    case Define(defn, rst) =>
      val defn2 = applyDefn(defn)
      val rst2 = applyBlock(rst)
      if (defn2 is defn) && (rst2 is rst) then b else Define(defn2, rst2)
    case HandleBlock(l, res, par, cls, hdr, bod, rst) =>
      val l2 = applyLocal(l)
      val res2 = applyLocal(res)
      val par2 = applyPath(par)
      val cls2 = cls.subst
      val hdr2 = hdr.mapConserve(applyHandler)
      val bod2 = applyBlock(bod)
      val rst2 = applyBlock(rst)
      if (l2 is l) && (res2 is res) && (par2 is par) && (cls2 is cls) &&
          (hdr2 is hdr) && (bod2 is bod) && (rst2 is rst)
        then b else HandleBlock(l2, res2, par2, cls2, hdr2, bod2, rst2)
  
  def applyResult2(r: Result)(k: Result => Block): Block = k(applyResult(r))

  def applyResult(r: Result): Result = r match
    case r @ Call(fun, args) =>
      val fun2 = applyPath(fun)
      val args2 = args.mapConserve(applyArg)
      if (fun2 is fun) && (args2 is args) then r else Call(fun2, args2)(r.isMlsFun)
    case Instantiate(cls, args) =>
      val cls2 = applyPath(cls)
      val args2 = args.mapConserve(applyPath)
      if (cls2 is cls) && (args2 is args) then r else Instantiate(cls2, args2)
    case p: Path => applyPath(p)
  
  def applyPath(p: Path): Path = p match
    case p @ Select(qual, name) =>
      val qual2 = applyPath(qual)
      val sym2 = p.symbol.mapConserve(_.subst)
      if (qual2 is qual) && (sym2 is p.symbol) then p else Select(qual2, name)(sym2)
    case v: Value => applyValue(v)
  
  def applyValue(v: Value): Value = v match
    case Value.Ref(l) =>
      val l2 = l.subst
      if (l2 is l) then v else Value.Ref(l2)
    case Value.This(sym) =>
      val sym2 = sym.subst
      if (sym2 is sym) then v else Value.This(sym2)
    case Value.Lit(lit) => v
    case v @ Value.Lam(params, body) => applyLam(v)
    case Value.Arr(elems) =>
      val elems2 = elems.mapConserve(applyArg)
      if (elems2 is elems) then v else Value.Arr(elems2)
  
  def applyLocal(sym: Local): Local = sym.subst
  
  def applyFunDefn(fun: FunDefn): FunDefn =
    val own2 = fun.owner.mapConserve(_.subst)
    val sym2 = fun.sym.subst
    val params2 = fun.params.mapConserve(applyParamList)
    val body2 = applyBlock(fun.body)
    if (own2 is fun.owner) && (sym2 is fun.sym) && (params2 is fun.params) && (body2 is fun.body)
      then fun else FunDefn(own2, sym2, params2, body2)
  
  def applyDefn(defn: Defn): Defn = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case ValDefn(owner, k, sym, rhs) =>
      val owner2 = owner.mapConserve(_.subst)
      val sym2 = sym.subst
      val rhs2 = applyPath(rhs)
      if (owner2 is owner) && (sym2 is sym) && (rhs2 is rhs)
        then defn else ValDefn(owner2, k, sym2, rhs2)
    case ClsLikeDefn(own, isym, sym, k, paramsOpt, parentPath, methods, privateFields, publicFields, preCtor, ctor) =>
      val own2 = own.mapConserve(_.subst)
      val isym2 = isym.subst
      val sym2 = sym.subst
      val paramsOpt2 = paramsOpt.mapConserve(applyParamList)
      val parentPath2 = parentPath.mapConserve(applyPath)
      val methods2 = methods.mapConserve(applyFunDefn)
      val privateFields2 = privateFields.mapConserve(_.subst)
      val publicFields2 = publicFields.mapConserve(applyTermDefinition)
      val preCtor2 = applyBlock(preCtor)
      val ctor2 = applyBlock(ctor)
      if (own2 is own) && (isym2 is isym) && (sym2 is sym) &&
          (paramsOpt2 is paramsOpt) &&
          (parentPath2 is parentPath) &&
          (methods2 is methods) &&
          (privateFields2 is privateFields) &&
          (publicFields2 is publicFields) &&
          (preCtor2 is preCtor) && (ctor2 is ctor)
        then defn else ClsLikeDefn(own, isym2, sym2, k, paramsOpt, parentPath2, methods2, privateFields2, publicFields2, preCtor2, ctor2)
  
  def applyArg(arg: Arg): Arg =
    val val2 = applyPath(arg.value)
    if val2 is arg.value then arg else Arg(arg.spread, val2)
  
  def applyParamList(pl: ParamList): ParamList =
    def applyParam(p: Param): Param =
      val sym2 = p.sym.subst
      if sym2 is p.sym then p else Param(p.flags, sym2, p.sign)
    val params2 = pl.params.mapConserve(applyParam)
    val rest2 = pl.restParam.mapConserve(applyParam)
    if (params2 is pl.params) && (rest2 is pl.restParam)
      then pl else ParamList(pl.flags, params2, rest2)
  
  def applyCase(cse: Case): Case = cse match
    case Case.Lit(lit) => cse
    case Case.Cls(cls, path) =>
      val cls2 = cls.subst
      val path2 = applyPath(path)
      if (cls2 is cls) && (path2 is path) then cse else Case.Cls(cls2, path2)
    case Case.Tup(len, inf) => cse
  
  def applyHandler(hdr: Handler): Handler =
    val sym2 = hdr.sym.subst
    val resumeSym2 = hdr.resumeSym.subst
    val params2 = hdr.params.mapConserve(applyParamList)
    val body2 = applyBlock(hdr.body)
    if (sym2 is hdr.sym) && (resumeSym2 is hdr.resumeSym) &&
        (params2 is hdr.params) && (body2 is hdr.body)
      then hdr else Handler(sym2, resumeSym2, params2, body2)
  
  def applyLam(lam: Value.Lam): Value.Lam =
    val params2 = applyParamList(lam.params)
    val body2 = applyBlock(lam.body)
    if (params2 is lam.params) && (body2 is lam.body) then lam else Value.Lam(params2, body2)
  
  def applyTermDefinition(td: TermDefinition): TermDefinition =
    val owner2 = td.owner.mapConserve(_.subst)
    val sym2 = td.sym.subst
    val params2 = td.params.mapConserve(applyParamList)
    val resSym2 = td.resSym.subst
    if (owner2 is td.owner) && (sym2 is td.sym) &&
        (params2 is td.params) && (resSym2 is td.resSym)
      then td else TermDefinition(owner2, td.k, sym2, params2, td.sign, td.body, resSym2, td.flags, td.annotations)

class BlockTransformerShallow(subst: SymbolSubst) extends BlockTransformer(subst):
  override def applyLam(lam: Value.Lam) = lam
  override def applyFunDefn(fun: FunDefn): FunDefn = fun
  override def applyDefn(defn: Defn): Defn = defn match
    case _: FunDefn | _: ClsLikeDefn => defn
    case _: ValDefn => super.applyDefn(defn)
  
  override def applyHandler(hdr: Handler): Handler = hdr
  
  override def applyBlock(b: Block): Block = b match
    case HandleBlock(l, res, par, cls, hdr, bod, rst) =>
      val l2 = applyLocal(l)
      val res2 = applyLocal(res)
      val par2 = applyPath(par)
      val cls2 = cls.subst
      val hdr2 = hdr.mapConserve(applyHandler)
      val rst2 = applyBlock(rst)
      if (l2 is l) && (res2 is res) && (par2 is par) && (cls2 is cls) &&
          (hdr2 is hdr) && (rst2 is rst)
        then b else HandleBlock(l2, res2, par2, cls2, hdr2, bod, rst2)
    case _ => super.applyBlock(b)

