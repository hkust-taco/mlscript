package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import os.write.over


// Default implementation: nothing is transformed
class BlockTransformer(subst: SymbolSubst):
  
  given SymbolSubst = subst
  
  def applySubBlock(b: Block): Block = applyBlock(b)
  
  def applyBlock(b: Block): Block = b match
    case _: End => b
    case Break(lbl) =>
      val lbl2 = applyLocal(lbl)
      if lbl2 is lbl then b else Break(lbl2)
    case Continue(lbl) =>
      val lbl2 = applyLocal(lbl)
      if lbl2 is lbl then b else Continue(lbl2)
    case Return(res, implct) =>
      applyResult(res): res2 =>
        if res2 is res then b else Return(res2, implct)
    case Throw(exc) =>
      applyResult(exc): exc2 =>
        if exc2 is exc then b else Throw(exc2)
    case Match(scrut, arms, dflt, rst) =>
      applyPath(scrut): scrut2 =>
        applyListOf(
          arms,
          (tup, k) =>
            val (cse, blk) = tup
            val blk2 = applySubBlock(blk)
            applyCase(cse): cse2 =>
              if (cse2 is cse) && (blk is blk2) then k(tup) else k(cse2 -> blk2)
        ): arms2 =>
            val dflt2 = dflt.mapConserve(applySubBlock)
            val rst2 = applySubBlock(rst)
            if (scrut2 is scrut) &&
                (arms2 is arms) &&
                (dflt2 is dflt) && (rst2 is rst)
              then b else Match(scrut2, arms2, dflt2, rst2)
    case Label(lbl, bod, rst) =>
      val lbl2 = applyLocal(lbl)
      val bod2 = applySubBlock(bod)
      val rst2 = applySubBlock(rst)
      if (lbl2 is lbl) && (bod2 is bod) && (rst2 is rst) then b else Label(lbl2, bod2, rst2)
    case Begin(sub, rst) =>
      val sub2 = applySubBlock(sub)
      val rst2 = applySubBlock(rst)
      if (sub2 is sub) && (rst2 is rst) then b else Begin(sub2, rst2)
    case TryBlock(sub, fin, rst) =>
      val sub2 = applySubBlock(sub)
      val fin2 = applySubBlock(fin)
      val rst2 = applySubBlock(rst)
      if (sub2 is sub) && (fin2 is fin) && (rst2 is rst) then b else TryBlock(sub2, fin2, rst2)
    case Assign(l, r, rst) =>
      applyResult(r): r2 =>
        val l2 = applyLocal(l)
        val rst2 = applySubBlock(rst)
        if (l2 is l) && (r2 is r) && (rst2 is rst) then b else Assign(l2, r2, rst2)
    case b @ AssignField(l, n, r, rst) =>
      applyResult(r): r2 =>
        applyPath(l): l2 =>
          val rst2 = applySubBlock(rst)
          val sym = b.symbol.mapConserve(_.subst)
          if (l2 is l) && (r2 is r) && (rst2 is rst) && (sym is b.symbol)
            then b else AssignField(l2, n, r2, rst2)(sym)
    case Define(defn, rst) =>
      applyDefn(defn): defn2 =>
        val rst2 = applySubBlock(rst)
        if (defn2 is defn) && (rst2 is rst) then b else Define(defn2, rst2)
    case HandleBlock(l, res, par, args, cls, hdr, bod, rst) =>
      val l2 = applyLocal(l)
      val res2 = applyLocal(res)
      applyPath(par): par2 =>
        applyListOf(args, applyPath(_)(_)): args2 =>
          val cls2 = cls.subst
          val hdr2 = hdr.mapConserve(applyHandler)
          val bod2 = applySubBlock(bod)
          val rst2 = applySubBlock(rst)
          if (l2 is l) && (res2 is res) && (par2 is par) && (args2 is args) &&
              (cls2 is cls) && (hdr2 is hdr) && (bod2 is bod) && (rst2 is rst)
            then b else HandleBlock(l2, res2, par2, args2, cls2, hdr2, bod2, rst2)
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      applyResult(rhs): rhs2 =>
        applyPath(lhs): lhs2 =>
          applyPath(fld): fld2 =>
            val rest2 = applySubBlock(rest)
            if (lhs2 is lhs) && (fld2 is fld) && (rhs2 is rhs) && (rest2 is rest)
            then b
            else AssignDynField(lhs2, fld2, arrayIdx, rhs2, rest2)
  
  def applyRcdArg(rcdArg: RcdArg)(k: RcdArg => Block): Block =
    val RcdArg(idx, p) = rcdArg
    val toBeIdxed = (idx2: Opt[Path]) =>
      applyPath(p): p2 =>
        k(if (p2 is p) && (idx2 is idx) then rcdArg else RcdArg(idx2, p2))
    idx match
      case Some(i) =>
        applyPath(i): i2 =>
          toBeIdxed(if i is i2 then idx else Some(i2))
      case None => toBeIdxed(idx)
  
  def applyRcdArgs(rcdArgs: List[RcdArg])(k: List[RcdArg] => Block): Block =
    applyListOf(rcdArgs, applyRcdArg(_)(_))(k)
  
  def applyArgs(args: List[Arg])(k: List[Arg] => Block): Block =
    applyListOf(args, applyArg(_)(_))(k)
  
  def applyResult(r: Result)(k: Result => Block): Block =
    r match
    case r @ Call(fun, args) =>
      applyPath(fun): fun2 =>
        applyArgs(args): args2 =>
          k(if (fun2 is fun) && (args2 is args) then r else Call(fun2, args2)(r.isMlsFun, r.mayRaiseEffects))
    case Instantiate(mut, cls, args) =>
      applyPath(cls): cls2 =>
        applyArgs(args): args2 =>
          k(if (cls2 is cls) && (args2 is args) then r else Instantiate(mut, cls2, args2))
    case l: Lambda => k(applyLam(l))
    case Tuple(mut, elems) =>
      applyArgs(elems): elems2 =>
        k(if (elems2 is elems) then r else Tuple(mut, elems2))
    case Record(mut, fields) =>
      applyRcdArgs(fields): fields2 =>
        k(if fields2 is fields then r else Record(mut, fields2))
    case p: Path => applyPath(p)(k)  
  
  def applyPath(p: Path)(k: Path => Block): Block = p match
    case DynSelect(qual, fld, arrayIdx) =>
      applyPath(qual): qual2 =>
        applyPath(fld): fld2 =>
          k(if (qual2 is qual) && (fld2 is fld) then p else DynSelect(qual2, fld2, arrayIdx))
    case p @ Select(qual, name) =>
      applyPath(qual): qual2 =>
        val sym2 = p.symbol.mapConserve(_.subst)
        k(if (qual2 is qual) && (sym2 is p.symbol) then p else Select(qual2, name)(sym2))
    case v: Value => applyValue(v)(k)
  
  def applyValue(v: Value)(k: Value => Block) = v match
    case Value.Ref(l) =>
      val l2 = l.subst
      k(if (l2 is l) then v else Value.Ref(l2))
    case Value.This(sym) =>
      val sym2 = sym.subst
      k(if (sym2 is sym) then v else Value.This(sym2))
    case Value.Lit(lit) => k(v)
  
  def applyLocal(sym: Local): Local = sym.subst
  
  def applyFunDefn(fun: FunDefn): FunDefn =
    val own2 = fun.owner.mapConserve(_.subst)
    val sym2 = fun.sym.subst
    val params2 = fun.params.mapConserve(applyParamList)
    val body2 = applySubBlock(fun.body)
    if (own2 is fun.owner) && (sym2 is fun.sym) && (params2 is fun.params) && (body2 is fun.body)
      then fun else FunDefn(own2, sym2, params2, body2)
  
  def applyValDefn(defn: ValDefn)(k: ValDefn => Block): Block =
    val ValDefn(tsym, sym, rhs) = defn
    val tsym2 = tsym.subst
    val sym2 = sym.subst
    applyPath(rhs): rhs2 =>
      if (tsym2 is tsym) && (sym2 is sym) && (rhs2 is rhs)
        then k(defn) else k(ValDefn(tsym2, sym2, rhs2))
  
  def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
    val isym2 = defn.isym.subst
    val methods2 = defn.methods.mapConserve(applyFunDefn)
    val privateFields2 = defn.privateFields.mapConserve(_.subst)
    val publicFields2 = defn.publicFields.mapConserve(f => f._1.subst -> f._2.subst)
    val ctor2 = applySubBlock(defn.ctor)
    if (methods2 is defn.methods) &&
        (privateFields2 is defn.privateFields) &&
        (publicFields2 is defn.publicFields) &&
        (ctor2 is defn.ctor)
      then defn else ClsLikeBody(isym2, methods2, privateFields2, publicFields2, ctor2)
    
  def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
    case defn: FunDefn => k(applyFunDefn(defn))
    case defn: ValDefn => applyValDefn(defn)(k)
    case ClsLikeDefn(own, isym, sym, kind, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, mod)
    =>
      val own2 = own.mapConserve(_.subst)
      val isym2 = isym.subst
      val sym2 = sym.subst
      val paramsOpt2 = paramsOpt.mapConserve(applyParamList)
      val auxParams2 = auxParams.mapConserve(applyParamList)
      val withoutParentPath = (parentPath2: Opt[Path]) =>
        val methods2 = methods.mapConserve(applyFunDefn)
        val privateFields2 = privateFields.mapConserve(_.subst)
        val publicFields2 = publicFields.mapConserve(f => f._1.subst -> f._2.subst)
        val preCtor2 = applySubBlock(preCtor)
        val ctor2 = applySubBlock(ctor)
        val mod2 = mod.mapConserve(applyObjBody)
        k:
          if (own2 is own) && (isym2 is isym) && (sym2 is sym) &&
              (paramsOpt2 is paramsOpt) &&
              (auxParams2 is auxParams) &&
              (parentPath2 is parentPath) &&
              (methods2 is methods) &&
              (privateFields2 is privateFields) &&
              (publicFields2 is publicFields) &&
              (preCtor2 is preCtor) && (ctor2 is ctor) &&
              (mod2 is mod)
            then defn else ClsLikeDefn(own2, isym2, sym2, kind, paramsOpt2, 
              auxParams2, parentPath2, methods2, privateFields2, publicFields2, preCtor2, ctor2, mod2)
      parentPath match
        case Some(pp) => applyPath(pp): pp2 =>
          withoutParentPath:
            if pp2 is pp then parentPath else Some(pp2)
        case None => withoutParentPath(parentPath)
      
  
  def applyArg(arg: Arg)(k: Arg => Block): Block =
    applyPath(arg.value): val2 =>
      k(if val2 is arg.value then arg else Arg(arg.spread, val2))
  
  def applyParamList(pl: ParamList): ParamList =
    def applyParam(p: Param): Param =
      val sym2 = p.sym.subst
      if sym2 is p.sym then p else p.copy(sym = sym2)
    val params2 = pl.params.mapConserve(applyParam)
    val rest2 = pl.restParam.mapConserve(applyParam)
    if (params2 is pl.params) && (rest2 is pl.restParam)
      then pl else ParamList(pl.flags, params2, rest2)
  
  def applyCase(cse: Case)(k: Case => Block): Block = cse match
    case Case.Lit(lit) => k(cse)
    case Case.Cls(cls, path) =>
      val cls2 = cls.subst
      applyPath(path): path2 =>
        k(if (cls2 is cls) && (path2 is path) then cse else Case.Cls(cls2, path2))
    case Case.Tup(len, inf) => k(cse)
    case Case.Field(name, safe) => k(cse)
  
  def applyHandler(hdr: Handler): Handler =
    val sym2 = hdr.sym.subst
    val resumeSym2 = hdr.resumeSym.subst
    val params2 = hdr.params.mapConserve(applyParamList)
    val body2 = applySubBlock(hdr.body)
    if (sym2 is hdr.sym) && (resumeSym2 is hdr.resumeSym) &&
        (params2 is hdr.params) && (body2 is hdr.body)
      then hdr else Handler(sym2, resumeSym2, params2, body2)
  
  def applyLam(lam: Lambda): Lambda =
    val params2 = applyParamList(lam.params)
    val body2 = applySubBlock(lam.body)
    if (params2 is lam.params) && (body2 is lam.body) then lam else Lambda(params2, body2)
  
  def applyListOf[A](ls: List[A], f: (A, (A => Block)) => Block)(k: List[A] => Block): Block =
    def rec(ls: List[A], k: List[A] => Block): Block = ls match
      case Nil => k(Nil)
      case a :: t =>
        f(a, a2 => rec(t, t2 => if (a2 is a) && (t2 is t) then k(ls) else k(a2 :: t2)))
    rec(ls, k)



class BlockTransformerShallow(subst: SymbolSubst) extends BlockTransformer(subst):
  override def applyLam(lam: Lambda) = lam
  override def applyFunDefn(fun: FunDefn): FunDefn = fun
  override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
    case _: FunDefn | _: ClsLikeDefn => k(defn)
    case _: ValDefn => super.applyDefn(defn)(k)
  
  override def applyHandler(hdr: Handler): Handler = hdr
  
  override def applyBlock(b: Block): Block = b match
    case HandleBlock(l, res, par, args, cls, hdr, bod, rst) =>
      val l2 = applyLocal(l)
      val res2 = applyLocal(res)
      applyPath(par): par2 =>
        applyListOf(args, applyPath(_)(_)): args2 =>
          val cls2 = cls.subst
          val hdr2 = hdr.mapConserve(applyHandler)
          val rst2 = applySubBlock(rst)
          if (l2 is l) && (res2 is res) && (par2 is par) && (args2 is args) &&
              (cls2 is cls) && (hdr2 is hdr) && (rst2 is rst)
            then b else HandleBlock(l2, res2, par2, args2, cls2, hdr2, bod, rst2)
    case _ => super.applyBlock(b)

// Does not traverse into sub-blocks or definitions. The purpose of this is is to only rewrite a block's data, i.e. 
// paths, values, cases, etc. within a block. Can be used in tandem with `BlockTransformer` or `BlockTransformerShallow` 
// to traverse sub-blocks while using this class to perform more complicated transformations on the blocks themselves.
class BlockDataTransformer(subst: SymbolSubst) extends BlockTransformerShallow(subst):
  override def applySubBlock(b: Block): Block = b
