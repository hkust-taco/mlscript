package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*


// Default implementation: nothing is transformed
class BlockTransformer(subst: SymbolSubst):
  
  given SymbolSubst = subst
  
  def applyProgram(prog: Program): Program =
    val imports2 = prog.imports.mapConserve(applyImport)
    val main2 = applyMainBlock(prog.main)
    if (imports2 is prog.imports) && (main2 is prog.main) then prog
    else Program(imports2, main2)
  
  def applyMainBlock(main: Block): Block =
    applyBlock(main)
  
  def applyImport(imp: ImportSymbol -> Str): ImportSymbol -> Str =
    val (l, s) = imp
    val l2 = applyImportSymbol(l)
    if l2 is l then imp else l2 -> s
  
  def applySubBlock(b: Block): Block = applyBlock(b)
  
  /** Called for any sub block not in the `rest` position (when `rest` is nonempty).
    * This is not called for Label body or function body. */
  def applySubBlockNonTail(b: Block): Block = applySubBlock(b)
  
  def applyBlock(b: Block): Block = b match
    case _: End | _: Unreachable => b
    case Break(lbl) =>
      val lbl2 = lbl.subst
      if lbl2 is lbl then b else Break(lbl2)
    case Continue(lbl) =>
      val lbl2 = lbl.subst
      if lbl2 is lbl then b else Continue(lbl2)
    case Return(res) =>
      applyResult(res): res2 =>
        if res2 is res then b else Return(res2)
    case Throw(exc) =>
      applyResult(exc): exc2 =>
        if exc2 is exc then b else Throw(exc2)
    case Match(scrut, arms, dflt, rst) =>
      def applySub(b: Block) = if rst.isEmpty then applySubBlock(b) else applySubBlockNonTail(b)
      applyPath(scrut): scrut2 =>
        applyListOf(
          arms,
          (tup, k) =>
            val (cse, blk) = tup
            val blk2 = applySub(blk)
            applyCase(cse): cse2 =>
              if (cse2 is cse) && (blk is blk2) then k(tup) else k(cse2 -> blk2)
        ): arms2 =>
            val dflt2 = dflt.mapConserve(applySub)
            val rst2 = applySubBlock(rst)
            if (scrut2 is scrut) &&
                (arms2 is arms) &&
                (dflt2 is dflt) && (rst2 is rst)
              then b else Match(scrut2, arms2, dflt2, rst2)
    case Label(lbl, loop, bod, rst) =>
      val lbl2 = lbl.subst
      val bod2 = if loop then applyScopedBlock(bod) else applySubBlock(bod)
      val rst2 = applySubBlock(rst)
      if (lbl2 is lbl) && (bod2 is bod) && (rst2 is rst) then b else Label(lbl2, loop, bod2, rst2)
    case Begin(sub, rst) =>
      def applySub(b: Block) = if rst.isEmpty then applySubBlock(b) else applySubBlockNonTail(b)
      val sub2 = applySub(sub)
      val rst2 = applySubBlock(rst)
      if (sub2 is sub) && (rst2 is rst) then b else Begin(sub2, rst2)
    case TryBlock(sub, fin, rst) =>
      def applySub(b: Block) = if rst.isEmpty then applySubBlock(b) else applySubBlockNonTail(b)
      val sub2 = applySub(sub)
      val fin2 = applySub(fin)
      val rst2 = applySubBlock(rst)
      if (sub2 is sub) && (fin2 is fin) && (rst2 is rst) then b else TryBlock(sub2, fin2, rst2)
    case Assign(l, r, rst) =>
      applyResult(r): r2 =>
        val l2 = applyAssignLhs(l)
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
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      applyResult(rhs): rhs2 =>
        applyPath(lhs): lhs2 =>
          applyPath(fld): fld2 =>
            val rest2 = applySubBlock(rest)
            if (lhs2 is lhs) && (fld2 is fld) && (rhs2 is rhs) && (rest2 is rest)
            then b
            else AssignDynField(lhs2, fld2, arrayIdx, rhs2, rest2)
    case _: Scoped => applyScopedBlock(b)
  
  // FunDefn body, Lambda body, Handler body, ctor and pCtor are considered "funBodyLike"
  def applyFunBodyLikeBlock(b: Block): Block = applyScopedBlock(b)
  
  // Apply to Blocks that are conceptually "scoped", which includes:
  // - "funBodyLike" blocks
  // - loop body blocks
  // - manually nested `Scoped` blocks
  // These blocks are usually instances of `Scoped`, but "funBodyLike" and loop bodies
  // may not be `Scoped` in practice, because empty `Scoped` blocks may be ignored
  def applyScopedBlock(b: Block): Block = b match
    case Scoped(s, bd) =>
      val nb = applySubBlock(bd)

      // Set does not have .mapConserve
      var hasDiff = false
      val ns = s.map[ScopedSymbol]:
        case s: LocalVarSymbol =>
          val ns = s.subst
          if ns isnt s then hasDiff = true
          ns
        case s: BlockMemberSymbol =>
          val ns = s.subst
          if ns isnt s then hasDiff = true
          ns
        
      if (nb is bd) && !hasDiff then b else Scoped(ns, nb)
    case _ => applySubBlock(b)
  
  
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

  def applyArgss(argss: NELs[List[Arg]])(k: NELs[List[Arg]] => Block): Block =
    applyListOf(argss, applyArgs(_)(_)): newArgss =>
      k(newArgss.ne_!)
  
  def applyArgss(argss: List[List[Arg]])(k: List[List[Arg]] => Block): Block =
    applyListOf(argss, applyArgs(_)(_))(k)
  
  def applyResult(r: Result)(k: Result => Block): Block =
    r match
    case r @ Call(fun, argss) =>
      applyPath(fun): fun2 =>
        applyListOf(argss, (args, k2) => applyArgs(args)(k2)): argss2 =>
          k(if (fun2 is fun) && (argss2 is argss) then r
            else Call(fun2, argss2.ne_!)(r.metadata).withLocOf(r))
    case r @ Instantiate(mut, cls, argss) =>
      applyPath(cls): cls2 =>
        applyListOf(argss, (args, k2) => applyArgs(args)(k2)): argss2 =>
          k(if (cls2 is cls) && (argss2 is argss) then r
            else Instantiate(mut, cls2, argss2)(r.metadata).withLocOf(r))
    case l: Lambda => k(applyLam(l))
    case Tuple(mut, elems) =>
      applyArgs(elems): elems2 =>
        k(if (elems2 is elems) then r else Tuple(mut, elems2).withLocOf(r))
    case Record(mut, fields) =>
      applyRcdArgs(fields): fields2 =>
        k(if fields2 is fields then r else Record(mut, fields2).withLocOf(r))
    case p: Path => applyPath(p)(k)
  
  def applyPath(p: Path)(k: Path => Block): Block = p match
    case DynSelect(qual, fld, arrayIdx) =>
      applyPath(qual): qual2 =>
        applyPath(fld): fld2 =>
          k(if (qual2 is qual) && (fld2 is fld) then p else DynSelect(qual2, fld2, arrayIdx).withLocOf(p))
    case p @ Select(qual, name) =>
      applyPath(qual): qual2 =>
        val sym2 = p.symbol.mapConserve(_.subst)
        k(if (qual2 is qual) && (sym2 is p.symbol) then p else Select(qual2, name)(sym2)(p.sanitize).withLocOf(p))
    case v: Value => applyValue(v)(k)
  
  def applyValue(v: Value)(k: Value => Block) = v match
    case Value.SimpleRef(l) =>
      val l2 = applySimpleSymbol(l)
      k(if (l2 is l) then v else l2.asSimpleRef.withLocOf(v))
    case Value.MemberRef(bms, disamb) =>
      val bms2 = bms.subst
      val disamb2 = disamb.subst
      k(if (bms2 is bms) && (disamb2 is disamb) then v else bms2.asMemberRef(disamb2).withLocOf(v))
    case Value.This(sym) =>
      val sym2 = sym.subst
      k(if (sym2 is sym) then v else sym2.asThis.withLocOf(v))
    case Value.Lit(lit) => k(v)
  
  def applySimpleSymbol(sym: SimpleSymbol): SimpleSymbol = sym match
    case sym: LocalVarSymbol => sym.subst
    case sym: BuiltinSymbol => sym.subst
  
  def applyImportSymbol(sym: ImportSymbol): ImportSymbol = sym match
    case sym: TempSymbol => sym.subst
    case sym: VarSymbol => sym.subst
    case sym: BlockMemberSymbol => sym.subst
  
  def applyAssignLhs(sym: Assignable): Assignable = sym match
    case NoSymbol => NoSymbol
    case sym: TempSymbol => sym.subst
    case sym: VarSymbol => sym.subst
  
  def applyFunDefn(fun: FunDefn): FunDefn =
    val own2 = fun.owner.mapConserve(_.subst)
    val sym2 = fun.sym.subst
    val dSym2 = fun.dSym.subst
    val params2 = fun.params.mapConserve(applyParamList)
    val body2 = applyFunBodyLikeBlock(fun.body)
    if (own2 is fun.owner) && (sym2 is fun.sym) && (dSym2 is fun.dSym) && (params2 is fun.params) && (body2 is fun.body)
      then fun else FunDefn(own2, sym2, dSym2, params2, body2)(fun.configOverride, fun.annotations)
  
  def applyValDefn(defn: ValDefn)(k: ValDefn => Block): Block =
    val ValDefn(tsym, sym, rhs) = defn
    val tsym2 = tsym.subst
    val sym2 = sym.subst
    applyPath(rhs): rhs2 =>
      if (tsym2 is tsym) && (sym2 is sym) && (rhs2 is rhs)
        then k(defn) else k(ValDefn(tsym2, sym2, rhs2)(defn.configOverride, defn.annotations))
  
  def applyPublicField(f: BlockMemberSymbol -> TermSymbol): BlockMemberSymbol -> TermSymbol =
    val f_1_2 = f._1.subst
    val f_2_2 = f._2.subst
    if (f_1_2 is f._1) && (f_2_2 is f._2) then f else f_1_2 -> f_2_2
  
  def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
    val isym2 = defn.isym.subst
    val methods2 = defn.methods.mapConserve(applyFunDefn)
    val privateFields2 = defn.privateFields.mapConserve(_.subst)
    val publicFields2 = defn.publicFields.mapConserve(applyPublicField)
    val ctor2 = applyFunBodyLikeBlock(defn.ctor)
    if (methods2 is defn.methods) &&
        (privateFields2 is defn.privateFields) &&
        (publicFields2 is defn.publicFields) &&
        (ctor2 is defn.ctor)
      then defn else ClsLikeBody(isym2, methods2, privateFields2, publicFields2, ctor2, defn.annotations)
  
  def applyClsLikeDefn(defn: ClsLikeDefn)(k: Defn => Block): Block =
    val ClsLikeDefn(own, isym, sym, ctorSym, kind, paramsOpt, auxParams, parentPath, methods,
      privateFields, publicFields, preCtor, ctor, mod, bufferable) = defn
    val own2 = own.mapConserve(_.subst)
    val isym2 = isym.subst
    val sym2 = sym.subst
    val ctorSym2 = ctorSym.mapConserve(_.subst)
    val paramsOpt2 = paramsOpt.mapConserve(applyParamList)
    val auxParams2 = auxParams.mapConserve(applyParamList)
    def helper(parentPath2: Opt[Path]) =
      val methods2 = methods.mapConserve(applyFunDefn)
      val privateFields2 = privateFields.mapConserve(_.subst)
      val publicFields2 = publicFields.mapConserve(applyPublicField)
      val preCtor2 = applyFunBodyLikeBlock(preCtor)
      val ctor2 = applyFunBodyLikeBlock(ctor)
      val mod2 = mod.mapConserve(applyObjBody)
      k:
        if (own2 is own) && (isym2 is isym) && (sym2 is sym) && (ctorSym2 is ctorSym) &&
            (paramsOpt2 is paramsOpt) &&
            (auxParams2 is auxParams) &&
            (parentPath2 is parentPath) &&
            (methods2 is methods) &&
            (privateFields2 is privateFields) &&
            (publicFields2 is publicFields) &&
            (preCtor2 is preCtor) && (ctor2 is ctor) &&
            (mod2 is mod)
          then defn else ClsLikeDefn(own2, isym2, sym2, ctorSym2, kind, paramsOpt2, 
            auxParams2, parentPath2, methods2, privateFields2, publicFields2, preCtor2, ctor2, mod2, bufferable)(defn.configOverride, defn.annotations)
    parentPath match
    case Some(pp) => applyPath(pp): pp2 =>
      helper:
        if pp2 is pp then parentPath else Some(pp2)
    case None => helper(parentPath)
  
  def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
    case defn: FunDefn => k(applyFunDefn(defn))
    case defn: ValDefn => applyValDefn(defn)(k)
    case defn: ClsLikeDefn => applyClsLikeDefn(defn)(k)
  
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
    val body2 = applyFunBodyLikeBlock(hdr.body)
    if (sym2 is hdr.sym) && (resumeSym2 is hdr.resumeSym) &&
        (params2 is hdr.params) && (body2 is hdr.body)
      then hdr else Handler(sym2, resumeSym2, params2, body2)
  
  def applyLam(lam: Lambda): Lambda =
    val params2 = applyParamList(lam.params)
    val body2 = applyFunBodyLikeBlock(lam.body)
    if (params2 is lam.params) && (body2 is lam.body) then lam else Lambda(params2, body2)(lam.annot)
  
  def applyListOf[A](ls: List[A], f: (A, (A => Block)) => Block)(k: List[A] => Block): Block =
    def rec(ls: List[A], k: List[A] => Block): Block = ls match
      case Nil => k(Nil)
      case a :: t =>
        f(a, a2 => rec(t, t2 => if (a2 is a) && (t2 is t) then k(ls) else k(a2 :: t2)))
    rec(ls, k)



class BlockTransformerShallow(subst: SymbolSubst) extends BlockTransformer(subst):
  override def applyLam(lam: Lambda) = lam
  // Note: no need to override things like applyFunDefn, as they are only called by applyDefn
  override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
    case _: FunDefn | _: ClsLikeDefn => k(defn)
    case _: ValDefn => super.applyDefn(defn)(k)
  
  override def applyHandler(hdr: Handler): Handler = hdr

// Does not traverse into sub-blocks or definitions. The purpose of this is is to only rewrite a block's data, i.e. 
// paths, values, cases, etc. within a block. Can be used in tandem with `BlockTransformer` or `BlockTransformerShallow` 
// to traverse sub-blocks while using this class to perform more complicated transformations on the blocks themselves.
class BlockDataTransformer(subst: SymbolSubst) extends BlockTransformerShallow(subst):
  override def applySubBlock(b: Block): Block = b
