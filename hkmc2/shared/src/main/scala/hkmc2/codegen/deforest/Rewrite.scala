package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, Buffer}
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, ParamBind, Fun, Ins}



class DeforestRewriter(val solver: DeforestConstrainSolver)(using Raise):
  import solver.FinalDest
  given tl: TraceLogger = solver.tl
  given dState: Deforest.State = solver.dState
  given eState: Elaborator.State = solver.collector.elabState
  given pre: DeforestPreAnalyzer = solver.preAnalyzer
  
  extension (vs: Ls[VarSymbol])
    def asParamList: ParamList =
      ParamList(ParamListFlags.empty, vs.map(Param.simple), N)
  
  private val _symSubst = new SymbolSubst()
  
  // C(1, 2)
  //  ~> let x = 1; y = 2 in (fvs) => branchBody(fvs, x, y)
  // if scrut is C then let a = scrut.x; b = scrut.y in body
  //  ~> scrut(fvs)
  //  ~> fun branchBody(fvs, x, y) = let a = x; b = y in body
  
  val ctorFieldSyms = MutMap.empty[CtorDtorId, Ls[TempSymbol]] // the `a` and `b`
  val newPolyFnSyms = LinkedHashMap.empty[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]]
  val branchSelSyms = MutMap.empty[CtorDtorId, VarSymbol]
  val branchFunSyms = LinkedHashMap.empty[BranchId, (BlockMemberSymbol, TermSymbol)]
  // branch fun params for fields (which share the same symbol in `branchSelSyms`)
  val branchFunParamFieldSyms = MutMap.empty[BranchId, Ls[VarSymbol]]
  val ctorWhichBranch = MutMap.empty[CtorDtorId, BranchId]
  // compute original bodies of a branch
  val branchOriginalBodies = MutMap.empty[ResultId -> Opt[CtorCls], Block]
  // if a fusing dtor needs explicit returns
  val dtorExplicitRet = MutMap.empty[ResultId, Boolean].withDefaultValue(false)
  
  // compute new symbols
  locally {
    for (ctor, FinalDest(dest, sels)) <- solver.finalCtorDests do
      // create ctor field syms
      val ctorInfo = solver.fusingIdInfo(ctor).asInstanceOf[Ctor]
      ctorFieldSyms(ctor) =
        val clsNme = ctorInfo.ctor match
          case n: Int => s"tup$n"
          case c: (ClassSymbol | ModuleOrObjectSymbol) => c.name
        ctorInfo.args.unzip._1.map:
          case termSym: TermSymbol => new TempSymbol(N, s"${clsNme}_${termSym.nme}")
          case n: Int => new TempSymbol(N, s"${clsNme}_$n")
      
      // create poly fun syms
      for
        ctorInstId <- List(ctor.instId, dest.instId)
        case path@(pathTo :+ refedFun) <- ctorInstId.inits
      do
        val groupFuns = solver.collector.funToSccGroups(refedFun.getReferredFun.get)
        newPolyFnSyms.getOrElseUpdate(
          path,
          groupFuns
            .map: f =>
              val name = path.mkFunName + s"$$${f.nme}"
              f -> (
                new BlockMemberSymbol(name, Nil, true),
                new TermSymbol(Fun, N, Tree.Ident(name)))
            .toMap)
      
      // create branch sel syms
      for sel <- sels do
        branchSelSyms.getOrElseUpdate(
          sel,
          locally:
            val selInfo = solver.fusingIdInfo(sel).asInstanceOf[FieldSel]
            val clsNme = selInfo.isSelFromCls match
              case cls: ClassSymbol => cls.name
              case n: Int => s"tup$n"
            selInfo.field match
              case termSym: TermSymbol => new VarSymbol(Tree.Ident(s"${clsNme}_${termSym.nme}"))
              case ith: Int => new VarSymbol(Tree.Ident(s"${clsNme}_$ith"))
        )
      
      // ctor dest branch function computations
      val matchBlk = pre.res.matchScrutToMatchBlock(dest._1)
      val (whichBranch, whichBranchPreBody) =
        val tmp =
          val ctorCls = ctorInfo.ctor
          matchBlk.arms
            .find: (cse, _) =>
              cse match
              case Case.Cls(cls, path) => cls === ctorCls
              case Case.Tup(len, inf) => len === ctorCls
              case _ => die
            .map(b => ctorCls -> b._2)
        tmp.map(_._1) ->
        tmp.fold(matchBlk.dflt.get)(_._2)
      val destBranchId: BranchId = dest -> whichBranch
      // identify the dest branchid for a ctor
      ctorWhichBranch(ctor) = destBranchId
      // compute the function symbols for branch funs
      branchFunSyms.getOrElseUpdate(
        destBranchId,
        locally:
          val branchName = whichBranch.fold("_dflt"):
            case n: Int => s"_$n"
            case cls: ClassLikeSymbol => s"_${cls.nme}"
          val scrutName = dest._1.getReferredSym.nme
          val branchFnNme = s"${dest.instId.mkFunName}$$$scrutName$branchName"
          (new BlockMemberSymbol(branchFnNme, Nil, true),
          new TermSymbol(Fun, N, Tree.Ident(branchFnNme)))
      )
      // compute the function parameters corresponding to ctor fields of branch funs
      branchFunParamFieldSyms.getOrElseUpdate(
        destBranchId,
        locally:
          val completeArgs: Ls[SelField] = ctorInfo.args.unzip._1
          val selsInfos: Map[SelField, CtorDtorId] = sels
            .iterator
            .map: sel =>
              solver.fusingIdInfo(sel).asInstanceOf[FieldSel].field -> sel
            .toMap
          completeArgs.map: selField =>
            selsInfos.get(selField) match
            case Some(selId) => branchSelSyms(selId)
            case None => selField match
              case n: Int => VarSymbol(Tree.Ident(s"_tup_${n}"))
              case tSym: TermSymbol => VarSymbol(Tree.Ident(s"_${tSym.name}"))
      )
      // compute the complete deforestable branch body of a fusing match
      // also compute if the match contains explicit return
      branchOriginalBodies.getOrElseUpdate(
        dest._1 -> whichBranch,
        locally:
          val ogBranchBody = Begin(whichBranchPreBody, pre.res.getFullRestOfMatch(dest._1))
          val transformer = new ReplaceBreakAndCheckExplicitRet
          val newBranch = transformer.applyBlock(ogBranchBody)
          dtorExplicitRet(dest._1) ||= transformer.hasExplicitRet
          newBranch
      )
  }
    
  // with new symbols computed, compute free vars
  // for all the fusing branches of a dtor
  // the values are sorted by uid
  val dtorBranchFunsFvs: Map[CtorDtorId, Ls[Symbol]] =
    val store = MutMap.empty[CtorDtorId, MutMap[Opt[CtorCls], Set[Symbol]]]
    extension (b: Block)
      // ctx should be the branch fun parameters corresponding to ctor fields 
      def deforestFreeVars(ctx: collection.Set[Symbol], instId: InstantiationId) =
        val traverser = new FreeVarTraverser(ctx, instId)
        traverser.applyBlock(b)
        (traverser.refedVars.toSet -- traverser.assignedVars.toSet).filter: s =>
          s.asClsLike.isEmpty
    class FreeVarTraverser(ctx: collection.Set[Symbol], instId: InstantiationId) extends BlockTraverser:
      extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
      val assignedVars = MutSet.from[Symbol]:
        pre.b match
          case Scoped(syms, body) =>
            ctx
            ++ newPolyFnSyms.values.flatMap(_.values.unzip._1)
            ++ branchFunSyms.values.unzip._1
            ++ eState.builtinOpsMap.values
            ++ (eState.globalThisSymbol :: eState.runtimeSymbol :: Nil)
            ++ syms
          case _ => die
      val refedVars = MutSet.empty[Symbol]
      
      override def applyValue(v: Value): Unit =
        v match
        case Value.Ref(l, disamb) => refedVars.add(l)
        case _ => super.applyValue(v)
      
      override def applyResult(r: Result): Unit =
        r match
        case s@DeforestTupSelect(_, _) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
          refedVars.add(branchSelSyms(s.uid.toCtorDtorId))
        case _ => super.applyResult(r)
      
      override def applyPath(p: Path): Unit =
        p match
        case s@DeforestableSelect(sym: TermSymbol) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
          assert(sym.k is ParamBind)
          refedVars.add(branchSelSyms(s.uid.toCtorDtorId))
        case _ => super.applyPath(p)
      
      override def applyBlock(b: Block): Unit =
        b match
        case m: Match if solver.finalDtorSrcs.isDefinedAt(m.scrut.uid.toCtorDtorId) =>
          refedVars.addAll(store(m.scrut.uid.toCtorDtorId).values.flatten)
          super.applyPath(m.scrut)
        case Assign(lhs, rhs, rest) =>
          assignedVars.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case _ => super.applyBlock(b)
      
      override def applyParamList(pl: ParamList): Unit =
        assignedVars.addAll(pl.params.map(_.sym)): Unit
      
      override def applyDefn(defn: Defn): Unit =
        defn match
        case fDef: FunDefn =>
          assignedVars.add(fDef.sym)
          super.applyDefn(defn)
        case _: ClsLikeDefn => die
        case vDef: ValDefn =>
          assignedVars.add(vDef.sym)
          super.applyDefn(defn)
    end FreeVarTraverser
    
    // need to do a sort and only start with those containing zero nested fusing matches
    val innerToOuterDtors =
      branchFunSyms.keys.toList.sortBy: branchId =>
        -pre.res.matchScrutToCtxOfMatch(branchId._1.exprId).size
    
    for destBranchId@(dest, whichBranch) <- innerToOuterDtors do
      store.getOrElseUpdate(dest, MutMap.empty).getOrElseUpdate(
        whichBranch,
        branchOriginalBodies(dest._1 -> whichBranch).deforestFreeVars(
          branchFunParamFieldSyms(destBranchId).toSet,
          dest._2
        )
      )
    store.view.mapValues(_.values.flatten.toSet.toList.sortBy(_.uid)).toMap
  end dtorBranchFunsFvs
  
  // generate var symbols for fv params of branch funs
  val branchFunParamFvSyms = MutMap.empty[BranchId, Ls[Symbol -> VarSymbol]]
  // when rewriting, we should call a dtor with these free vars
  // for non-nested matches, these are the free var symbols in the original program
  // for nested matches, these are the free var VarSymbols from parent fusing matches
  val callDtorFvs = MutMap.empty[CtorDtorId, Ls[Symbol]]
  // when rewriting, we should transform a ctor to a lam with the following parameter
  val ctorLamFvs = MutMap.empty[CtorDtorId, Ls[VarSymbol]]
  locally {
    for (branchId, _) <- branchFunSyms do
      branchFunParamFvSyms.getOrElseUpdate(
        branchId,
        dtorBranchFunsFvs(branchId._1).map: s =>
          s -> new VarSymbol(Tree.Ident(s"fv_${s.nme}"))
      )
    for (dtorId, _) <- dtorBranchFunsFvs do
      callDtorFvs.getOrElseUpdate(
        dtorId,
        locally:
          val ogFvs = dtorBranchFunsFvs(dtorId)
          pre.res.getNearestFusingParentMatch(dtorId, solver) match
            case None => ogFvs
            case Some(branchId) =>
              val parentMatchFvs = branchFunParamFvSyms(branchId)
              ogFvs.map: s =>
                parentMatchFvs.find(_._1 == s).fold(s)(_._2)
      )
    for (ctorId, FinalDest(dtorId, _)) <- solver.finalCtorDests do
      ctorLamFvs(ctorId) = callDtorFvs(dtorId).map(s => new VarSymbol(Tree.Ident(s"fv_ctorLam_${s.nme}")))
  }
  
  private class ReplaceBreakAndCheckExplicitRet extends BlockTransformerShallow(_symSubst):
    var hasExplicitRet = false
    override def applyBlock(b: Block): Block = b match
      case Break(label) =>
        val labelRest = pre.res.getFullRestOrLabel(label)
        assert(!pre.res.labelSymToLabelBlk(label).loop)
        applyBlock(labelRest)
      case Return(_, implicitRet) =>
        hasExplicitRet ||= !implicitRet
        super.applyBlock(b)
      case _ => super.applyBlock(b)
  end ReplaceBreakAndCheckExplicitRet
  
  
  
  
  
  
  // TODO:
  // - handle scoped blocks
  // - refresh vars (this needs to be done after deforestation rewriting because this may change uid)
  // forceExplicitReturn: branch functions should always explicitly return
  private class Rewriter(instId: InstantiationId, forceExplicitRet: Boolean = false) extends BlockTransformer(_symSubst):
    extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
    private def newRefId(refId: ResultId, refSym: TermSymbol) =
      instId match
      case Nil => refId :: Nil
      case pathTo :+ called =>
        val lastRefedSymbol = called.getReferredFun.get
        val funToSccRepMap = solver.collector.funToSccRep
        (funToSccRepMap(lastRefedSymbol), funToSccRepMap(refSym)) match
          case (Some(a), Some(b)) if a is b => instId
          case _ => instId :+ refId
      case _ => die
    override def applyResult(r: Result)(k: Result => Block): Block =
      r match
      case s@DeforestTupSelect(_, _) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
      case ctor@CtorCall(cls, args) if solver.finalCtorDests.isDefinedAt(ctor.uid.toCtorDtorId) =>
        val fieldSyms = ctorFieldSyms(ctor.uid.toCtorDtorId)
        val (branchBms, branchTermSym) = branchFunSyms(ctorWhichBranch(ctor.uid.toCtorDtorId))
        val ctorLamParams = ctorLamFvs(ctor.uid.toCtorDtorId)
        val callBranchFun =
          Lambda(
            ctorLamParams.asParamList,
            Return(
              Call(
                Value.Ref(branchBms, S(branchTermSym)),
                (ctorLamParams ++ fieldSyms).map(a => Arg(N, Value.Ref(a, N))))(true, false, false),
              false))
        args.zip(fieldSyms).foldRight(k(callBranchFun)):
          case (Arg(N, a) -> fieldSym, rest) =>
            applyPath(a): fusedField =>
              Scoped(Set(fieldSym), Assign(fieldSym, fusedField, rest))
          case _ => die
      case _ => super.applyResult(r)(k)
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      p match
      case ref@FunRef(f) if newPolyFnSyms.isDefinedAt(newRefId(ref.uid, f)) =>
        val (bms, tSym) = newPolyFnSyms(newRefId(ref.uid, f))(f)
        k(Value.Ref(bms, S(tSym)))
      case ctor@CtorCall(_, args) if solver.finalCtorDests.isDefinedAt(ctor.uid.toCtorDtorId) =>
        assert(args.isEmpty)
        val (branchBms, branchTermSym) = branchFunSyms(ctorWhichBranch(ctor.uid.toCtorDtorId))
        val ctorLamParams = ctorLamFvs(ctor.uid.toCtorDtorId)
        val lambdaSym = new TempSymbol(N, "deforest$lam")
        Scoped(
          Set(lambdaSym),
          Assign(
            lambdaSym,
            Lambda(
              ctorLamParams.asParamList,
              Return(Call(
                Value.Ref(branchBms, S(branchTermSym)),
                ctorLamParams.map(s => Arg(N, Value.Ref(s)))
              )(true, false, false), false)),
            k(Value.Ref(lambdaSym, N)))
        )
      case s@DeforestableSelect(sym: TermSymbol) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        assert(sym.k is ParamBind)
        k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
      case _ => super.applyPath(p)(k)
    
    override def applyBlock(b: Block): Block =
      b match
      case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.toCtorDtorId) =>
        val explicitRet = forceExplicitRet || dtorExplicitRet(scrut.uid)
        val callWithFvs = callDtorFvs(scrut.uid.toCtorDtorId)
        applyPath(scrut): newScrut =>
          Return(
            Call(newScrut, callWithFvs.map(s => Arg(N, Value.Ref(s, N))))(true, false, false),
            !explicitRet)
      case Return(res, implct) if forceExplicitRet => super.applyBlock(Return(res, false))
      case _ => super.applyBlock(b)
  end Rewriter
  
  // this is a shallow traverser because nested funs have their own scoped blocks
  // this is only used for new branch funs, which don't have scoped blocks;
  // otherwise we only refresh parameters and symbols in scoped blocks
  // tempsymbols
  // bms without an owner (local funs and immut val def)
  // varsymbols (for local lets)
  // TODO: branch symbols...?
  // TODO: basically a `Block.definedSymbols`... with labels?
  extension (b: Block) def branchFunScopedSymbols: collection.Set[Symbol] =
    object BranchFunToplvlScopedSymbols extends BlockTraverserShallow:
      val collectedScopedSyms = MutSet.empty[Symbol]
      override def applyBlock(b: Block): Unit =
        b match
        case Assign(lhs, rhs, rest) =>
          collectedScopedSyms.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case _ => super.applyBlock(b)
      
      override def applyDefn(defn: Defn): Unit =
        defn match
        case fDef: FunDefn =>
          collectedScopedSyms.add(fDef.sym)
        case vDef: ValDefn =>
          collectedScopedSyms.add(vDef.sym)
        case _: ClsLikeDefn => die
    end BranchFunToplvlScopedSymbols
    BranchFunToplvlScopedSymbols.applyBlock(b)
    BranchFunToplvlScopedSymbols.collectedScopedSyms
  
  // in scoped blocks:
  // tmpsymbol
  // membersymbol: for fundef and valdef
  // varsymbol: for let bind
  // others:
  // label symbol
  private class RefreshSymbol(existingMapping: Map[Symbol, Symbol]) extends BlockTransformer(_symSubst):
    val mapping = MutMap.from(existingMapping)
    override def applyScopedBlock(b: Block): Block =
      b match
      case Scoped(syms, body) =>
        val newSyms = MutSet.empty[Symbol]
        for s <- syms.toList.sortBy(_.uid) do
          assert(!mapping.isDefinedAt(s), s"already defined: $s")
          val newS = s match
            case tmpSym: TempSymbol => new TempSymbol(N, tmpSym.nme)
            case bms: BlockMemberSymbol =>
              assert(bms.tsym.forall(_.owner.isEmpty))
              val newBms = new BlockMemberSymbol(bms.nme, Nil, bms.nameIsMeaningful)
              newBms.tsym = bms.tsym.map(t => new TermSymbol(t.k, N, t.id))
              newBms
            case varSym: VarSymbol => new VarSymbol(varSym.id)
            case _ => lastWords(s"unexpected symbol kind: $s")
          mapping(s) = newS
          newSyms.add(newS)
        val res = Scoped(newSyms, applyBlock(body))
        for s <- syms do mapping.remove(s)
        res
      case _ => super.applyScopedBlock(b)
    override def applyBlock(b: Block): Block =
      b match
      case Assign(lhs, rhs, rest) =>
        applyResult(rhs): newRhs =>
          val newLhs = mapping.getOrElse(lhs, lhs)
          val newRest = applyBlock(rest)
          if (newLhs is lhs) && (newRhs is rhs) && (newRest is rest) then b else Assign(newLhs, newRhs, newRest)
      case Label(label, loop, body, rest) =>
        assert(!mapping.isDefinedAt(label) && !loop)
        val newLabel = new LabelSymbol(label.trm, label.nme)
        mapping(label) = newLabel
        val newBody = applyBlock(body)
        mapping.remove(label)
        val newRest = applyBlock(rest)
        Label(newLabel, loop, newBody, newRest)
      case Break(label) => Break(mapping.getOrElse(label, label).asInstanceOf[LabelSymbol])
      case Continue(label) => die
      case _ => super.applyBlock(b)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      assert(fun.owner.isEmpty)
      val sym2 = mapping.getOrElse(fun.sym, fun.sym).asInstanceOf[BlockMemberSymbol]
      val dSym2 = mapping.getOrElse(fun.sym, fun.sym).asInstanceOf[BlockMemberSymbol].tsym.getOrElse(lastWords(s"${mapping.getOrElse(fun.sym, fun.sym)} no tsym"))
      val oldParamSyms = Buffer.empty[VarSymbol]
      val params2 = fun.params.map:
        case ParamList(flags, params, N) =>
          ParamList(
            flags,
            params.map: 
              case Param(flags, sym, sign, modulefulness) =>
                oldParamSyms.append(sym)
                val newSym = new VarSymbol(sym.id)
                assert(!mapping.isDefinedAt(sym))
                mapping(sym) = newSym
                Param(flags, newSym, sign, modulefulness),
            N)
        case _ => die
      val body2 = applyFunBodyLikeBlock(fun.body)
      for s <- oldParamSyms do mapping.remove(s)
      FunDefn(N, sym2, dSym2, params2, body2)(fun.forceTailRec)
    
    override def applyValDefn(defn: ValDefn)(k: ValDefn => Block): Block =
      val ValDefn(tsym, sym, rhs) = defn
      val tsym2 = tsym.subst
      val sym2 = sym.subst
      applyPath(rhs): rhs2 =>
        k(ValDefn(
          mapping.getOrElse(sym, sym).asBlkMember.get.tsym.get,
          mapping.getOrElse(sym, sym).asBlkMember.get,
          rhs2))
    
    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case Value.Ref(l, x) =>
        pre.res.modSymToBms.get(l) match
          case None => 
            mapping.get(l) match
              case None => k(Value.Ref(l, x))
              case Some(newBms: BlockMemberSymbol) => k(Value.Ref(newBms, newBms.tsym))
              case Some(newSym) => k(Value.Ref(newSym, N))
          case Some(bms) =>
            k(Value.Ref(bms, l.asMod))
      case _ => super.applyValue(v)(k)
  end RefreshSymbol
  
  val newPolyFuns =
    for
      (instId, funSymMap) <- newPolyFnSyms
      (referringFun, (bms, tSym)) <- funSymMap.toList.sortBy(_._1.uid)
    yield
      val fDefn = pre.res.funSymToFunDefn(referringFun)
      val transformedBody = new Rewriter(instId).applyBlock(fDefn.body)
      // refresh other local symbols: for funs, we can check existing scoped blocks and
      // there is no need to add scoped blocks, because function bodies now already are scoped
      val bodyWithCorrectSymbols = new RefreshSymbol(Map.empty).applyBlock(transformedBody)
      FunDefn(
        N, bms, tSym, fDefn.params,
        bodyWithCorrectSymbols)(false)
  end newPolyFuns
  
  val newBranchFuns =
    for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
      val originalBranchBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
      val transformedBranchBody = new Rewriter(dtorId.instId, forceExplicitRet = true).applyBlock(originalBranchBody)
      // after we can have scoped blocks in branches,
      // we can remove this pass of computing `branchFunScopedSymbols`
      val scopedBody = Scoped(transformedBranchBody.branchFunScopedSymbols, transformedBranchBody)
      val bodyWithCorrectSymbols = new RefreshSymbol(branchFunParamFvSyms(branchId).toMap).applyBlock(scopedBody)
      FunDefn(N, bms, tSym,
        (branchFunParamFvSyms(branchId).unzip._2 ++ branchFunParamFieldSyms(branchId)).asParamList :: Nil,
        bodyWithCorrectSymbols
      )(false)
  end newBranchFuns
  
  
  val newBody =
    val newMainBody =
      Scoped(
        Set.from(newPolyFuns.map(_.sym) ++ newBranchFuns.map(_.sym)),
        (new Rewriter(Nil).applyBlock(pre.b)))
    (newPolyFuns ++ newBranchFuns).foldRight(newMainBody): (fdef, rest) =>
      Define(fdef, rest)
  
  
  
  
  
  
  
  
  
  // for (instId, bms) <- newPolyFnSyms do
  //   tl.log(bms)
  
  tl.log("========")
  for (dtorId, fvs) <- dtorBranchFunsFvs do
    tl.log(s"free vars of ${dtorId.pp}:")
    tl.log(s"\t$fvs")
  for (dtorId, callFvs) <- callDtorFvs do
    tl.log(s"call dtor ${dtorId.pp} with:")
    tl.log(s"\t$callFvs")
  // tl.log("--------")
  // tl.log(newBody.pp)
  // for (bId, body) <- branchOriginalBodies do
  //   tl.log(bId._1.getResult)
  //   tl.log(s"\t${body.pp}")
end DeforestRewriter

