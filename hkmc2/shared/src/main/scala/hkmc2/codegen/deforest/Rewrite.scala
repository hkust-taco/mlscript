package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap}
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
        // newPolyFnSyms.getOrElseUpdate(
        //   path,
        //   new BlockMemberSymbol(path.mkFunName, Nil, true) ->
        //   new TermSymbol(Fun, N, Tree.Ident(path.mkFunName)))
      
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
          val branchFnNme = s"$scrutName$branchName"
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
  // - free vars
  // - handle scoped blocks
  // - refresh vars (this needs to be done after deforestation rewriting because this may change uid)
  //    refs to MM(moduleSymbol).fun needs to be changed to MM(bms).fun
  private class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
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
              Assign(fieldSym, fusedField, rest)
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
        Assign(
          lambdaSym,
          Lambda(
            ctorLamParams.asParamList,
            Return(Call(
              Value.Ref(branchBms, S(branchTermSym)),
              ctorLamParams.map(s => Arg(N, Value.Ref(s)))
            )(true, false, false), false)),
          k(Value.Ref(lambdaSym, N)))
      case s@DeforestableSelect(sym: TermSymbol) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        assert(sym.k is ParamBind)
        k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
      case _ => super.applyPath(p)(k)
    
    override def applyBlock(b: Block): Block =
      b match
      case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.toCtorDtorId) =>
        val explicitRet = dtorExplicitRet(scrut.uid)
        val callWithFvs = callDtorFvs(scrut.uid.toCtorDtorId)
        applyPath(scrut): newScrut =>
          Return(
            Call(newScrut, callWithFvs.map(s => Arg(N, Value.Ref(s, N))))(true, false, false),
            explicitRet)
      case _ => super.applyBlock(b)
  end Rewriter
  
  val newPolyFuns =
    for
      (instId, funSymMap) <- newPolyFnSyms
      (referringFun, (bms, tSym)) <- funSymMap
    yield
      val fDefn = pre.res.funSymToFunDefn(referringFun)
      FunDefn(
        N, bms, tSym, fDefn.params, // TODO: refresh symbols
        (new Rewriter(instId).applyBlock(fDefn.body)))(false)
  end newPolyFuns
  
  val newBranchFuns =
    for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
      val originalBranchBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
      FunDefn(N, bms, tSym,
        (branchFunParamFvSyms(branchId).unzip._2 ++ branchFunParamFieldSyms(branchId)).asParamList :: Nil,
        (new Rewriter(dtorId.instId).applyBlock(originalBranchBody)))(false)
  end newBranchFuns
  
  
  val newBody =
    // TODO: scoped blocks
    val newMainBody = (new Rewriter(Nil).applyBlock(pre.b))
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
  tl.log("--------")
  tl.log(newBody.pp)
  // for (bId, body) <- branchOriginalBodies do
  //   tl.log(bId._1.getResult)
  //   tl.log(s"\t${body.pp}")
end DeforestRewriter

