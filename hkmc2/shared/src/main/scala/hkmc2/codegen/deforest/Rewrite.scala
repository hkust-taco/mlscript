package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, Buffer}
import hkmc2.syntax.Fun
import hkmc2.codegen.flowAnalysis.*



class DeforestRewriter(val solver: DeforestFusionSolver)(using Raise):
  
  def apply(): Program =
    if newBody is pre.pgrm.main then pre.pgrm
    else Program(pre.pgrm.imports, newBody)
  
  val collector = solver.constraintSolver.collector
  given tl: TraceLogger = solver.tl
  given fState: FlowAnalysis.State = solver.fState
  given eState: Elaborator.State = solver.eState
  given pre: FlowPreAnalyzer = solver.preAnalyzer
  
  type MatchOrLabelId = ResultId | LabelSymbol
  type BranchId = CtorDtorId -> Opt[CtorCls]
  type LabelId = LabelSymbol -> InstantiationId
  type RestFunId = CtorDtorId | LabelId
  
  extension (restFunId: RestFunId) def withoutInstId: MatchOrLabelId =
    restFunId match
    case ConcreteId(exprId, instId) => exprId
    case l: LabelId => l._1
  extension (restFunId: RestFunId) def getInstId = restFunId match
    case ConcreteId(exprId, instId) => instId
    case l: LabelId => l._2
  extension (matchOrLabelId: MatchOrLabelId) def withInstId(instId: InstantiationId): RestFunId =
    matchOrLabelId match
    case l: LabelSymbol => l -> instId
    case scrutId: ResultId => ConcreteId(scrutId, instId)
  extension (vs: Ls[VarSymbol]) def asParamList: ParamList =
    ParamList(ParamListFlags.empty, vs.map(Param.simple), N)
  extension (c: CtorCls) def ctorClsName: String = c match
    case cls: ClassLikeSymbol => cls.nme
    case n: Int => s"tup$n"
  extension (f: SelField) def fieldName: String = f match
    case tSym: TermSymbol => tSym.nme
    case n: Int => n.toString

  private def getParentLabelOrMatchesAndRestBefore(
    matchOrLabelId: MatchOrLabelId
  ): (Iterator[Label | Match], Block) =
    val ctx = matchOrLabelId match
      case label: LabelSymbol => pre.res.labelSymToCtxOfLabel(label)
      case dtorId: ResultId => pre.res.matchScrutToCtxOfMatch(dtorId)
    val simpleRest = matchOrLabelId match
      case label: LabelSymbol => pre.res.labelSymToLabelBlk(label).rest
      case dtorId: ResultId => pre.res.matchScrutToMatchBlock(dtorId).rest
    def it = ctx.iterator
      .takeWhile:
        case _: (pre.InCtx.Fn | pre.InCtx.ModCtor | pre.InCtx.Cls | pre.InCtx.ClsPreCtor | pre.InCtx.ClsCtor | pre.InCtx.TopLvl) => false
        case _ => true
      .collect:
        case pre.InCtx.LblBody(l) => l
        case pre.InCtx.MtchBody(m, _) => m
        case pre.InCtx.BegnBody(b) => b
    val blockUntilParent = it
      .takeWhile(_.isInstanceOf[Begin])
      .collect:
        case b: Begin => b.rest
      .foldLeft(simpleRest)(Begin.apply)
    val parents = it
      .collect:
        case l: Label => l
        case m: Match => m
      .asInstanceOf[Iterator[Label | Match]]
    parents -> blockUntilParent

  private val _symSubst = SymbolSubst.Id
  
  val newPolyFnSyms = LinkedHashMap.empty[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]]
  val branchSelSyms = MutMap.empty[CtorDtorId, VarSymbol]
  // branch fun params for fields (which share the same symbol in `branchSelSyms`)
  val branchFunParamFieldSyms = MutMap.empty[BranchId, Ls[VarSymbol]]
  val ctorWhichBranch = MutMap.empty[CtorDtorId, BranchId]
  
  // Symbols of branch functions
  // the content of those functions should be
  // `<computation of the branch>; return match_rest(...)`
  val branchFunSyms = LinkedHashMap.empty[BranchId, (BlockMemberSymbol, TermSymbol)]
  
  // Symbols of rest functions for relevant matches or labels.
  // 1) Matches that will be fused or
  // 2) Matches or Labels that properly nest other fusing matches
  // should get their "rest"s extracted as functions,
  // and the content of those functions should be
  // `<computation of rests up to a parent>; return parent_rest(...)`
  val restFunSyms = LinkedHashMap.empty[RestFunId, (BlockMemberSymbol, TermSymbol)]
  
  // original bodies of a branch
  val branchOriginalBodies = MutMap.empty[ResultId -> Opt[CtorCls], Block]
  // original rest function bodies and their parent matches (if any)
  val restOriginalBodiesAndParentRest = MutMap.empty[MatchOrLabelId, Block -> Opt[MatchOrLabelId]]
  
  // compute new symbols
  locally {
    def mkNewPolyFnSyms(path: List[ResultId], refedFun: ResultId): Unit =
      val groupFuns = collector.funToSccGroups(refedFun.getReferredFun.get)
      newPolyFnSyms.getOrElseUpdate(
        path,
        groupFuns
          .map: f =>
            val name = path.mkFunName + s"$$${f.nme}"
            f -> (
              new BlockMemberSymbol(name, Nil, true),
              new TermSymbol(Fun, N, Tree.Ident(name)))
          .toMap)
    end mkNewPolyFnSyms
    
    for case (ctor, finalDest) <- solver.finalCtorDests do
      finalDest match
      case FinalDestSel(dtors, field) =>
        // create poly fun syms
        val instIds = (dtors + ctor).toList.sortBy(_.exprId).map(_.instId)
        for
          ctorInstId <- instIds
          case path@(pathTo :+ refedFun) <- ctorInstId.inits
          // skip synthesized instIds — those rewrite in-place
          if !collector.synthesizedInstIdToFunSym.contains(path)
        do mkNewPolyFnSyms(path, refedFun)
      case FinalDestMatch(dest, sels) =>
        val ctorInfo = solver.fusingCtorInfo(ctor)

        // create poly fun syms
        for
          ctorInstId <- List(ctor.instId, dest.instId)
          case path@(pathTo :+ refedFun) <- ctorInstId.inits
          // skip synthesized instIds — those rewrite in-place
          if !collector.synthesizedInstIdToFunSym.contains(path)
        do mkNewPolyFnSyms(path, refedFun)
        
        // create branch sel syms
        val fieldSym = MutMap.empty[SelField, VarSymbol]
        for sel <- sels.toList.sortBy(_._1) do
          branchSelSyms.getOrElseUpdate(
            sel,
            locally:
              val selInfo = solver.fusingDtorInfo(sel).asInstanceOf[FieldSel]
              val clsNme = selInfo.selectsFrom.ctorClsName
              fieldSym.getOrElseUpdate(
                selInfo.field,
                new VarSymbol(Tree.Ident(s"${clsNme}_${selInfo.field.fieldName}")))
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
            val branchName = whichBranch.fold("_dflt")(c => s"_${c.ctorClsName}")
            val scrutName = dest._1.getReferredSym.nme
            val branchFnNme = s"${dest.instId.mkFunName}$$$scrutName$branchName"
            new BlockMemberSymbol(branchFnNme, Nil, true)
            -> new TermSymbol(Fun, N, Tree.Ident(branchFnNme))
        )
        // compute the function parameters corresponding to ctor fields of branch funs
        branchFunParamFieldSyms.getOrElseUpdate(
          destBranchId,
          locally:
            val completeArgs: Ls[SelField] = ctorInfo.args.unzip._1
            val selsInfos: Map[SelField, CtorDtorId] = sels
              .iterator
              .map: sel =>
                solver.fusingDtorInfo(sel).asInstanceOf[FieldSel].field -> sel
              .toMap
            completeArgs.map: selField =>
              selsInfos.get(selField) match
              case Some(selId) => branchSelSyms(selId)
              case None => VarSymbol(Tree.Ident(s"_${selField.fieldName}"))
        )
        
        val (parents, _) = getParentLabelOrMatchesAndRestBefore(dest.exprId)
        for needRest <- Iterator.single(pre.res.matchScrutToMatchBlock(dest._1)) ++ parents do
          val (matchOrLabelId, nme) = needRest match
            case Match(scrut, arms, dflt, rest) => scrut.uid -> scrut.uid.getReferredSym.nme
            case Label(label, loop, body, rest) => label -> label.nme
          val restFunId = matchOrLabelId.withInstId(dest.instId)
          restFunSyms.getOrElseUpdate(
            restFunId,
            locally:
              val restFunName = dest.instId.mkFunName + s"$$${nme}_rest"
              new BlockMemberSymbol(restFunName, Nil, true)
              -> new TermSymbol(Fun, N, Tree.Ident(restFunName))
          )
          val (ps, restBeforeParent) = getParentLabelOrMatchesAndRestBefore(matchOrLabelId)
          restOriginalBodiesAndParentRest.getOrElseUpdate(
            matchOrLabelId,
            restBeforeParent
            -> ps.nextOption().map:
              case Match(scrut, arms, dflt, rest) => scrut.uid
              case Label(label, loop, body, rest) => label
          )
        
        // compute the complete deforestable branch body of a fusing match
        branchOriginalBodies.getOrElseUpdate(
          dest._1 -> whichBranch,
          whichBranchPreBody
        )
  }
  
  // compute free vars after we know new symbols
  val dtorBranchFnFvs = MutMap.empty[CtorDtorId, Ls[Symbol]]
  val restFnFvs = MutMap.empty[RestFunId, Ls[Symbol]]
  locally {
    val allBranchesOfDtor = branchFunSyms.keys.groupBy(_._1)
    extension (b: Block)
      // ctx should be the branch fun parameters corresponding to ctor fields 
      def deforestFreeVars(
        ctx: collection.Set[Symbol],
        instId: InstantiationId
      ): collection.Set[Symbol] =
        val traverser = new FreeVarTraverser(ctx, instId)
        traverser.applyBlock(b)
        traverser.freeVars
        
    class FreeVarTraverser(ctx: collection.Set[Symbol], instId: InstantiationId) extends BlockTraverser:
      extension (resId: ResultId) def concreteId = ConcreteId(resId, instId)
      val inCtx = MutSet.from[Symbol]:
        ctx
        ++ newPolyFnSyms.values.flatMap(_.values.unzip._1)
        ++ branchFunSyms.values.unzip._1
        ++ eState.builtinOpsMap.values
        ++ (eState.globalThisSymbol :: eState.runtimeSymbol :: eState.noSymbol :: Nil)
        ++ locally:
          pre.pgrm.main match
          case Scoped(syms, _) => syms
          case _ => Nil
      val freeVars = MutSet.empty[Symbol]
      
      private def handleTrackableSel(s: Result) =
        val toBeSubstSymbol = branchSelSyms(s.uid.concreteId)
        if !inCtx(toBeSubstSymbol) then freeVars.add(toBeSubstSymbol)
      
      override def applyValue(v: Value): Unit =
        v match
        case Value.Ref(l, disamb) if !inCtx(l) && l.asClsLike.isEmpty => freeVars.add(l)
        case _ => super.applyValue(v)
      
      override def applyResult(r: Result): Unit =
        r match
        case s@TrackableSelect(_, _, _) if branchSelSyms.isDefinedAt(s.uid.concreteId) =>
          handleTrackableSel(s)
        case Lambda(params, body) =>
          for p <- params.allParams do inCtx.add(p.sym)
          applyBlock(body)
          for p <- params.allParams do inCtx.remove(p.sym)
        case _ => super.applyResult(r)
      
      override def applyPath(p: Path): Unit =
        p match
        case s@TrackableSelect(_, _, _) if branchSelSyms.isDefinedAt(s.uid.concreteId) =>
          handleTrackableSel(s)
        case _ => super.applyPath(p)
      
      override def applyBlock(b: Block): Unit =
        b match
        case m: Match if solver.finalDtorSrcs.isDefinedAt(m.scrut.uid.concreteId) =>
          for
            fv <- fvsForDtor(m.scrut.uid.concreteId)
            if !inCtx(fv)
          do freeVars.add(fv)
          super.applyPath(m.scrut)
        case Assign(lhs, rhs, rest) =>
          if !inCtx(lhs) then freeVars.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case Scoped(syms, body) =>
          for s <- syms do inCtx.add(s)
          applyBlock(body)
          for s <- syms do inCtx.remove(s)
        case _ => super.applyBlock(b)
      
      override def applyDefn(defn: Defn): Unit =
        defn match
        case fDef: FunDefn =>
          inCtx.add(fDef.sym)
          for p <- fDef.params.flatMap(_.allParams) do inCtx.add(p.sym)
          applyBlock(fDef.body)
          for p <- fDef.params.flatMap(_.allParams) do inCtx.remove(p.sym)
        case cDef: ClsLikeDefn =>
          inCtx.add(cDef.sym)
          val ps = (cDef.auxParams ++ cDef.paramsOpt).flatMap(_.params).map(_.sym)
          for p <- ps do inCtx.add(p)
          super.applyDefn(cDef)
          for p <- ps do inCtx.remove(p)
        case vDef: ValDefn =>
          inCtx.add(vDef.sym)
          super.applyDefn(defn)
    end FreeVarTraverser
    
    def fvsForDtor(dtorId: CtorDtorId): Ls[Symbol] =
      dtorBranchFnFvs.get(dtorId) match
      case Some(fvs) => fvs
      case None =>
        val fvsOfBranches = allBranchesOfDtor(dtorId)
          .flatMap: branchId =>
            branchOriginalBodies(branchId._1._1 -> branchId._2)
              .deforestFreeVars(
                branchFunParamFieldSyms(branchId).toSet,
                branchId._1._2)
          .toSortedSet(using Ordering.by[Symbol, Uid[Symbol]](_.uid))
          .toList
        val fvsOfRest = fvsForRest(dtorId)
        val fvs = fvsOfBranches ++ fvsOfRest
        dtorBranchFnFvs(dtorId) = fvs
        fvs
    
    def fvsForRest(restFunId: RestFunId): Ls[Symbol] =
      restFnFvs.get(restFunId) match
      case Some(fvs) => fvs
      case None =>
        val instId = restFunId.getInstId
        val (restBody, parentRest) = restOriginalBodiesAndParentRest(restFunId.withoutInstId)
        val fvOfRestBody = restBody.deforestFreeVars(Set.empty, restFunId.getInstId).toList.sortBy(_.uid)
        val fvOfRestParent = parentRest.fold(List.empty)(pr => fvsForRest(pr.withInstId(instId)))
        val fvs = fvOfRestBody ++ fvOfRestParent
        restFnFvs(restFunId) = fvs
        fvs
    
    allBranchesOfDtor.keysIterator.foreach(fvsForDtor)
  }
  
  // compute new program body
  val newBody =
    
    extension (a: Symbol) def toValueRef =
      a match
      case bms: BlockMemberSymbol => Value.Ref(bms, bms.tsym)
      case _ => Value.Ref(a, N)
    def mkReturnCall(target: (BlockMemberSymbol, TermSymbol), args: Ls[Symbol]): Block =
      Return(Call(
        Value.Ref(target._1, S(target._2)),
        args.map(a => Arg(N, a.toValueRef)) ne_:: Nil
      )(true, false, false), false)
    
    class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
      extension (resId: ResultId) def concreteId = ConcreteId(resId, instId)
      
      private def ctorLamFvs(ctorId: CtorDtorId): Ls[VarSymbol] =
        // only for ctors that are fused with a match
        val dtorId = solver.finalCtorDests(ctorId).asInstanceOf[FinalDestMatch].dtor
        dtorBranchFnFvs(dtorId).map(s => new VarSymbol(Tree.Ident(s"fv_ctorLam_${s.nme}")))
      
      private def newRefId(refId: ResultId, refSym: TermSymbol) =
        instId match
        case Nil => refId :: Nil
        case pathTo :+ called =>
          val lastRefedSymbol = called.getReferredFun.get
          val funToSccRepMap = collector.funToSccRep
          (funToSccRepMap(lastRefedSymbol), funToSccRepMap(refSym)) match
            case (Some(a), Some(b)) if a is b => instId
            case _ => instId :+ refId
        case _ => die
      override def applyResult(r: Result)(k: Result => Block): Block =
        r match
        case s@TrackableSelect(from, _, _) =>
          if branchSelSyms.isDefinedAt(s.uid.concreteId) then
            k(Value.Ref(branchSelSyms(s.uid.concreteId)))
          else if solver.finalDtorSrcs.contains(s.uid.concreteId) then
            applyPath(from)(k)
          else
            super.applyResult(r)(k)
        case ctor@CtorCall(cls, args) =>
          def mkCtorFieldSyms(ctorDtorId: CtorDtorId): Ls[TempSymbol] =
            val ctorInfo = solver.fusingCtorInfo(ctorDtorId)
            val clsNme = ctorInfo.ctor.ctorClsName
            ctorInfo.args.unzip._1.map: f =>
              new TempSymbol(N, s"${clsNme}_${f.fieldName}")
          end mkCtorFieldSyms
          
          solver.finalCtorDests.get(ctor.uid.concreteId) match
          case None => super.applyResult(ctor)(k)
          case Some(FinalDestSel(_, field)) =>
            val ctorInfo = solver.fusingCtorInfo(ctor.uid.concreteId)
            val idx = ctorInfo.args.unzip._1.indexOf(field)
            val fieldSyms = mkCtorFieldSyms(ctor.uid.concreteId)
            args.zip(fieldSyms).foldRight(k(Value.Ref(fieldSyms(idx)))):
              case (Arg(N, a) -> s, rest) =>
                applyPath(a): fusedField =>
                  Scoped(Set.single(s), Assign(s, fusedField, rest))
              case _ => TODO("spread args are not supported")
          case Some(_: FinalDestMatch) =>
            val fieldSyms = mkCtorFieldSyms(ctor.uid.concreteId)
            val (branchBms, branchTermSym) = branchFunSyms(ctorWhichBranch(ctor.uid.concreteId))
            val ctorLamParams = ctorLamFvs(ctor.uid.concreteId)
            val callBranchFun =
              Lambda(
                ctorLamParams.asParamList,
                mkReturnCall((branchBms, branchTermSym), ctorLamParams ++ fieldSyms))
            args.zip(fieldSyms).foldRight(k(callBranchFun)):
              case (Arg(N, a) -> fieldSym, rest) =>
                applyPath(a): fusedField =>
                  Scoped(Set.single(fieldSym), Assign(fieldSym, fusedField, rest))
              case _ => TODO("spread args are not supported")
        case _ => super.applyResult(r)(k)
      
      override def applyPath(p: Path)(k: Path => Block): Block =
        p match
        case ref@FunRef(f) if newPolyFnSyms.isDefinedAt(newRefId(ref.uid, f)) =>
          val (bms, tSym) = newPolyFnSyms(newRefId(ref.uid, f))(f)
          k(Value.Ref(bms, S(tSym)))
        case ctor@CtorCall(_, args) if solver.finalCtorDests.isDefinedAt(ctor.uid.concreteId) =>
          assert(args.isEmpty)
          val (branchBms, branchTermSym) = branchFunSyms(ctorWhichBranch(ctor.uid.concreteId))
          val ctorLamParams = ctorLamFvs(ctor.uid.concreteId)
          val lambdaSym = new TempSymbol(N, "deforest$lam")
          Scoped(
            Set.single(lambdaSym),
            Assign(
              lambdaSym,
              Lambda(
                ctorLamParams.asParamList,
                mkReturnCall((branchBms, branchTermSym), ctorLamParams)),
              k(Value.Ref(lambdaSym, N)))
          )
        case s@TrackableSelect(from, _, _) =>
          if branchSelSyms.isDefinedAt(s.uid.concreteId) then
            k(Value.Ref(branchSelSyms(s.uid.concreteId)))
          else if solver.finalDtorSrcs.contains(s.uid.concreteId) then
            applyPath(from)(k)
          else
            super.applyPath(s)(k)
        case _ => super.applyPath(p)(k)
      
      override def applyBlock(b: Block): Block =
        b match
        case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.concreteId) =>
          val callWithFvs = dtorBranchFnFvs(scrut.uid.concreteId)
          applyPath(scrut): newScrut =>
            Return(
              Call(newScrut, callWithFvs.map(s => Arg(N, s.toValueRef)) ne_:: Nil)(true, false, false),
              false)
        case Break(label) =>
          val labelRestFunId = label.withInstId(instId)
          restFunSyms.get(labelRestFunId) match
          case None => super.applyBlock(b)
          case Some(labelRestFunSym) =>
            val labelRestFunFvs = restFnFvs(labelRestFunId)
            mkReturnCall(labelRestFunSym, labelRestFunFvs)
        case Return(res, true) => super.applyBlock(Return(res, false))
        case _ => super.applyBlock(b)
    end Rewriter
    
    class RefreshSymbol(existingMapping: Map[Symbol, Symbol]) extends SymbolRefresher(existingMapping):
      override def applyScopedBlock(b: Block): Block =
        b match
        case Scoped(syms, body) =>
          syms.foreach: sym =>
            sym match
              case bms: BlockMemberSymbol =>
                assert(bms.tsym.forall(_.owner.isEmpty))
              case _ =>
        case _ =>
        super.applyScopedBlock(b)
      override def applyBlock(b: Block): Block =
        b match
        case Label(label, loop, body, rest) =>
          assert(!loop)
        case Continue(label) => TODO("unsupported `continue` instruction during rewriting")
        case _ =>
        super.applyBlock(b)
      override def applyValue(v: Value)(k: Value => Block): Block = v match
        case Value.Ref(l, x) =>
          pre.res.modSymToBms.get(l) match
            case Some(bms) =>
              k(Value.Ref(bms, l.asMod))
            case None => super.applyValue(v)(k)
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
        val refreshParamMap = MutMap.empty[VarSymbol, VarSymbol]
        val refreshedParams = fDefn.params.map: pl =>
          ParamList(
            pl.flags,
            pl.params.map: p =>
              val newSym = new VarSymbol(Tree.Ident(p.sym.name))
              refreshParamMap(p.sym) = newSym
              Param(p.flags, newSym, p.sign, p.modulefulness),
            pl.restParam)
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshParamMap.toMap).applyBlock(transformedBody)
        FunDefn(
          N, bms, tSym, refreshedParams,
          bodyWithCorrectSymbols)(N, fDefn.annotations)
    end newPolyFuns
    
    val newBranchFuns =
      for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
        val instId = dtorId.getInstId
        val ogBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
        val restFunSym = restFunSyms(dtorId)
        val restFunArgs = restFnFvs(dtorId)
        val actualBody = Begin(
          new Rewriter(instId).applyBlock(ogBody),
          mkReturnCall(restFunSym, restFunArgs))
        val refreshedFvSymbols = dtorBranchFnFvs(branchId._1).map(s => s -> new VarSymbol(Tree.Ident(s"fv_${s.nme}")))
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshedFvSymbols.toMap).applyBlock(actualBody)
        FunDefn(N, bms, tSym,
          (refreshedFvSymbols.unzip._2 ++ branchFunParamFieldSyms(branchId)).asParamList :: Nil,
          bodyWithCorrectSymbols
        )(N, annotations = Nil)
    end newBranchFuns
    
    val newRestFuns =
      for (restFunId, (bms, tsym)) <- restFunSyms yield
        val instId = restFunId.getInstId
        val (ogBody, parent) = restOriginalBodiesAndParentRest(restFunId.withoutInstId)
        val transformedOgBody = new Rewriter(instId).applyBlock(ogBody)
        val actualBody = parent match
          case Some(parentRestId) =>
            val parentRestFunId = parentRestId.withInstId(instId)
            val parentFunSym = restFunSyms(parentRestFunId)
            val parentFunFvs = restFnFvs(parentRestFunId)
            Begin(
              transformedOgBody,
              mkReturnCall(parentFunSym, parentFunFvs))
          case None =>
            Begin(transformedOgBody, Return(Value.Lit(Tree.UnitLit(true)), false))
        val refreshedFvSymbols = restFnFvs(restFunId).map(s => s -> new VarSymbol(Tree.Ident(s"fv_${s.nme}")))
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshedFvSymbols.toMap).applyBlock(actualBody)
        FunDefn(N, bms, tsym, refreshedFvSymbols.unzip._2.asParamList :: Nil, bodyWithCorrectSymbols)(N, annotations = Nil)
    end newRestFuns

    val inplaceRewrittenFunBodies = Map.from[TermSymbol, Block]:
      for (selfInstId, funSym) <- collector.synthesizedInstIdToFunSym yield
        val fDefn = pre.res.funSymToFunDefn(funSym)
        funSym -> new Rewriter(selfInstId).applyBlock(fDefn.body)

    val newMainBody =
      object mainRewriter extends Rewriter(Nil):
        override def applyFunDefn(fun: FunDefn): FunDefn =
          inplaceRewrittenFunBodies.get(fun.dSym) match
            case Some(rewrittenBody) =>
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, rewrittenBody)(fun.configOverride, fun.annotations)
            case None => super.applyFunDefn(fun)
      object implicitRetPass extends BlockTransformerShallow(_symSubst):
        override def applyBlock(b: Block): Block = b match
          case Return(res, false) => Return(res, true)
          case _ => super.applyBlock(b)
      Scoped(
        Set.from(newPolyFuns.map(_.sym) ++ newBranchFuns.map(_.sym) ++ newRestFuns.map(_.sym)),
        implicitRetPass.applyBlock(mainRewriter.applyBlock(pre.pgrm.main)))
    
    (newPolyFuns ++ newBranchFuns ++ newRestFuns).foldRight(newMainBody): (fdef, rest) =>
      Define(fdef, rest)
    
  end newBody
  
end DeforestRewriter

