package hkmc2
package codegen
package deforest

import utils.*
import hkmc2.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, LinkedHashSet, Buffer}
import hkmc2.syntax.Fun
import hkmc2.codegen.flowAnalysis.*



class DeforestRewriter(val solver: DeforestFusionSolver, additionalTopLevelSymbols: Set[LocalVarSymbol])(using Raise)
  extends PolyInstantiationRewrite(solver.constraintSolver):
  
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
    ParamList(ParamListFlags.empty, vs.map(Param.simple), N)(N)
  extension (c: CtorCls) def ctorClsName: String = c match
    case cls: ClassLikeSymbol => cls.nme
    case n: Int => s"tup$n"
  extension (f: SelField) def fieldName: String = f match
    case tSym: TermSymbol => tSym.nme
    case n: Int => n.toString
  extension (f: SelField) def erasedFieldType: Opt[ErasedValueType] = f match
    case tSym: TermSymbol => tSym.mapErasedValueType
    case _: Int => N

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

  private val PrivateModifier = Annot.Modifier(syntax.Keyword.`private`)(N)
  private val AffineAnnotForBranchFns = Annot.Affine(1)(N)
  
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
  
  // compute new symbols for branch body functions and rest functions
  locally {
    for case (ctor, finalDest) <- solver.finalCtorDests do
      finalDest match
      case FinalDestSel(dtors, field) => ()
      case FinalDestMatch(dest, sels) =>
        val ctorInfo = solver.fusingCtorInfo(ctor)
        // create branch sel syms
        val fieldSym = MutMap.empty[SelField, VarSymbol]
        for sel <- sels.toList.sortBy(_._1.uid) do
          branchSelSyms.getOrElseUpdate(
            sel,
            locally:
              val selInfo = solver.fusingDtorInfo(sel).asInstanceOf[FieldSel]
              val clsNme = selInfo.selectsFrom.ctorClsName
              fieldSym.getOrElseUpdate(
                selInfo.field,
                new VarSymbol(
                  Tree.Ident(s"${clsNme}_${selInfo.field.fieldName}"),
                  erasedType = selInfo.field.erasedFieldType))
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
            -> new TermSymbol(Fun, N, Tree.Ident(branchFnNme), erasedType = N)
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
              case None => VarSymbol(Tree.Ident(s"_${selField.fieldName}"), erasedType = selField.erasedFieldType)
        )
        
        val (parents, _) = getParentLabelOrMatchesAndRestBefore(dest.exprId)
        for needRest <- Iterator.single(pre.res.matchScrutToMatchBlock(dest._1)) ++ parents do
          val (matchOrLabelId, nme): MatchOrLabelId -> Str = needRest match
            case Match(scrut, arms, dflt, rest) => scrut.uid -> scrut.uid.getReferredSym.nme
            case Label(label, loop, body, rest) => label -> label.nme
          val restFunId = matchOrLabelId.withInstId(dest.instId)
          restFunSyms.getOrElseUpdate(
            restFunId,
            locally:
              val restFunName = dest.instId.mkFunName + s"$$${nme}_rest"
              new BlockMemberSymbol(restFunName, Nil, true)
              -> new TermSymbol(Fun, N, Tree.Ident(restFunName), erasedType = N)
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
  val dtorBranchFnFvs = MutMap.empty[CtorDtorId, Ls[LocalVarSymbol]]
  val restFnFvs = MutMap.empty[RestFunId, Ls[LocalVarSymbol]]
  locally {
    val allBranchesOfDtor = branchFunSyms.keys.groupBy(_._1)
    extension (b: Block)
      // ctx should be the branch fun parameters corresponding to ctor fields 
      def deforestFreeVars(
        ctx: collection.Set[LocalVarSymbol],
        instId: InstantiationId
      ): LinkedHashSet[LocalVarSymbol] =
        val traverser = new FreeVarTraverser(ctx, instId)
        traverser.applyBlock(b)
        traverser.freeVars
        
    class FreeVarTraverser(ctx: collection.Set[LocalVarSymbol], instId: InstantiationId) extends BlockTraverser:
      extension (resId: ResultId) def concreteId = ConcreteId(resId, instId)
      val inCtx = MutSet.from[LocalVarSymbol]:
        ctx
        ++ (eState.runtimeSymbol :: Nil : Ls[LocalVarSymbol])
        ++ pre.pgrm.main.match
          case Scoped(syms, _) => syms.iterator.collect{case s: LocalVarSymbol => s}
          case _ => Nil
        // for diff tests
        ++ additionalTopLevelSymbols
      val freeVars = LinkedHashSet.empty[LocalVarSymbol]
      
      private def handleTrackableSel(s: Result) =
        val toBeSubstSymbol = branchSelSyms(s.uid.concreteId)
        if !inCtx(toBeSubstSymbol) then freeVars.add(toBeSubstSymbol)
      
      override def applyValue(v: Value): Unit =
        v match
        case Value.SimpleRef(l) =>
          l match
          case l: LocalVarSymbol => if !inCtx(l) then freeVars.add(l)
          case _: BuiltinSymbol => super.applyValue(v)
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
        case Assign(lhs: LocalVarSymbol, rhs, rest) =>
          if !inCtx(lhs) then freeVars.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case Scoped(syms, body) =>
          for case s: LocalVarSymbol <- syms do inCtx.add(s)
          applyBlock(body)
          for case s: LocalVarSymbol <- syms do inCtx.remove(s)
        case _ => super.applyBlock(b)
      
      override def applyDefn(defn: Defn): Unit =
        softAssert(false, s"deforestation copying the definition ${defn.sym.nme}")
    end FreeVarTraverser
    
    def fvsForDtor(dtorId: CtorDtorId): Ls[LocalVarSymbol] =
      dtorBranchFnFvs.get(dtorId) match
      case Some(fvs) => fvs
      case None =>
        val fvsOfBranches = LinkedHashSet.empty[LocalVarSymbol]
        for branchId <- allBranchesOfDtor(dtorId) do
          fvsOfBranches.addAll:
            branchOriginalBodies(branchId._1._1 -> branchId._2)
              .deforestFreeVars(
                branchFunParamFieldSyms(branchId).toSet,
                branchId._1._2)
        val fvsOfRest = fvsForRest(dtorId)
        val fvs = fvsOfBranches.addAll(fvsOfRest).toList
        dtorBranchFnFvs(dtorId) = fvs
        fvs
    
    def fvsForRest(restFunId: RestFunId): Ls[LocalVarSymbol] =
      restFnFvs.get(restFunId) match
      case Some(fvs) => fvs
      case None =>
        val instId = restFunId.getInstId
        val (restBody, parentRest) = restOriginalBodiesAndParentRest(restFunId.withoutInstId)
        val fvOfRestBody = restBody.deforestFreeVars(Set.empty, restFunId.getInstId)
        val fvOfRestParent = parentRest.fold(List.empty)(pr => fvsForRest(pr.withInstId(instId)))
        val fvs = (fvOfRestBody.iterator ++ fvOfRestParent.iterator.filterNot(fvOfRestBody)).toList
        restFnFvs(restFunId) = fvs
        fvs
    
    allBranchesOfDtor.keysIterator.foreach(fvsForDtor)
  }

  // Rewrites the program under a specific instantiation id
  // from the polymorphic analysis
  protected class Rewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[LocalVarSymbol, LocalVarSymbol]]) extends InstantiationRewriter(instId, refreshSymbolMappingForCopy):
    
    def rewriteFunDefn(fun: FunDefn): RewrittenFunDefn =
      fun.params.mapConserve(applyParamList) -> applyBlock(fun.body)
    
    // calls `fun` with possibly remapped `args`
    def mkCall(fun: Path, args: Ls[LocalVarSymbol])(k: Result => Block): Block =
      applyArgs(args.map(s => Arg(N, s.asPath))): args2 =>
        k(Call(fun, args2 ne_:: Nil)(CallMetadata.defaultMlsFun, N))
    
    override def applyResult(r: Result)(k: Result => Block): Block =
      r match
      case s@TrackableSelect(from, _, _) =>
        if branchSelSyms.isDefinedAt(s.uid.concreteId) then
          k(branchSelSyms(s.uid.concreteId).subst.asSimpleRef)
        else if solver.finalDtorSrcs.contains(s.uid.concreteId) then
          applyPath(from)(k)
        else
          super.applyResult(r)(k)
      case ctor@CtorProducer(cls, args, _) =>
        def mkCtorFieldSyms(ctorDtorId: CtorDtorId): Ls[TempSymbol] =
          val ctorInfo = solver.fusingCtorInfo(ctorDtorId)
          val clsNme = ctorInfo.ctor.ctorClsName
          ctorInfo.args.unzip._1.map: f =>
            new TempSymbol(N, erasedType = f.erasedFieldType, s"${clsNme}_${f.fieldName}")
        end mkCtorFieldSyms
        
        solver.finalCtorDests.get(ctor.uid.concreteId) match
        case None => super.applyResult(ctor)(k)
        case Some(FinalDestSel(_, field)) =>
          val ctorInfo = solver.fusingCtorInfo(ctor.uid.concreteId)
          val idx = ctorInfo.args.unzip._1.indexOf(field)
          val fieldSyms = mkCtorFieldSyms(ctor.uid.concreteId)
          args.zip(fieldSyms).foldRight(k(fieldSyms(idx).asSimpleRef)):
            case (Arg(N, a) -> s, rest) =>
              applyPath(a): fusedField =>
                Scoped(Set.single(s), Assign(s, fusedField, rest))
            case _ => TODO("spread args are not supported")
        case Some(_: FinalDestMatch) =>
          val fieldSyms = mkCtorFieldSyms(ctor.uid.concreteId)
          val (branchFunBms, branchFunTSym) = branchFunSyms(ctorWhichBranch(ctor.uid.concreteId))
          args.zip(fieldSyms).foldRight(mkCall(branchFunBms.asMemberRef(branchFunTSym), fieldSyms)(k)):
            case (Arg(N, a) -> fieldSym, rest) =>
              applyPath(a): fusedField =>
                Scoped(Set.single(fieldSym), Assign(fieldSym, fusedField, rest))
            case _ => TODO("spread args are not supported")
      case _ => super.applyResult(r)(k)
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      p match
      case PolyFnRef(specializedRef) => k(specializedRef)
      case ctor@CtorProducer(_, args, _) if solver.finalCtorDests.isDefinedAt(ctor.uid.concreteId) =>
        assert(args.isEmpty)
        val (branchFunBms, branchFunTSym) = branchFunSyms(ctorWhichBranch(ctor.uid.concreteId))
        val lambdaSym = new TempSymbol(N, erasedType = N, "deforest$lam")
        mkCall(branchFunBms.asMemberRef(branchFunTSym), Nil): callBranchFun =>
          Scoped(
            Set.single(lambdaSym),
            Assign(
              lambdaSym,
              callBranchFun,
              k(lambdaSym.asSimpleRef)
          ))
      case s@TrackableSelect(from, _, _) =>
        if branchSelSyms.isDefinedAt(s.uid.concreteId) then
          k(branchSelSyms(s.uid.concreteId).subst.asSimpleRef)
        else if solver.finalDtorSrcs.contains(s.uid.concreteId) then
          applyPath(from)(k)
        else
          super.applyPath(s)(k)
      case _ => super.applyPath(p)(k)
    
    // a free block member symbol of an extracted part becomes an `fv_` parameter, which needs a different node
    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case Value.This(l) if refreshSymbolMappingForCopy.isDefined =>
        pre.res.modSymToBms.get(l) match
        case S(bms) => k(bms.asMemberRef(l.asMod.get))
        case N => super.applyValue(v)(k)
      case _ => super.applyValue(v)(k)
      
    override def applyBlock(b: Block): Block =
      b match
      case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.concreteId) =>
        applyPath(scrut): newScrut =>
          mkCall(newScrut, dtorBranchFnFvs(scrut.uid.concreteId))(Return(_))
      case Break(label) =>
        val labelRestFunId = label.withInstId(instId)
        restFunSyms.get(labelRestFunId) match
        case None => super.applyBlock(b)
        case Some((bms, tSym)) =>
          mkCall(bms.asMemberRef(tSym), restFnFvs(labelRestFunId))(Return(_))
      // copying a definition would need fresh symbols for it; lifting removes the nested ones beforehand
      case Define(defn, _) if refreshSymbolMappingForCopy.isDefined =>
        softAssert(false, s"deforestation copying the definition ${defn.sym.nme}")
        b
      case Label(sym, true, _, _) if refreshSymbolMappingForCopy.isDefined =>
        softAssert(false, s"unsupported loop $sym during rewriting")
        b
      case Continue(sym) if refreshSymbolMappingForCopy.isDefined =>
        softAssert(false, s"unsupported `continue` to $sym during rewriting")
        b
      case _ => super.applyBlock(b)
  end Rewriter
  

  
  // ====== start: implements the abstract members of `PolyInstantiationRewrite` ======
  def solvers: Iterable[FlowAnalysisSolverResult] = solver :: Nil
  
  def mkRewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[LocalVarSymbol, LocalVarSymbol]]) = new Rewriter(instId, refreshSymbolMappingForCopy)
  
  def otherNewFunDefns: Iterable[FunDefn] =
    
    // the rewriter of an extracted part (branch body functions and match rest functions),
    // whose free variables `fvs` become the `fv_` parameters it returns
    def mkExtractedBodyRewriter(instId: InstantiationId, body: Block, fvs: Ls[LocalVarSymbol]): (Rewriter, Ls[VarSymbol]) =
      val fvParams = fvs.map(s => new VarSymbol(Tree.Ident(s"fv_${s.nme}"), erasedType = s.mapErasedValueType))
      mkCopyRewriter(instId, Nil, body, Map.from(fvs.iterator.zip(fvParams))) -> fvParams
  
    // Functions for fused match branches; each runs one arm and then its rest
    val newBranchFuns =
      for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
        val instId = dtorId.getInstId
        val ogBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
        val (restFunBms, restFunTSym) = restFunSyms(dtorId)
        val (rewriter, fvParams) = mkExtractedBodyRewriter(instId, ogBody, dtorBranchFnFvs(branchId._1))
        val actualBody = Begin(
          rewriter.applyBlock(ogBody),
          rewriter.mkCall(restFunBms.asMemberRef(restFunTSym), restFnFvs(dtorId))(Return(_)))
        FunDefn(N, bms, tSym,
          branchFunParamFieldSyms(branchId).asParamList :: fvParams.asParamList :: Nil,
          actualBody
        )(N, annotations = AffineAnnotForBranchFns :: PrivateModifier :: Nil)
    end newBranchFuns
    
    // Continuation functions for the code after fused matches or labels
    val newRestFuns =
      for (restFunId, (bms, tsym)) <- restFunSyms yield
        val instId = restFunId.getInstId
        val (ogBody, parent) = restOriginalBodiesAndParentRest(restFunId.withoutInstId)
        val (rewriter, fvParams) = mkExtractedBodyRewriter(instId, ogBody, restFnFvs(restFunId))
        val transformedOgBody = rewriter.applyBlock(ogBody)
        val actualBody = parent match
          case Some(parentRestId) =>
            val parentRestFunId = parentRestId.withInstId(instId)
            val (parentFunBms, parentFunTSym) = restFunSyms(parentRestFunId)
            val parentFunFvs = restFnFvs(parentRestFunId)
            Begin(
              transformedOgBody,
              rewriter.mkCall(parentFunBms.asMemberRef(parentFunTSym), parentFunFvs)(Return(_)))
          case None =>
            Begin(transformedOgBody, Return(Value.Lit(Tree.UnitLit(true))(N)))
        FunDefn(N, bms, tsym, fvParams.asParamList :: Nil, actualBody)(N, annotations = PrivateModifier :: Nil)
    end newRestFuns
    
    newBranchFuns ++ newRestFuns
    
  end otherNewFunDefns
  
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]) =
    new Rewriter(Nil, N):
      override def applyFunDefn(fun: FunDefn): FunDefn =
        rewrittenInPlace.get(fun.dSym) match
          case Some((params, rewrittenBody)) =>
            // deforest never changes fun params in place
            assert(params is fun.params)
            FunDefn(fun.owner, fun.sym, fun.dSym, params, rewrittenBody)(fun.configOverride, fun.annotations)
          case None => super.applyFunDefn(fun)
  // ====== end: implements the abstract members of `PolyInstantiationRewrite` ======
end DeforestRewriter
