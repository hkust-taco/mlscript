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
  import solver.FinalDestMatch
  import solver.FinalDestSel
  given tl: TraceLogger = solver.tl
  given dState: Deforest.State = solver.dState
  given eState: Elaborator.State = solver.collector.elabState
  given pre: DeforestPreAnalyzer = solver.preAnalyzer
  
  
  extension (restFunId: RestFunId) def withoutInstId: MatchOrLabelId =
    restFunId match
    case CtorDtorId(exprId, instId) => exprId
    case l: LabelId => l._1
  extension (restFunId: RestFunId) def getInstId = restFunId match
    case CtorDtorId(exprId, instId) => instId
    case l: LabelId => l._2
  extension (matchOrLabelId: MatchOrLabelId) def withInstId(instId: InstantiationId): RestFunId =
    matchOrLabelId match
    case l: LabelSymbol => l -> instId
    case scrutId => CtorDtorId(scrutId.asInstanceOf[ResultId], instId)
  extension (vs: Ls[VarSymbol])
    def asParamList: ParamList =
      ParamList(ParamListFlags.empty, vs.map(Param.simple), N)
  
  private val _symSubst = new SymbolSubst()
  
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
    end mkNewPolyFnSyms
    
    for case (ctor, finalDest) <- solver.finalCtorDests do
      finalDest match
      case FinalDestSel(dtors, field) =>
        // create poly fun syms
        val instIds = (dtors + ctor).toList.sortBy(_.exprId).map(_.instId)
        for
          ctorInstId <- instIds
          case path@(pathTo :+ refedFun) <- ctorInstId.inits
        do mkNewPolyFnSyms(path, refedFun)
      case FinalDestMatch(dest, sels) =>
        val ctorInfo = solver.fusingCtorInfo(ctor)

        // create poly fun syms
        for
          ctorInstId <- List(ctor.instId, dest.instId)
          case path@(pathTo :+ refedFun) <- ctorInstId.inits
        do mkNewPolyFnSyms(path, refedFun)
        
        // create branch sel syms
        val fieldSym = MutMap.empty[SelField, VarSymbol]
        for sel <- sels.toList.sortBy(_._1) do
          branchSelSyms.getOrElseUpdate(
            sel,
            locally:
              val selInfo = solver.fusingDtorInfo(sel).asInstanceOf[FieldSel]
              val clsNme = selInfo.isSelFromCls match
                case cls: ClassSymbol => cls.name
                case n: Int => s"tup$n"
              fieldSym.getOrElseUpdate(
                selInfo.field,  
                selInfo.field match
                  case termSym: TermSymbol => new VarSymbol(Tree.Ident(s"${clsNme}_${termSym.nme}"))
                  case ith: Int => new VarSymbol(Tree.Ident(s"${clsNme}_$ith")))
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
              case None => selField match
                case n: Int => VarSymbol(Tree.Ident(s"_tup_${n}"))
                case tSym: TermSymbol => VarSymbol(Tree.Ident(s"_${tSym.name}"))
        )
        
        val (parents, _) = pre.res.getParentLabelOrMatchesAndRestBefore(dest.exprId)
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
          val (ps, restBeforeParent) = pre.res.getParentLabelOrMatchesAndRestBefore(matchOrLabelId)
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
      def deforestFreeVars(ctx: collection.Set[Symbol], instId: InstantiationId) =
        val traverser = new FreeVarTraverser(ctx, instId)
        traverser.applyBlock(b)
        traverser.freeVars.toSet.filter(s => s.asClsLike.isEmpty)
        
    class FreeVarTraverser(ctx: collection.Set[Symbol], instId: InstantiationId) extends BlockTraverser:
      extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
      val inCtx = MutSet.from[Symbol]:
        pre.b match
          case Scoped(syms, body) =>
            ctx
            ++ newPolyFnSyms.values.flatMap(_.values.unzip._1)
            ++ branchFunSyms.values.unzip._1
            ++ eState.builtinOpsMap.values
            ++ (eState.globalThisSymbol :: eState.runtimeSymbol :: Nil)
            ++ syms
          case _ => die
      val freeVars = MutSet.empty[Symbol]
      
      override def applyValue(v: Value): Unit =
        v match
        case Value.Ref(l, disamb) if !inCtx(l) => freeVars.add(l)
        case _ => super.applyValue(v)
      
      override def applyResult(r: Result): Unit =
        r match
        case s@DeforestTupSelect(_, _) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
          val toBeSubstSymbol = branchSelSyms(s.uid.toCtorDtorId)
          if !inCtx(toBeSubstSymbol) then freeVars.add(toBeSubstSymbol)
        case Lambda(params, body) =>
          for p <- params.allParams do inCtx.add(p.sym)
          applyBlock(body)
          for p <- params.allParams do inCtx.remove(p.sym)
        case _ => super.applyResult(r)
      
      override def applyPath(p: Path): Unit =
        p match
        case s@DeforestableSelect(sym: TermSymbol) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
          val toBeSubstSymbol = branchSelSyms(s.uid.toCtorDtorId)
          if !inCtx(toBeSubstSymbol) then freeVars.add(toBeSubstSymbol)
        case _ => super.applyPath(p)
      
      override def applyBlock(b: Block): Unit =
        b match
        case m: Match if solver.finalDtorSrcs.isDefinedAt(m.scrut.uid.toCtorDtorId) =>
          for
            fv <- fvsForDtor(m.scrut.uid.toCtorDtorId)
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
        case _: ClsLikeDefn => die
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
    class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
      extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
      
      private def ctorLamFvs(ctorId: CtorDtorId): Ls[VarSymbol] =
        // only for ctors that are fused with a match
        val dtorId = solver.finalCtorDests(ctorId).asInstanceOf[FinalDestMatch].dtor
        dtorBranchFnFvs(dtorId).map(s => new VarSymbol(Tree.Ident(s"fv_ctorLam_${s.nme}")))
      
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
        case ctor@CtorCall(cls, args) =>
          def mkCtorFieldSyms(ctorDtorId: CtorDtorId): Ls[TempSymbol] =
            val ctorInfo = solver.fusingCtorInfo(ctorDtorId)
            val clsNme = ctorInfo.ctor match
              case n: Int => s"tup$n"
              case c: (ClassSymbol | ModuleOrObjectSymbol) => c.name
            ctorInfo.args.unzip._1.map:
              case termSym: TermSymbol => new TempSymbol(N, s"${clsNme}_${termSym.nme}")
              case n: Int => new TempSymbol(N, s"${clsNme}_$n")
          end mkCtorFieldSyms
          
          solver.finalCtorDests.get(ctor.uid.toCtorDtorId) match
          case None => super.applyResult(ctor)(k)
          case Some(FinalDestSel(_, field)) =>
            val ctorInfo = solver.fusingCtorInfo(ctor.uid.toCtorDtorId)
            val idx = ctorInfo.args.unzip._1.indexOf(field)
            val fieldSyms = mkCtorFieldSyms(ctor.uid.toCtorDtorId)
            args.zip(fieldSyms).foldRight(k(Value.Ref(fieldSyms(idx)))):
              case (Arg(N, a) -> s, rest) =>
                applyPath(a): fusedField =>
                  Scoped(Set(s), Assign(s, fusedField, rest))
              case _ => die
          case Some(_: FinalDestMatch) =>
            val fieldSyms = mkCtorFieldSyms(ctor.uid.toCtorDtorId)
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
        case s@DeforestableSelect(sym: TermSymbol) =>
          if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) then
            assert(sym.k is ParamBind)
            k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
          else if solver.finalDtorSrcs.contains(s.uid.toCtorDtorId) then
            applyPath(s.qual)(k)
          else
            super.applyPath(p)(k)
        case _ => super.applyPath(p)(k)
      
      override def applyBlock(b: Block): Block =
        b match
        case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.toCtorDtorId) =>
          val callWithFvs = dtorBranchFnFvs(scrut.uid.toCtorDtorId)
          applyPath(scrut): newScrut =>
            Return(
              Call(newScrut, callWithFvs.map(s => Arg(N, Value.Ref(s, N))))(true, false, false),
              false)
        case Break(label) =>
          val labelRestFunId = label.withInstId(instId)
          restFunSyms.get(labelRestFunId) match
          case None => super.applyBlock(b)
          case Some(labelRestFunSym) => 
            val labelRestFunFvs = restFnFvs(labelRestFunId)
            Return(
              Call(
                Value.Ref(labelRestFunSym._1, S(labelRestFunSym._2)),
                labelRestFunFvs.map(s => Arg(N, Value.Ref(s, N)))
              )(true, false, false),
              false)
        case Return(res, true) => super.applyBlock(Return(res, false))
        case _ => super.applyBlock(b)
    end Rewriter
    
    class RefreshSymbol(existingMapping: Map[Symbol, Symbol]) extends BlockTransformer(_symSubst):
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
      
      override def applyDefn(defn: Defn)(k: Defn => Block): Block =
        defn match
        case fun: FunDefn =>
          assert(fun.owner.isEmpty)
          // because fun sym is not treated as a free var, we refresh here
          var newlyCreated = false
          val (sym2, dSym2) = mapping.get(fun.sym) match
            case Some(s: BlockMemberSymbol) => (s, s.tsym.get)
            case None =>
              newlyCreated = true
              val newBms = new BlockMemberSymbol(fun.sym.nme, fun.sym.trees, fun.sym.nameIsMeaningful)
              val newDsym = fun.sym.tsym.map: tsym =>
                assert(tsym.owner.isEmpty)
                new TermSymbol(tsym.k, N, tsym.id)
              newBms.tsym = S(newDsym.get)
              mapping(fun.sym) = newBms
              (newBms, newDsym.get)
            case _ => die
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
          if newlyCreated then
            Scoped(Set(sym2), k(FunDefn(N, sym2, dSym2, params2, body2)(fun.forceTailRec)))
          else
            k(FunDefn(N, sym2, dSym2, params2, body2)(fun.forceTailRec))
        case ValDefn(tsym, sym, rhs) =>
          val (tsym2, sym2) = mapping.get(sym) match
            case None =>
              val newBms = new BlockMemberSymbol(sym.nme, sym.trees, sym.nameIsMeaningful)
              val newTsym = new TermSymbol(tsym.k, tsym.owner, tsym.id)
              newBms.tsym = S(newTsym)
              (newTsym, newBms)
            case S(bms: BlockMemberSymbol) =>
              (bms.tsym.get, bms)
            case _ => die
          applyPath(rhs): rhs2 =>
            k(ValDefn(tsym2, sym2, rhs2))
        case _ => super.applyDefn(defn)(k)
      
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
          bodyWithCorrectSymbols)(false)
    end newPolyFuns
    
    val newBranchFuns =
      for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
        val instId = dtorId.getInstId
        val ogBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
        val restFunSym = restFunSyms(dtorId)
        val restFunArgs = restFnFvs(dtorId)
        val actualBody = Begin(
          new Rewriter(instId).applyBlock(ogBody),
          Return(
            Call(
                Value.Ref(restFunSym._1, S(restFunSym._2)),
                restFunArgs.map(a => Arg(N, Value.Ref(a, N)))
              )(true, false, false),
              false))
        val refreshedFvSymbols = dtorBranchFnFvs(branchId._1).map(s => s -> new VarSymbol(Tree.Ident(s"fv_${s.nme}")))
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshedFvSymbols.toMap).applyBlock(actualBody)
        FunDefn(N, bms, tSym,
          (refreshedFvSymbols.unzip._2 ++ branchFunParamFieldSyms(branchId)).asParamList :: Nil,
          bodyWithCorrectSymbols
        )(false)
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
              Return(
                Call(
                  Value.Ref(parentFunSym._1, S(parentFunSym._2)),
                  parentFunFvs.map(a => Arg(N, Value.Ref(a, N)))
                )(true, false, false),
                false))
          case None => transformedOgBody
        val refreshedFvSymbols = restFnFvs(restFunId).map(s => s -> new VarSymbol(Tree.Ident(s"fv_${s.nme}")))
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshedFvSymbols.toMap).applyBlock(actualBody)
        FunDefn(N, bms, tsym, refreshedFvSymbols.unzip._2.asParamList :: Nil, bodyWithCorrectSymbols)(false)
    end newRestFuns
    
    val newMainBody =
      val rewritten = Scoped(
        Set.from(newPolyFuns.map(_.sym) ++ newBranchFuns.map(_.sym) ++ newRestFuns.map(_.sym)),
        new Rewriter(Nil).applyBlock(pre.b))
      object implicitRetPass extends BlockTransformerShallow(_symSubst):
        override def applyBlock(b: Block): Block = b match
          case Return(res, false) => Return(res, true)
          case _ => super.applyBlock(b)
      implicitRetPass.applyBlock(rewritten)
    (newPolyFuns ++ newBranchFuns ++ newRestFuns).foldRight(newMainBody): (fdef, rest) =>
      Define(fdef, rest)
  end newBody
end DeforestRewriter

