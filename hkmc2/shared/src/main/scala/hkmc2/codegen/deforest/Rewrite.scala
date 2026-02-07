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
    def asParamList =
      ParamList(ParamListFlags.empty, vs.map(Param.simple), N)
  
  private val _symSubst = new SymbolSubst()
  
  // C(1, 2)
  //  ~> let x = 1; y = 2 in (fvs) => branchBody(fvs, x, y)
  // if scrut is C then let a = scrut.x; b = scrut.y in body
  //  ~> scrut(fvs)
  //  ~> fun branchBody(fvs, x, y) = let a = x; b = y in body
  
  type BranchId = CtorDtorId -> Opt[CtorCls]
  
  val ctorFieldSyms = MutMap.empty[CtorDtorId, Ls[TempSymbol]] // the `a` and `b`
  val newPolyFnSyms = LinkedHashMap.empty[InstantiationId, (BlockMemberSymbol, TermSymbol)]
  val branchSelSyms = MutMap.empty[CtorDtorId, VarSymbol]
  val branchFunSyms = LinkedHashMap.empty[BranchId, (BlockMemberSymbol, TermSymbol)]
  // branch fun params for fields (which share the same symbol in `branchSelSyms`)
  val branchFunParamFieldSyms = MutMap.empty[BranchId, Ls[VarSymbol]]
  val ctorWhichBranch = MutMap.empty[CtorDtorId, BranchId]
  
  // TODO: free vars for all the fusing branches of a dtor
  val dtorBranchFunsFvs = MutMap.empty[CtorDtorId, Set[Symbol]]
  // TODO: when rewriting, we should call a dtor with these free vars
  // for non-nested matches, these are the free var symbols in the original program
  // for nested matches, these are the free var VarSymbols from parent fusing matches
  val callDtorFvs = MutMap.empty[CtorDtorId, Ls[Symbol]]
  // TODO: when rewriting, we should turn a ctor to a lam with the following parameter
  val ctorLamFvs = MutMap.empty[CtorDtorId, Ls[VarSymbol]]
  
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
      for case ctorInstId@(referringTo :: _) <- List(ctor.instId, dest.instId) do
        newPolyFnSyms.getOrElseUpdate(
          ctorInstId,
          new BlockMemberSymbol(ctorInstId.mkFunName, Nil, true) ->
          new TermSymbol(Fun, N, Tree.Ident(ctorInstId.mkFunName)))
      
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
      
      // ctor dest branch function and free var computations
      val matchBlk = pre.res.matchScrutToMatchBlock(dest._1)
      val (whichBranch, whichBranchBody) =
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
      // compute the complete deforestable branch body of a fusing match
      // also compute if the match contains explicit return
      branchOriginalBodies.getOrElseUpdate(
        dest._1 -> whichBranch,
        locally:
          val ogBranchBody = Begin(whichBranchBody, pre.res.getFullRestOfMatch(dest._1))
          val transformer = new ReplaceBreakAndCheckExplicitRet
          val newBranch = transformer.applyBlock(ogBranchBody)
          dtorExplicitRet(dest._1) ||= transformer.hasExplicitRet
          newBranch
      )
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
      // compute the function parameters corresponding to fields of branch funs
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
  
  extension (b: Block)
    def deforestFreeVars(ctx: collection.Set[Symbol], instId: InstantiationId) =
      val traverser = new FreeVarTraverser(ctx, instId)
      traverser.applyBlock(b)
      traverser.refedVars.toSet -- traverser.assignedVars.toSet
  private class FreeVarTraverser(ctx: collection.Set[Symbol], instId: InstantiationId) extends BlockTraverser:
    extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
    val assignedVars = MutSet.from[Symbol]:
      pre.b match
        case Scoped(syms, body) =>
          syms
          ++ ctx
          ++ newPolyFnSyms.values.unzip._1
          ++ branchFunSyms.values.unzip._1
          ++ eState.builtinOpsMap.values
          ++ (eState.globalThisSymbol :: eState.runtimeSymbol :: Nil)
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
  
  
  
  
  // TODO:
  // - free vars
  // - handle scoped blocks
  // - refresh vars (this needs to be done after deforestation rewriting because this may change uid)
  //    refs to MM(moduleSymbol).fun needs to be changed to MM(bms).fun
  private class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
    extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
    override def applyResult(r: Result)(k: Result => Block): Block =
      r match
      case s@DeforestTupSelect(_, _) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
      case ctor@CtorCall(cls, args) if solver.finalCtorDests.isDefinedAt(ctor.uid.toCtorDtorId) =>
        val fieldSyms = ctorFieldSyms(ctor.uid.toCtorDtorId)
        val (branchBms, branchTermSym) = branchFunSyms(ctorWhichBranch(ctor.uid.toCtorDtorId))
        val callBranchFun =
          Lambda(
            ParamList(ParamListFlags.empty, Nil, N), // TODO: handle fvs, this should be a list of fvs vars
            Return(
              Call(
                Value.Ref(branchBms, S(branchTermSym)),
                fieldSyms.map(f => Arg(N, Value.Ref(f))))(true, false, false),
              false))
        args.zip(fieldSyms).foldRight(k(callBranchFun)):
          case (Arg(N, a) -> fieldSym, rest) =>
            applyPath(a): fusedField =>
              Assign(fieldSym, fusedField, rest)
          case _ => die
      case _ => super.applyResult(r)(k)
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      p match
      case ref@FunRef(f) if newPolyFnSyms.isDefinedAt(ref.uid :: instId) =>
        val (bms, tSym) = newPolyFnSyms(ref.uid :: instId)
        k(Value.Ref(bms, S(tSym)))
      case ctor@CtorCall(_, args) if solver.finalCtorDests.isDefinedAt(ctor.uid.toCtorDtorId) =>
        assert(args.isEmpty)
        val (branchBms, branchTermSym) = branchFunSyms(ctorWhichBranch(ctor.uid.toCtorDtorId))
        val lambdaSym = new TempSymbol(N, "deforest$lam")
        Assign(
          lambdaSym,
          Lambda(
            ParamList(ParamListFlags.empty, Nil, N), // TODO: handle fvs, this should be a list of fvs vars
            Return(Call(Value.Ref(branchBms, S(branchTermSym)), Nil)(true, false, false), false)),
          k(Value.Ref(lambdaSym, N)))
      case s@DeforestableSelect(sym: TermSymbol) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        assert(sym.k is ParamBind)
        k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
      case _ => super.applyPath(p)(k)
    
    override def applyBlock(b: Block): Block =
      b match
      case m@Match(scrut, _, _, _) if solver.finalDtorSrcs.isDefinedAt(scrut.uid.toCtorDtorId) =>
        val explicitRet = dtorExplicitRet(scrut.uid)
        applyPath(scrut): newScrut =>
          // TODO: handle fvs, the call param list should be a list of fvs vars
          Return(Call(newScrut, Nil)(true, false, false), explicitRet)
      case _ => super.applyBlock(b)
  end Rewriter
  
  val newPolyFuns =
    for case (instId@(referringTo :: _), (bms, tSym)) <- newPolyFnSyms yield
      val referringFun = referringTo.getReferredFun.get
      val fDefn = pre.res.funSymToFunDefn(referringFun)
      FunDefn(
        N, bms, tSym, fDefn.params, // TODO: refresh symbols
        (new Rewriter(instId).applyBlock(fDefn.body)))(false)
  end newPolyFuns
  
  val newBranchFuns =
    for (branchId@(dtorId, whichBranch), (bms, tSym)) <- branchFunSyms yield
      val originalBranchBody = branchOriginalBodies(dtorId.exprId -> whichBranch)
      // TODO: fvs!
      FunDefn(N, bms, tSym,
        branchFunParamFieldSyms(branchId).asParamList :: Nil,
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
  tl.log(newBody.pp)
  // for (bId, body) <- branchOriginalBodies do
  //   tl.log(bId._1.getResult)
  //   tl.log(s"\t${body.pp}")
end DeforestRewriter

