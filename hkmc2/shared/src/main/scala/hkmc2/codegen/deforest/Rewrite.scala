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
  // TODO: the first one is free vars,
  // the second one is for fields (which share the same symbol in `branchSelSyms`)
  val branchFunParamSyms = MutMap.empty[BranchId, (Ls[VarSymbol], Ls[VarSymbol])]
  val ctorWhichBranch = MutMap.empty[CtorDtorId, BranchId]
  
  // TODO: when rewriting, we should call a dtor with these free vars
  // for non-nested matches, these are the free var symbols in the original program
  // for nested matches, these are the free var VarSymbols from parent fusing matches
  val callDtorFvs = MutMap.empty[CtorDtorId, Ls[Symbol]]
  // TODO: when rewriting, we should turn a ctor to a lam with the following parameter
  val ctorLamFvs = MutMap.empty[CtorDtorId, Ls[VarSymbol]]
  
  
  // compute original bodies of a branch
  private val branchOriginalBodies = MutMap.empty[ResultId -> Opt[CtorCls], Block]
  // if a fusing dtor needs explicit returns
  private val dtorExplicitRet = MutMap.empty[ResultId, Boolean].withDefaultValue(false)
  
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
      // identify branch for a ctor
      // keep track of the branch body for later use
      // create branch func syms
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
      ctorWhichBranch(ctor) = destBranchId
      branchOriginalBodies.getOrElseUpdate(
        dest._1 -> whichBranch,
        Begin(whichBranchBody, pre.res.getFullRestOfMatch(dest._1)))
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
      branchFunParamSyms.getOrElseUpdate(
        destBranchId,
        Nil -> // TODO: compute free vars!!
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
  
  locally {
    class ReplaceBreakTransformer extends BlockTransformerShallow(_symSubst):
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
    
    branchOriginalBodies.mapValuesInPlace:
      case (d, branch) =>
        val transformer = new ReplaceBreakTransformer
        val newBranch = transformer.applyBlock(branch)
        dtorExplicitRet(d._1) ||= transformer.hasExplicitRet
        newBranch
  }

  // TODO:
  // - free vars
  // - handle scoped blocks
  // - refresh vars
  private class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
    extension (resId: ResultId) def toCtorDtorId = CtorDtorId(resId, instId)
    override def applyResult(r: Result)(k: Result => Block): Block =
      r match
      case s@DeforestTupSelect(_, _) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        k(Value.Ref(branchSelSyms(s.uid.toCtorDtorId)))
      case s@DeforestableSelect(sym: TermSymbol) if branchSelSyms.isDefinedAt(s.uid.toCtorDtorId) =>
        assert(sym.k is ParamBind)
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
        branchFunParamSyms(branchId)._2.asParamList :: Nil,
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

