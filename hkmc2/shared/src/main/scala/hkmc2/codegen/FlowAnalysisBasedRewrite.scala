package hkmc2
package codegen

import scala.collection.mutable.{Set as MutSet, Buffer, LinkedHashMap}

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.flowAnalysis.*
import semantics.*
import syntax.{Tree, SpreadKind}


class FlowAnalysisBasedRewrite(
  constraintSolver: FlowConstraintSolver,
  val deadParamElimSolver: DeadParamElimResult,
  val etaExpansionSolver: EtaExpansionResult,
  val deadConstructorElimSolver: DeadConstructorElimResult,
)(using Raise) extends PolyInstantiationRewrite(constraintSolver):

  private case class EtaParamList(params: LoweredParamList):
    def args: Ls[Arg] = params.params.map(p => Arg(N, p.sym.asSimpleRef)) :::
      params.restParam.toList.map(p => Arg(S(SpreadKind.Eager), p.sym.asSimpleRef))
  
  // the targets of each param list that eta expansion appends to `id`, with the target params dpe eliminates
  private def etaTargetLists(id: ConcreteFunId, existingParams: Ls[LoweredParamList]): Ls[(EtaTargets, Set[Int])] =
    def eliminableParamsOf(targets: EtaTargets): Set[Int] =
      val paramInfos = targets.prodFuns.map(_.paramInfo)
      assert(paramInfos.forall(_ === targets.paramInfo),
        s"eta expansion level disagrees with its targets on arity: ${targets.pp} -> $paramInfos")
      val eliminable = targets.prodFuns.map: target =>
        deadParamElimSolver.eliminableParams(target.concreteId)
      assert(eliminable.size <= 1,
        s"eta expansion targets disagree on eliminable parameters: " +
        s"${targets.pp} -> $eliminable")
      eliminable.headOption.getOrElse(Set.empty)
    end eliminableParamsOf
    
    etaExpansionSolver.etaExpandedFunShape.get(id).toList.flatMap: targetShape =>
      val existingShape = existingParams.map: pl =>
        (pl.params.size, pl.paramCountLB, pl.restParam.isDefined)
      if targetShape.map(_.paramInfo).startsWith(existingShape) then
        targetShape.drop(existingShape.size).map(targets => targets -> eliminableParamsOf(targets))
      else
        lastWords("not the same shape?")
  
  
  // an eta param stands for the `i`-th param of every target, so it takes all their types
  private def etaParamType(targets: EtaTargets, i: Int): Opt[ErasedValueType] =
    // the params of the targets' param lists, read from their definitions, which keep up with lifting
    def targetParams(target: ProdFun): Ls[Param] = target.exprId match
      case (fun: TermSymbol, idx: Int) => pre.res.funSymToFunDefn(fun).params(idx).params
      case lamId: ResultId => lamId.getResult match
        case lam: Lambda => lam.params.params
        case other => lastWords(s"expected lambda result, got $other")
    val types = targets.prodFuns.toList.map(targetParams(_)(i).sym.erasedType)
    if types.forall(_.isDefined) then S(ErasedType.Union.mk(types.flatten)) else N
  
  private def filterParamList(pl: LoweredParamList, eliminable: Set[Int]): (LoweredParamList, Set[VarSymbol]) =
    if eliminable.isEmpty then pl -> Set.empty
    else
      val removed = MutSet.empty[VarSymbol]
      val keptParams = Buffer.empty[Param]
      pl.params.zipWithIndex.foreach:
        case (param, i) =>
          if eliminable(i) then removed.add(param.sym)
          else keptParams.append(param)
      LoweredParamList(pl.flags, keptParams.toList, pl.restParam)(pl.toLoc) -> removed.toSet
  
  private def filterFunParams(funSym: TermSymbol, params: Ls[LoweredParamList], instId: InstantiationId): (Ls[LoweredParamList], Set[VarSymbol]) =
    val removed = MutSet.empty[VarSymbol]
    var changed = false
    val params2 = params.zipWithIndex.map:
      case (pl, whichParamList) =>
        val (pl2, removed2) =
          filterParamList(pl, deadParamElimSolver.eliminableParams(ConcreteId((funSym, whichParamList), instId)))
        if pl2 isnt pl then changed = true
        removed ++= removed2
        pl2
    (if changed then params2 else params) -> removed.toSet
  
  
  private def etaParamLists(targets: Ls[(EtaTargets, Set[Int])]): Ls[EtaParamList] =
    targets.zipWithIndex.map:
      case ((targets, eliminable), idx) =>
        def etaParam(name: Str, tpe: Opt[ErasedValueType]): Param =
          Param.simple(new VarSymbol(new Tree.Ident(s"eta$$$idx$$$name"), erasedType = tpe, mut = false))
        // * The expanded parameters corresponding to optional parameters of the targets must
        // * remain optional, since callers may omit their arguments.
        def optionalEtaParam(name: Str, tpe: Opt[ErasedValueType]): Param =
          val sym = new VarSymbol(new Tree.Ident(s"eta$$$idx$$$name"), erasedType = tpe, mut = false)
          Param(FldFlags.empty.copy(opt = true), sym, N, Modulefulness.none)(N)
        val params = (0 until targets.paramCount).iterator.filterNot(eliminable).map: i =>
          if i < targets.requiredParamCount then etaParam(i.toString, etaParamType(targets, i))
          else optionalEtaParam(i.toString, etaParamType(targets, i))
        .toList
        val restParam = Option.when(targets.hasRestParam)(etaParam("rest", N))
        EtaParamList(LoweredParamList(ParamListFlags.empty, params, restParam)(N))
  
  class Rewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[Symbol, Symbol]]) extends InstantiationRewriter(instId, refreshSymbolMappingForCopy):
    
    // dead parameter elimination states and helper functions
    private val activeEliminatedParams = MutSet.empty[VarSymbol]
    
    private def withEliminatedParams[A](removed: Set[VarSymbol])(thunk: => A): A =
      if removed.isEmpty then thunk
      else
        activeEliminatedParams ++= removed
        try thunk
        finally activeEliminatedParams --= removed
    
    // eta expansion states and helper functions
    private var activeEtaArgss: Ls[Ls[Arg]] = Nil
    
    private def withEtaArgss[A](etaArgss: Ls[Ls[Arg]])(thunk: => A): A =
      val saved = activeEtaArgss
      activeEtaArgss = etaArgss
      try thunk
      finally activeEtaArgss = saved
    
    private def etaCall(base: Path): Result =
      Call(base, activeEtaArgss.ne_!)(CallMetadata.mlsFunWithEffect, N)
    
    
    override def rewriteFunDefn(fun: FunDefn): RewrittenFunDefn =
      val rewrite = functionRewrites.get(instId -> fun.dSym).orElse(functionRewrites.get(Nil -> fun.dSym))
      val signature = rewrite.fold(fun.signature)(_.signature)
      val params2 = signature.params.mapConserve(applyParamList)
      val signature2 = if params2 is signature.params then signature else signature.copy(params = params2)
      val etaArgss = signature2.params.takeRight(rewrite.fold(0)(_.etaCount)).map(EtaParamList(_).args)
      val body2 = withEliminatedParams(rewrite.fold(Set.empty[VarSymbol])(_.removed)):
        withEtaArgss(etaArgss):
          applyFunBodyLikeBlock(fun.body)
      // Calls added for eta expansion may be effectful even when the original body was pure.
      val annotations = if rewrite.exists(_.etaCount > 0) then fun.annotations.filterNot(_.isInstanceOf[Annot.Pure])
        else fun.annotations
      (signature2, body2, annotations)
    
    
    // traversal
    override def applyPath(p: Path)(k: Path => Block): Block = p match
      case PolyFnRef(specializedRef) => k(specializedRef)
      case _ => super.applyPath(p)(k)
    
    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case ref@Value.SimpleRef(l: VarSymbol) if activeEliminatedParams(l) =>
        k(Value.Lit(Tree.UnitLit(false))(ref.toLoc))
      case Value.This(l) if refreshSymbolMappingForCopy.isDefined =>
        pre.res.modSymToBms.get(l) match
        case S(bms) => k(bms.asMemberRef(l.asMod.get))
        case N => super.applyValue(v)(k)
      case _ => super.applyValue(v)(k)
    
    override def applyBlock(b: Block): Block = b match
      case Assign(lhs: VarSymbol, rhs, rst) if activeEliminatedParams(lhs) =>
        applyResult(rhs): rhs2 =>
          Assign.discard(rhs2, applySubBlock(rst))
      case Return(res) if activeEtaArgss.nonEmpty =>
        applyResult(res): res2 =>
          if activeEtaArgss.isEmpty then Return(res2)
          else res2 match
          case p: Path =>
            Return(etaCall(p).withLocOf(res2))
          case c @ Call(fun, argss) =>
            Return(
              Call(fun, (argss ++ activeEtaArgss).ne_!)(c.metadata.copy(
                mayRaiseEffects = true,
                annotations = c.metadata.annotations.filterNot(_.isInstanceOf[Annot.Pure])), c.toLoc))
          case _ =>
            val tmp = TempSymbol(N, initErasedType = N, "eta$res")
            Scoped(
              Set.single(tmp),
              Assign(tmp, res2, Return(etaCall(tmp.asPath).withLocOf(res2))))
      case _ => super.applyBlock(b)
    
    override def applyResult(r: Result)(k: Result => Block): Block =
      def rewriteArgs(args: Ls[Arg], eliminable: Set[Int])(k: Ls[Arg] => Block): Block =
        if eliminable.isEmpty then applyArgs(args)(k)
        else
          val lastImpureEliminableIdx = args.iterator.zipWithIndex.foldLeft(-1):
            case (last, (arg, idx)) => if eliminable(idx) && !arg.value.isPure then idx else last
          def rec(rest: Ls[Arg], idx: Int, changed: Bool, accRev: Ls[Arg]): Block = rest match
            case Nil =>
              k(if changed then accRev.reverse else args)
            case arg :: tl if eliminable(idx) =>
              if arg.value.isPure then rec(tl, idx + 1, true, accRev)
              else applyPath(arg.value)(Assign.discard(_, rec(tl, idx + 1, true, accRev)))
            case arg :: tl =>
              applyArg(arg): arg2 =>
                if idx < lastImpureEliminableIdx then
                  val tmp = TempSymbol(N, initErasedType = arg2.value.erasedType, "arg")
                  Scoped(
                    Set.single(tmp),
                    Assign(tmp, arg2.value, rec(tl, idx + 1, true, arg2.copy(value = tmp.asPath) :: accRev)))
                else rec(tl, idx + 1, changed || !(arg2 is arg), arg2 :: accRev)
          rec(args, 0, false, Nil)
      end rewriteArgs
      
      r match
      case ctorSite@CtorProducer(_, args, selectedFrom)
        if deadConstructorElimSolver.deadCtors.contains(ConcreteId(ctorSite.uid, instId)) =>
        (args.reverseIterator.map(_.value) ++ selectedFrom)
          .filterNot(_.isPure)
          .foldLeft(k(Value.Lit(Tree.UnitLit(false))(ctorSite.toLoc))): (rest, p) =>
            applyPath(p)(Assign.discard(_, rest))
      case c@Call(fun, argss) =>
        def rewriteArgss(argLists: Iterator[(Ls[Arg], Int)])(k: Ls[Ls[Arg]] => Block): Block = argLists.nextOption() match
          case N => k(Nil)
          case S((args, whichArgList)) =>
            val eliminable = deadParamElimSolver.eliminableCallSiteArgs(ConcreteId((c.uid, whichArgList), instId))
            rewriteArgs(args, eliminable): args2 =>
              rewriteArgss(argLists): rest2 =>
                k(args2 :: rest2)
        applyPath(fun): fun2 =>
          rewriteArgss(argss.iterator.zipWithIndex): argss2 =>
            k(
              if (fun2 is fun) && argss2.corresponds(argss)(_ is _) then c
              else Call(fun2, argss2.ne_!)(c.metadata, c.toLoc)
            )
      case i@Instantiate(mut, cls, args :: restArgss) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableCallSiteArgs(ConcreteId((i.uid, 0), instId))
        applyPath(cls): cls2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (cls2 is cls) && (args2 is args) then i
              else Instantiate(mut, cls2, args2 :: restArgss)(i.metadata, i.toLoc)
            )
      case _ => super.applyResult(r)(k)
    
    override def applyDefn(defn: Defn)(k: Defn => Block): Block =
      def checkedK(defn2: Defn): Block =
        // if we are making specialized copies of the original code,
        // we shouldn't rebind the original symbol as this leads to wrong irDefn stored in the symbol
        if refreshSymbolMappingForCopy.isDefined then defn2.defnSym.foreach: ds =>
          softAssert(!defn.defnSym.contains(ds), s"a copy binds the original symbol ${ds}")
        k(defn2)
      defn match
      case cls: ClsLikeDefn =>
        withEtaArgss(Nil):
          super.applyDefn(cls)(checkedK)
      case _ =>
        super.applyDefn(defn)(checkedK)
    
    override def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
      withEtaArgss(Nil):
        super.applyObjBody(defn)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      val own2 = fun.owner.mapConserve(_.subst)
      val sym2 = fun.sym.subst
      val dSym2 = fun.dSym.subst
      val (signature2, body2, annotations) = rewriteFunDefn(fun)
      if (own2 is fun.owner) && (sym2 is fun.sym) && (dSym2 is fun.dSym) && (signature2 is fun.signature) && (body2 is fun.body)
        then fun else FunDefn(own2, sym2, dSym2, signature2, body2)(fun.configOverride, annotations)
    
    override def applyLam(lam: Lambda): Lambda =
      val lamId: ConcreteFunId = ConcreteId(lam.uid, instId)
      val etaParams = etaParamLists(etaTargetLists(lamId, lam.params :: Nil))
      val (params2, removed) =
        filterParamList(lam.params, deadParamElimSolver.eliminableParams(lamId))
      val body2 = withEliminatedParams(removed):
        withEtaArgss(etaParams.map(_.args)):
          applyFunBodyLikeBlock(lam.body)
      val wrappedBody = etaParams.map(_.params).foldRight(body2): (params, body) =>
        Return(Lambda(params, body)(Nil, N))
      if (params2 is lam.params) && (wrappedBody is lam.body) then lam
      else Lambda(params2, wrappedBody)(lam.annot, lam.toLoc)
    
  end Rewriter
  
  
  // ====== start: implements the abstract members of `PolyInstantiationRewrite` ======
  def solvers: Iterable[FlowAnalysisSolverResult] =
    deadParamElimSolver :: etaExpansionSolver :: deadConstructorElimSolver :: Nil
  
  def mkRewriter(instId: InstantiationId, refreshSymbolMappingForCopy: Opt[collection.Map[Symbol, Symbol]]) = new Rewriter(instId, refreshSymbolMappingForCopy)
  
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]) =
    new Rewriter(Nil, N):
      override def applyFunDefn(fun: FunDefn): FunDefn =
        rewrittenInPlace.get(fun.dSym) match
          case S((signature, body, annotations)) =>
            val dSym2 = fun.dSym.subst
            if (signature is fun.signature) && (body is fun.body) && (dSym2 is fun.dSym) then fun
            else FunDefn(fun.owner, fun.sym, dSym2, signature, body)(fun.configOverride, annotations)
          case N => super.applyFunDefn(fun)
  
  def otherNewFunDefns: Iterable[FunDefn] = Nil
  
  private case class FunctionRewrite(signature: FunDefn.Signature, removed: Set[VarSymbol], etaCount: Int)
  
  // Prepare actual parameter bindings once, before publishing symbols for forward/recursive calls.
  // The body rewrite consumes this same plan instead of independently reconstructing its signature.
  private lazy val functionRewrites: LinkedHashMap[(InstantiationId, TermSymbol), FunctionRewrite] =
    val res = LinkedHashMap.empty[(InstantiationId, TermSymbol), FunctionRewrite]
    val funIds =
      deadParamElimSolver.eliminableParamsById.keysIterator ++ etaExpansionSolver.etaExpandedFunShape.keysIterator
    for case ConcreteId((fun: TermSymbol, _), instId) <- funIds if !res.contains(instId -> fun) do
      val original = pre.res.funSymToFunDefn(fun)
      val (kept, removed) = filterFunParams(fun, original.params, instId)
      val eta = etaTargetLists(ConcreteId((fun, 0), instId), original.params)
      val etaParams = etaParamLists(eta)
      val params = kept ::: etaParams.map(_.params)
      val signature = if eta.isEmpty then
        if kept is original.params then original.signature else FunDefn.Signature.fromParams(kept, original.signature.result)
      else
        assert(!original.async && !original.generator, "Cannot eta-expand a wrapped result")
        val results = eta.last._1.prodFuns.toList.map: target =>
          target.exprId match
            case (targetFun: TermSymbol, idx: Int)
              if idx == pre.res.funSymToFunDefn(targetFun).params.size - 1
              && !etaExpansionSolver.etaExpandedFunShape.contains(
                ConcreteId((targetFun, 0), target.concreteId.instId)) =>
              targetFun.declaredResultType
            case _ => N
        val result = if results.forall(_.isDefined) then S(ErasedType.Union.mk(results.flatten)) else N
        FunDefn.Signature.fromParams(params, ErasedResult.Direct(result))
      res(instId -> fun) = FunctionRewrite(signature, removed, etaParams.size)
    res
  
  lazy val rewrittenSignatures: Map[(InstantiationId, TermSymbol), FunDefn.Signature] =
    collection.immutable.ListMap.from(functionRewrites.iterator.map((id, rewrite) => id -> rewrite.signature))
  // ====== end: implements the abstract members of `PolyInstantiationRewrite` ======
  
end FlowAnalysisBasedRewrite


object FlowAnalysisBasedRewrite:
  
  
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    symbolPrinter: SymbolPrinter,
  ): Program = cfg.flowBasedOpt.fold(p)(rewriteWith(p, _))
  
  
  private[codegen] def rewriteWith(
    p: Program,
    optCfg: Config.FlowBasedOpt,
    eta: Bool = true,
    dpe: Bool = true,
    dce: Bool = true,
  )(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    symbolPrinter: SymbolPrinter,
  ): Program =
    def mkTl(prefix: Str, debug: Bool) =
      FlowAnalysis.mkTraceLogger(optCfg.config.copy(debug = debug), prefix, tl.sink)(using tl.debugPrinter)
    val flowAnalysisRes = mkTl("flow-analysis > ", optCfg.debug).givenIn:
      FlowAnalysis(
        p,
        mono = optCfg.mono,
        nonAffineTracking = optCfg.config.effectiveTrackNonAffine,
        accumulatorTracking = optCfg.config.effectiveTrackAccumulator,
        logEffects = optCfg.config.logEffects,
      )
    
    val etaExpansionSolver =
      if eta && (cfg.liftDefns.isDefined || cfg.deforest.isDefined) then new EtaExpansionSolver(
        flowAnalysisRes, mkTl("eta-expansion > ", optCfg.effectiveDebugEta))
      else NoEtaExpansion
    val deadParamElimSolver =
      if dpe then new DeadParamElimSolver(
        flowAnalysisRes, mkTl("dead-param-elim > ", optCfg.effectiveDebugDpe))
      else NoDeadParamElim
    val deadConstructorElimSolver =
      if dce then new DeadConstructorElimSolver(
        flowAnalysisRes, mkTl("dead-constructor-elim > ", optCfg.effectiveDebugDce))
      else NoDeadConstructorElim
    new FlowAnalysisBasedRewrite(
      flowAnalysisRes,
      deadParamElimSolver,
      etaExpansionSolver,
      deadConstructorElimSolver,
    )()
