package hkmc2
package codegen

import utils.*
import hkmc2.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import hkmc2.codegen.flowAnalysis.*
import hkmc2.syntax.Fun
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, Buffer}


type ConcreteFunId = ConcreteId[FunId]
type ConcreteCallSiteId = ConcreteId[ResultId]


class DeadParamElimSolver(val constraintSolver: FlowConstraintSolver):
  given tl: TraceLogger = constraintSolver.tl
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState

  val collector: FlowConstraintsCollector = constraintSolver.collector
  val prodFuns: collection.Seq[ProdFun] = constraintSolver.prodFunsWithDests
  val consFuns: collection.Seq[ConsFun] = constraintSolver.consFunsWithSrcs
  
  // handle clashes for dead param elim
  val (liveParams, liveCallSiteParams) =
    def isSyntheticRoot(prodFun: ProdFun): Bool =
      val instId = prodFun.instantiationId.get
      collector.synthesizedInstIdToFunSym.get(instId).exists: rootFunSym =>
        prodFun.exprId match
          case (funSym: TermSymbol, _) =>
            (collector.funToSccRep(funSym), collector.funToSccRep(rootFunSym)) match
            case S(rep1) -> S(rep2) => rep1 is rep2
            case _ => false
          case _ => false
    end isSyntheticRoot
    
    val prodRoots = Buffer.empty[(ProdFun, Int)]
    val consRoots = Buffer.empty[(ConsFun, Int)]
    for prodFun <- prodFuns do
      if isSyntheticRoot(prodFun) || prodFun.dests.contains(UnknownCons) then
        prodFun.params.indices.foreach: i =>
          prodRoots += prodFun -> i
      else
        prodFun.params.zipWithIndex.foreach:
          case (v: StratVar, i) =>
            val ubs = constraintSolver.AllUpperBounds(v)
            if ubs.exists:
              case _: StratVar => false
              case _: IntoParam => false
              case NonAffine | Accumulator => false
              case _ => true
            then prodRoots += prodFun -> i
          case (_, i) =>
            prodRoots += prodFun -> i

    for consFun <- consFuns do
      if consFun.srcs.contains(UnknownProd) then
        consFun.params.indices.foreach: i =>
          consRoots += consFun -> i
      else
        val minSize = consFun.srcs
          .collect:
            case p: ProdFun if p.restParam.isDefined => p.params.size
          .minOption
        minSize match
        case None => ()
        case Some(s) =>
          (s until consFun.params.size).foreach: i =>
            consRoots += consFun -> i
        

    val result = FlowWebComputation[(ProdFun, Int), (ConsFun, Int)](
      (prodFun, idx) => prodFun.dests.collect:
        case c: ConsFun => (c, idx),
      (consFun, idx) => consFun.srcs.collect:
        case p: ProdFun => (p, idx),
      prodRoots,
      consRoots,
    )
    (result.markedProducers, result.markedConsumers)
  end val
  
  val eliminableParamsById =
    LinkedHashMap.empty[ConcreteFunId, Set[Int]].withDefaultValue(Set.empty)
  val eliminableCallSiteArgsById =
    LinkedHashMap.empty[ConcreteCallSiteId, Set[Int]].withDefaultValue(Set.empty)
  
  for prodFun <- prodFuns do
    val eliminable = prodFun.params.indices.filterNot: i =>
      liveParams.contains(prodFun -> i)
    if eliminable.nonEmpty then
      eliminableParamsById.get(prodFun.concreteId) match
      case None => eliminableParamsById(prodFun.concreteId) = eliminable.toSet
      case S(existing) => assert(existing.toList.sorted === eliminable)
  
  for consFun <- consFuns do
    val eliminable = consFun.params.indices.filterNot: i =>
      liveCallSiteParams.contains(consFun -> i)
    if eliminable.nonEmpty then
      eliminableCallSiteArgsById.get(consFun.concreteId) match
      case None => eliminableCallSiteArgsById(consFun.concreteId) = eliminable.toSet
      case S(existing) => assert(existing.toList.sorted === eliminable)
  
  if tl.doTrace then
    def showRefSite(resultId: ResultId): Str =
      resultId.getReferredFun match
        case Some(fun) => s"${fun.nme}@$resultId"
        case None => s"${resultId.getResult}@$resultId"
    end showRefSite

    def showInstId(instId: InstantiationId): Str =
      if instId.isEmpty then "<root>" else instId.map(showRefSite).mkString(".")
    end showInstId

    def showProdFun(prodFun: ProdFun): Str =
      def showFunId(funId: FunId): Str = funId match
        case (funSym: Symbol, whichParamList) => s"${funSym.nme}#$whichParamList"
        case exprId: ResultId => exprId.getResult match
          case Lambda(_, _) => s"lambda@$exprId"
          case _ => showRefSite(exprId)
      val inst = prodFun.instantiationId.fold("")(instId => s" @ ${showInstId(instId)}")
      s"prodfun ${showFunId(prodFun.exprId)}$inst"
    end showProdFun
    
    assert(eliminableCallSiteArgsById.nonEmpty === eliminableParamsById.nonEmpty)
    tl.log(">>> dead-param-elim results >>>")
    for (prodFun, prodFunStr) <- prodFuns.map(p => p -> showProdFun(p)).sortBy(_._2) do
      eliminableParamsById.get(prodFun.concreteId) match
        case Some(elim) =>
          tl.log(s"$prodFunStr -> eliminable: {${elim.toSeq.sorted.mkString(", ")}}")
        case _ => ()
    tl.log("<<< dead-param-elim results <<<")
  end if
end DeadParamElimSolver


class Rewrite(val deadParamElimSolver: DeadParamElimSolver)(using Raise):
  
  def apply(): Program =
    if newBody is pre.pgrm.main then pre.pgrm
    else Program(pre.pgrm.imports, newBody)
  
  val constraintSolver = deadParamElimSolver.constraintSolver
  val collector = deadParamElimSolver.collector
  given tl: TraceLogger = constraintSolver.tl
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  given pre: FlowPreAnalyzer = constraintSolver.preAnalyzer
  
  private val _symSubst = SymbolSubst.Id
  val newPolyFnSyms = LinkedHashMap.empty[InstantiationId, Map[TermSymbol, (BlockMemberSymbol, TermSymbol)]]
  
  // compute necessary poly fun syms
  locally {
    def mkNewPolyFnSyms(instId: InstantiationId): Unit =
      val referredFun = instId.last.getReferredFun.get
      val groupFuns = collector.funToSccGroups(referredFun)
      newPolyFnSyms.getOrElseUpdate(
        instId,
        groupFuns
          .map: f =>
            val name = instId.mkFunName + s"$$${f.nme}"
            f -> (
              new BlockMemberSymbol(name, Nil, true),
              new TermSymbol(Fun, N, Tree.Ident(name)))
          .toMap)
    end mkNewPolyFnSyms
    
    for
      case ConcreteId(_, instId) <-
        deadParamElimSolver.eliminableParamsById.keysIterator ++
        deadParamElimSolver.eliminableCallSiteArgsById.keysIterator
      path <- instId.inits
      if path.nonEmpty && !collector.synthesizedInstIdToFunSym.contains(path)
    do mkNewPolyFnSyms(path)
  }
  
  class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
    
    private val activeEliminatedParams = MutSet.empty[VarSymbol]

    private def withEliminatedParams[A](removed: Set[VarSymbol])(thunk: => A): A =
      if removed.isEmpty then thunk
      else
        activeEliminatedParams ++= removed
        try thunk
        finally activeEliminatedParams --= removed

    private def filterParamList(pl: ParamList, eliminable: Set[Int]): (ParamList, Set[VarSymbol]) =
      if eliminable.isEmpty then pl -> Set.empty
      else
        val removed = MutSet.empty[VarSymbol]
        val keptParams = Buffer.empty[Param]
        pl.params.zipWithIndex.foreach:
          case (param, i) =>
            if eliminable(i) then removed.add(param.sym)
            else keptParams.append(param)
        ParamList(pl.flags, keptParams.toList, pl.restParam) -> removed.toSet
    
    private def filterFunParams(funSym: TermSymbol, params: Ls[ParamList]): (Ls[ParamList], Set[VarSymbol]) =
      val removed = MutSet.empty[VarSymbol]
      var changed = false
      val params2 = params.zipWithIndex.map:
        case (pl, whichParamList) =>
          val (pl2, removed2) =
            filterParamList(pl, deadParamElimSolver.eliminableParamsById(ConcreteId((funSym, whichParamList), instId)))
          if pl2 isnt pl then changed = true
          removed ++= removed2
          pl2
      (if changed then params2 else params) -> removed.toSet

    def rewriteFunBody(funSym: TermSymbol, params: Ls[ParamList], body: Block): Block =
      val (_, removed) = filterFunParams(funSym, params)
      withEliminatedParams(removed):
        applyFunBodyLikeBlock(body)
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      def newRefId(refId: ResultId, refSym: TermSymbol): InstantiationId =
        instId match
        case Nil => refId :: Nil
        case pathTo :+ called =>
          val lastRefedSymbol = called.getReferredFun.get
          val funToSccRepMap = collector.funToSccRep
          (funToSccRepMap(lastRefedSymbol), funToSccRepMap(refSym)) match
            case (Some(a), Some(b)) if a is b => instId
            case _ => instId :+ refId
        case _ => lastWords(s"newRefId: impossible InstantiationId shape $instId")
      end newRefId
    
      p match
      case ref@FunRef(f, _) if newPolyFnSyms.isDefinedAt(newRefId(ref.uid, f)) =>
        val (bms, tSym) = newPolyFnSyms(newRefId(ref.uid, f))(f)
        k(bms.asMemberRef(tSym))
      case _ => super.applyPath(p)(k)

    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case ref@Value.SimpleRef(l: VarSymbol) if activeEliminatedParams(l) =>
        k(Value.Lit(Tree.UnitLit(false)).withLocOf(ref))
      case _ => super.applyValue(v)(k)

    override def applyBlock(b: Block): Block = b match
      case Assign(lhs: VarSymbol, rhs, rst) if activeEliminatedParams(lhs) =>
        applyResult(rhs): rhs2 =>
          Assign.discard(rhs2, applySubBlock(rst))
      case _ => super.applyBlock(b)
    
    override def applyResult(r: Result)(k: Result => Block): Block =
      def rewriteArgs(args: Ls[Arg], eliminable: Set[Int])(k: Ls[Arg] => Block): Block =
        if eliminable.isEmpty then applyArgs(args)(k)
        else
          def rec(rest: Ls[Arg], idx: Int, changed: Bool, accRev: Ls[Arg]): Block = rest match
            case Nil =>
              k(if changed then accRev.reverse else args)
            case arg :: tl if eliminable(idx) =>
              rec(tl, idx + 1, true, accRev)
            case arg :: tl =>
              applyArg(arg): arg2 =>
                rec(tl, idx + 1, changed || !(arg2 is arg), arg2 :: accRev)
          rec(args, 0, false, Nil)
      end rewriteArgs
      
      r match
      case c@Call(fun, args :: restArgss) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableCallSiteArgsById(ConcreteId(c.uid, instId))
        applyPath(fun): fun2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (fun2 is fun) && (args2 is args) then c
              else Call(fun2, args2 ne_:: restArgss)(c.metadata).withLocOf(c)
            )
      case i@Instantiate(mut, cls, args :: restArgss) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableCallSiteArgsById(ConcreteId(i.uid, instId))
        applyPath(cls): cls2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (cls2 is cls) && (args2 is args) then i
              else Instantiate(mut, cls2, args2 :: restArgss)(i.metadata).withLocOf(i)
            )
      case _ => super.applyResult(r)(k)
    
    override def applyLam(lam: Lambda): Lambda =
      val (params2, removed) = filterParamList(lam.params, deadParamElimSolver.eliminableParamsById(ConcreteId(lam.uid, instId)))
      val body2 = withEliminatedParams(removed):
        applyFunBodyLikeBlock(lam.body)
      if (params2 is lam.params) && (body2 is lam.body) then lam else Lambda(params2, body2)(lam.annot)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      val own2 = fun.owner.mapConserve(_.subst)
      val sym2 = fun.sym.subst
      val dSym2 = fun.dSym.subst
      val (params2, removed) = filterFunParams(fun.dSym, fun.params)
      val body2 = withEliminatedParams(removed):
        applyFunBodyLikeBlock(fun.body)
      if (own2 is fun.owner) && (sym2 is fun.sym) && (dSym2 is fun.dSym) &&
          (params2 is fun.params) && (body2 is fun.body)
      then fun else FunDefn(own2, sym2, dSym2, params2, body2)(fun.configOverride, fun.annotations)
  end Rewriter
  
  val newBody =
    
    def filterParamList(pl: ParamList, eliminable: Set[Int]): ParamList =
      if eliminable.isEmpty then pl
      else
        ParamList(
          pl.flags,
          pl.params.zipWithIndex.collect:
            case (param, i) if !eliminable(i) => param,
          pl.restParam
        )
    end filterParamList
    
    def filterFunParams(funSym: TermSymbol, params: Ls[ParamList], instId: InstantiationId): Ls[ParamList] =
      params.zipWithIndex.map:
        case (pl, whichParamList) =>
          filterParamList(pl, deadParamElimSolver.eliminableParamsById(ConcreteId((funSym, whichParamList), instId)))
    end filterFunParams
    
    class RefreshSymbol(existingMapping: Map[Symbol, Symbol]) extends SymbolRefresher(existingMapping):
      override def applyValue(v: Value)(k: Value => Block): Block = v match
        case Value.This(l) =>
          pre.res.modSymToBms.get(l) match
            case Some(bms) =>
              k(bms.asMemberRef(l.asMod.get))
            case None => super.applyValue(v)(k)
        case _ => super.applyValue(v)(k)
    end RefreshSymbol
    
    def makeRefreshedParams(params: Ls[ParamList]): (Ls[ParamList], Map[Symbol, Symbol]) =
      val refreshParamMap = MutMap.empty[Symbol, Symbol]
      val refreshedParams = params.map:
        case ParamList(flags, params, restParam) =>
          val params2 = params.map:
            case p =>
              val newSym = new VarSymbol(Tree.Ident(p.sym.name))
              refreshParamMap(p.sym) = newSym
              Param(p.flags, newSym, p.sign, p.modulefulness)
          val rest2 = restParam.map:
            case p =>
              val newSym = new VarSymbol(Tree.Ident(p.sym.name))
              refreshParamMap(p.sym) = newSym
              Param(p.flags, newSym, p.sign, p.modulefulness)
          ParamList(flags, params2, rest2)
      refreshedParams -> refreshParamMap.toMap
    end makeRefreshedParams
    
    val newPolyFuns =
      for
        (instId, funSymMap) <- newPolyFnSyms
        (referringFun, (bms, tSym)) <- funSymMap.toList.sortBy(_._1.uid)
      yield
        val fDefn = pre.res.funSymToFunDefn(referringFun)
        val filteredParams = filterFunParams(fDefn.dSym, fDefn.params, instId)
        val transformedBody = new Rewriter(instId).rewriteFunBody(fDefn.dSym, fDefn.params, fDefn.body)
        val (refreshedParams, refreshParamMap) = makeRefreshedParams(filteredParams)
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshParamMap).apply(transformedBody)
        FunDefn(
          N, bms, tSym, refreshedParams,
          bodyWithCorrectSymbols)(fDefn.configOverride, fDefn.annotations)
    
    val inplaceRewrittenFunBodies = Map.from[TermSymbol, Block]:
      for (selfInstId, funSym) <- collector.synthesizedInstIdToFunSym yield
        val fDefn = pre.res.funSymToFunDefn(funSym)
        funSym -> new Rewriter(selfInstId).rewriteFunBody(funSym, fDefn.params, fDefn.body)
    
    val newMainBody =
      object mainRewriter extends Rewriter(Nil):
        override def applyFunDefn(fun: FunDefn): FunDefn =
          inplaceRewrittenFunBodies.get(fun.dSym) match
            case Some(rewrittenBody) =>
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, rewrittenBody)(fun.configOverride, fun.annotations)
            case None => super.applyFunDefn(fun)
      Scoped(
        Set.from(newPolyFuns.map(_.sym)),
        mainRewriter.applyBlock(pre.pgrm.main))
    
    newPolyFuns.foldRight(newMainBody): (fdef, rest) =>
      Define(fdef, rest)
  
  end newBody
  
end Rewrite


object DeadParamElim:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    symbolPrinter: SymbolPrinter,
  ): Program =
    cfg.deadParamElim match
      case None => p
      case Some(dCfg) =>
        val outerTl = tl
        FlowAnalysis.mkTraceLogger(dCfg.config, "dead-param-elim > ", outerTl).givenIn:
          val flowAnalysisRes = FlowAnalysis(
            p,
            mono = dCfg.mono,
            nonAffineTracking = dCfg.effectiveTrackNonAffine,
            accumulatorTracking = dCfg.effectiveTrackAccumulator,
          )
          val deadParamElimSolver = new DeadParamElimSolver(flowAnalysisRes)
          if deadParamElimSolver.eliminableParamsById.isEmpty
            && deadParamElimSolver.eliminableCallSiteArgsById.isEmpty
          then p
          else
            val rewrite = new Rewrite(deadParamElimSolver)
            rewrite()


