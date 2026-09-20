package hkmc2
package codegen

import scala.collection.mutable.{Set as MutSet, Map as MutMap, Buffer}

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.flowAnalysis.*
import semantics.*
import syntax.Tree


class FlowAnalysisBasedRewrite(
  constraintSolver: FlowConstraintSolver,
  val deadParamElimSolver: DeadParamElimResult,
  val etaExpansionSolver: EtaExpansionResult,
  val deadConstructorElimSolver: DeadConstructorElimResult,
)(using Raise) extends PolyInstantiationRewrite(constraintSolver):

  private case class EtaParamList(params: ParamList, args: Ls[Arg])
  
  class Rewriter(instId: InstantiationId) extends InstantiationRewriter(instId):
    
    // dead parameter elimination states and helper functions
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
            filterParamList(pl, deadParamElimSolver.eliminableParams(ConcreteId((funSym, whichParamList), instId)))
          if pl2 isnt pl then changed = true
          removed ++= removed2
          pl2
      (if changed then params2 else params) -> removed.toSet
    
    
    // eta expansion states and helper functions
    private var activeEtaArgss: Ls[Ls[Arg]] = Nil
    
    private def withEtaArgss[A](etaArgss: Ls[Ls[Arg]])(thunk: => A): A =
      val saved = activeEtaArgss
      activeEtaArgss = etaArgss
      try thunk
      finally activeEtaArgss = saved
    
    private def etaParamLists(id: ConcreteFunId, existingParams: Ls[ParamList]): Ls[EtaParamList] =
      
      def paramCount(pl: ParamList): Int =
        pl.params.size + pl.restParam.fold(0)(_ => 1)
      end paramCount
      
      def eliminableParamsOf(targets: EtaTargets): Set[Int] =
        val arities = targets.prodFuns.map(pf => pf.params.size + pf.restParam.fold(0)(_ => 1))
        assert(arities.forall(_ === targets.paramCount),
          s"eta expansion level disagrees with its targets on arity: ${targets.pp} -> $arities")
        val eliminable = targets.prodFuns.map: target =>
          deadParamElimSolver.eliminableParams(target.concreteId)
        assert(eliminable.size <= 1,
          s"eta expansion targets disagree on eliminable parameters: " +
          s"${targets.pp} -> $eliminable")
        eliminable.headOption.getOrElse(Set.empty)
      end eliminableParamsOf
      
      etaExpansionSolver.etaExpandedFunShape.get(id).toList.flatMap: targetShape =>
        val existingShape = existingParams.map(paramCount)
        if targetShape.map(_.paramCount).startsWith(existingShape) then
          targetShape.drop(existingShape.size).zipWithIndex.map:
            case (targets, idx) =>
              val eliminable = eliminableParamsOf(targets)
              val params = (0 until targets.paramCount).iterator.filterNot(eliminable).map: i =>
                Param.simple(new VarSymbol(new Tree.Ident(s"eta$$$idx$$$i"), erasedType = N))
              .toList
              EtaParamList(
                ParamList(ParamListFlags.empty, params, N),
                params.map(p => Arg(N, p.sym.asSimpleRef)),
              )
        else
          lastWords("not the same shape?")
    
    private def etaCall(base: Path): Result =
      Call(base, activeEtaArgss.ne_!)(CallMetadata.mlsFunWithEffect)
    
    
    override def rewriteFunDefn(fun: FunDefn): RewrittenFunDefn =
      val FunDefn(_, _, dSym, params, body) = fun
      val etaParams = etaParamLists(ConcreteId((dSym, 0), instId), params)
      val (keptParams, removed) = filterFunParams(dSym, params)
      val params2 = keptParams.mapConserve(applyParamList) ::: etaParams.map(_.params)
      val body2 = withEliminatedParams(removed):
        withEtaArgss(etaParams.map(_.args)):
          applyFunBodyLikeBlock(body)
      params2 -> body2
    
    
    // traversal
    override def applyPath(p: Path)(k: Path => Block): Block = p match
      case PolyFnRef(specializedRef) => k(specializedRef)
      case _ => super.applyPath(p)(k)
    
    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case ref@Value.SimpleRef(l: VarSymbol) if activeEliminatedParams(l) =>
        k(Value.Lit(Tree.UnitLit(false)).withLocOf(ref))
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
              Call(fun, (argss ++ activeEtaArgss).ne_!)(c.metadata))
          case _ =>
            val tmp = TempSymbol(N, erasedType = N, "eta$res")
            Scoped(
              Set.single(tmp),
              Assign(tmp, res2, Return(etaCall(tmp.asPath).withLocOf(res2))))
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
      case ctorSite@CtorProducer(_, args, selectedFrom)
        if deadConstructorElimSolver.deadCtors.contains(ConcreteId(ctorSite.uid, instId)) =>
        (selectedFrom.toList ::: args.map(_.value))
          .filterNot(_.isPure)
          .foldRight(k(Value.Lit(Tree.UnitLit(false)).withLocOf(ctorSite))): (p, rest) =>
            applyPath(p)(Assign.discard(_, rest))
      case c@Call(fun, args :: restArgss) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableCallSiteArgs(ConcreteId(c.uid, instId))
        applyPath(fun): fun2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (fun2 is fun) && (args2 is args) then c
              else Call(fun2, args2 ne_:: restArgss)(c.metadata).withLocOf(c)
            )
      case i@Instantiate(mut, cls, args :: restArgss) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableCallSiteArgs(ConcreteId(i.uid, instId))
        applyPath(cls): cls2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (cls2 is cls) && (args2 is args) then i
              else Instantiate(mut, cls2, args2 :: restArgss)(i.metadata).withLocOf(i)
            )
      case _ => super.applyResult(r)(k)
    
    override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
      case cls: ClsLikeDefn =>
        withEtaArgss(Nil):
          super.applyDefn(cls)(k)
      case _ =>
        super.applyDefn(defn)(k)
    
    override def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
      withEtaArgss(Nil):
        super.applyObjBody(defn)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      val (params2, body2) = rewriteFunDefn(fun)
      if (params2 is fun.params) && (body2 is fun.body) then fun
      else FunDefn(fun.owner, fun.sym, fun.dSym, params2, body2)(fun.configOverride, fun.annotations)
    
    override def applyLam(lam: Lambda): Lambda =
      val lamId: ConcreteFunId = ConcreteId(lam.uid, instId)
      val etaParams = etaParamLists(lamId, lam.params :: Nil)
      val (params2, removed) =
        filterParamList(lam.params, deadParamElimSolver.eliminableParams(lamId))
      val body2 = withEliminatedParams(removed):
        withEtaArgss(etaParams.map(_.args)):
          applyFunBodyLikeBlock(lam.body)
      val wrappedBody = etaParams.map(_.params).foldRight(body2): (params, body) =>
        Return(Lambda(params, body)(Nil))
      if (params2 is lam.params) && (wrappedBody is lam.body) then lam
      else Lambda(params2, wrappedBody)(lam.annot).withLocOf(lam)
    
  end Rewriter
  
  
  // ====== start: implements the abstract members of `PolyInstantiationRewrite` ======
  def solvers: Iterable[FlowAnalysisSolverResult] =
    deadParamElimSolver :: etaExpansionSolver :: deadConstructorElimSolver :: Nil
  
  def mkRewriter(instId: InstantiationId) = new Rewriter(instId)
  
  def mkRootRewriter(rewrittenInPlace: Map[TermSymbol, RewrittenFunDefn]) =
    new Rewriter(Nil):
      override def applyFunDefn(fun: FunDefn): FunDefn =
        rewrittenInPlace.get(fun.dSym) match
          case S((params, body)) =>
            if (params is fun.params) && (body is fun.body) then fun
            else FunDefn(fun.owner, fun.sym, fun.dSym, params, body)(fun.configOverride, fun.annotations)
          case N => super.applyFunDefn(fun)
  
  def mkPolyFunCopy(
    original: FunDefn,
    bms: BlockMemberSymbol,
    tSym: TermSymbol,
    rewritten: RewrittenFunDefn,
  ): FunDefn =
    class RefreshSymbol(existingMapping: Map[Symbol, Symbol]) extends SymbolRefresher(existingMapping):
      override def applyValue(v: Value)(k: Value => Block): Block = v match
        case Value.This(l) =>
          pre.res.modSymToBms.get(l) match
            case Some(bms) =>
              k(bms.asMemberRef(l.asMod.get))
            case None => super.applyValue(v)(k)
        case _ => super.applyValue(v)(k)
    end RefreshSymbol
    
    val (rewrittenParams, rewrittenBody) = rewritten
    val refreshParamMap = MutMap.empty[Symbol, Symbol]
    def refreshParam(p: Param): Param =
      val newSym = new VarSymbol(Tree.Ident(p.sym.name), erasedType = p.sym.erasedType)
      refreshParamMap(p.sym) = newSym
      Param(p.flags, newSym, p.sign, p.modulefulness)
    val refreshedParams = rewrittenParams.map:
      case ParamList(flags, params, restParam) =>
        ParamList(flags, params.map(refreshParam), restParam.map(refreshParam))
    FunDefn(
      N, bms, tSym, refreshedParams,
      new RefreshSymbol(refreshParamMap.toMap).apply(rewrittenBody))(
        original.configOverride, original.annotations)
  end mkPolyFunCopy
  
  def otherNewFunDefns: Iterable[FunDefn] = Nil
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
      FlowAnalysis.mkTraceLogger(optCfg.config.copy(debug = debug), prefix, tl)
    val flowAnalysisRes = mkTl("flow-analysis > ", optCfg.debug).givenIn:
      FlowAnalysis(
        p,
        mono = optCfg.mono,
        nonAffineTracking = false,
        accumulatorTracking = false,
      )
    
    val etaExpansionSolver =
      if eta then new EtaExpansionSolver(
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
