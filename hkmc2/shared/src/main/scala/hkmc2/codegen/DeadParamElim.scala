package hkmc2
package codegen

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import hkmc2.codegen.flowAnalysis.*
import hkmc2.syntax.Fun
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, Buffer}


type ConcreteFunId = FunId -> InstantiationId
type ConcreteCallSiteId = ResultId -> InstantiationId


class DeadParamElimSolver(val constraintSolver: FlowConstraintSolver):
  given tl: TraceLogger = constraintSolver.tl
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState

  val collector: FlowConstraintsCollector = constraintSolver.collector
  val funDests: collection.Map[ConcreteFunProducer, Set[ConcreteFunConsumer | NoCons.type]] =
    constraintSolver.funDests
  val funSrcs: collection.Map[ConcreteFunConsumer, Set[ConcreteFunProducer | NoProd.type]] =
    constraintSolver.funSrcs

  extension (prodFun: ConcreteFunProducer)
    def concreteId: ConcreteFunId = prodFun.funId -> prodFun.instantiationId.get
  
  extension (consFun: ConcreteFunConsumer)
    def concreteId: ConcreteCallSiteId = consFun.exprId -> consFun.instantiationId.get
  
  val prodFunsById = LinkedHashMap.empty[ConcreteFunId, Set[ConcreteFunProducer]].withDefaultValue(Set.empty)
  val consFunsById = LinkedHashMap.empty[ConcreteCallSiteId, Set[ConcreteFunConsumer]].withDefaultValue(Set.empty)

  // handle clashes for dead param elim
  val (liveParams, liveCallSiteParams) =
    def isSyntheticRoot(prodFun: ConcreteFunProducer): Bool =
      val instId = prodFun.instantiationId.get
      collector.synthesizedInstIdToFunSym.get(instId).exists: rootFunSym =>
        prodFun.funId match
          case (funSym: TermSymbol, _) =>
            (collector.funToSccRep(funSym), collector.funToSccRep(rootFunSym)) match
            case S(rep1) -> S(rep2) => rep1 is rep2
            case _ => false
          case _ => false
    end isSyntheticRoot

    for (prodFun, _) <- funDests do
      prodFunsById(prodFun.concreteId) = prodFunsById(prodFun.concreteId) + prodFun
    for (consFun, _) <- funSrcs do
      consFunsById(consFun.concreteId) = consFunsById(consFun.concreteId) + consFun

    val prodRoots = Buffer.empty[(ConcreteFunProducer, Int)]
    for (prodFun, dests) <- funDests do
      if isSyntheticRoot(prodFun) || dests.contains(NoCons) then
        prodFun.params.indices.foreach(i => prodRoots += ((prodFun, i)))
      prodFun.params.zipWithIndex.foreach:
        case (ConsVar(s), i) =>
          val ubs = constraintSolver.upperBounds(s.uid)
          if ubs.exists(!_.isInstanceOf[ConsVar]) then
            prodRoots += ((prodFun, i))
        case (_, i) =>
          prodRoots += ((prodFun, i))

    val consRoots = Buffer.empty[(ConcreteFunConsumer, Int)]
    for (consFun, srcs) <- funSrcs do
      if srcs.contains(NoProd) then
        consFun.params.indices.foreach(i => consRoots += ((consFun, i)))

    val result = FlowWebComputation[(ConcreteFunProducer, Int), (ConcreteFunConsumer, Int)](
      (prodFun, idx) => funDests(prodFun).collect:
        case c: ConcreteFunConsumer => (c, idx),
      (consFun, idx) => funSrcs(consFun).collect:
        case p: ConcreteFunProducer => (p, idx),
      prodRoots,
      consRoots,
    )
    (result.markedProducers, result.markedConsumers)
  end val
  
  
  val eliminableParamsById: Map[ConcreteFunId, Set[Int]] =
    (for (prodId, prodFuns) <- prodFunsById yield
      val paramCount = prodFuns.head.params.size
      val live = prodFuns.iterator
        .flatMap: prodFun =>
          prodFun.params.indices.collect:
            case i if liveParams((prodFun, i)) => i
        .toSet
      val eliminable = (0 until paramCount).filter(i => !live(i)).toSet
      prodId -> eliminable
    ).filter(_._2.nonEmpty).toMap
  
  val eliminableCallSiteArgsById: Map[ConcreteCallSiteId, Set[Int]] =
    (for (consId, consFuns) <- consFunsById yield
      val argCount = consFuns.head.params.size
      val live = MutSet.empty[Int]
      for consFun <- consFuns do
        for
          i <- consFun.params.indices
          if liveCallSiteParams((consFun, i))
        do live.add(i)
        for case prodFun: ConcreteFunProducer <- funSrcs(consFun) do
          if prodFun.restParam.isDefined then
            live ++= (prodFun.params.size until consFun.params.size)
        if funSrcs(consFun).contains(NoProd) then
          live ++= consFun.params.indices
      val eliminable = (0 until argCount).filter(i => !live(i)).toSet
      consId -> eliminable
    ).filter(_._2.nonEmpty).toMap
  
  def eliminableParamsFor(funId: FunId, instId: InstantiationId): Set[Int] =
    eliminableParamsById.getOrElse(funId -> instId, Set.empty)
  
  def eliminableArgsFor(exprId: ResultId, instId: InstantiationId): Set[Int] =
    eliminableCallSiteArgsById.getOrElse(exprId -> instId, Set.empty)
  
  if tl.doTrace then
    def showRefSite(resultId: ResultId): Str =
      resultId.getReferredFun match
        case Some(fun) => s"${fun.nme}@$resultId"
        case None => resultId.getResult match
          case Value.Ref(sym, _) => s"${sym.nme}@$resultId"
          case res => s"$res@$resultId"
    end showRefSite

    def showInstId(instId: InstantiationId): Str =
      if instId.isEmpty then "<root>" else instId.map(showRefSite).mkString(".")
    end showInstId

    def showProdFun(prodFun: ConcreteFunProducer): Str =
      def showFunId(funId: FunId): Str = funId match
        case (funSym: Symbol, whichParamList) => s"${funSym.nme}#$whichParamList"
        case exprId: ResultId => exprId.getResult match
          case Lambda(_, _) => s"lambda@$exprId"
          case _ => showRefSite(exprId)
      val inst = prodFun.instantiationId.fold("")(instId => s" @ ${showInstId(instId)}")
      s"prodfun ${showFunId(prodFun.funId)}$inst"
    end showProdFun

    tl.log(">>> dead-param-elim results >>>")
    for (prodFun, _) <- funDests.toSeq.sortBy(pair => showProdFun(pair._1)) do
      eliminableParamsById.get(prodFun.concreteId) match
        case Some(elim) =>
          tl.log(s"${showProdFun(prodFun)} -> eliminable: {${elim.toSeq.sorted.mkString(", ")}}")
        case None =>
          tl.log(s"${showProdFun(prodFun)} -> all params live")
    tl.log("<<< dead-param-elim results <<<")
  end if
end DeadParamElimSolver


class Rewrite(val deadParamElimSolver: DeadParamElimSolver)(using Raise):
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
      ((funId, instId), _) <- deadParamElimSolver.eliminableParamsById
      if instId.nonEmpty
      if !collector.synthesizedInstIdToFunSym.contains(instId.head :: Nil)
      path <- instId.inits
      if path.nonEmpty
    do mkNewPolyFnSyms(path)
    for
      ((callId, instId), _) <- deadParamElimSolver.eliminableCallSiteArgsById
      if instId.nonEmpty
      if !collector.synthesizedInstIdToFunSym.contains(instId.head :: Nil)
      path <- instId.inits
      if path.nonEmpty
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
            filterParamList(pl, deadParamElimSolver.eliminableParamsFor((funSym, whichParamList), instId))
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
      end newRefId
    
      p match
      case ref@FunRef(f) if newPolyFnSyms.isDefinedAt(newRefId(ref.uid, f)) =>
        val (bms, tSym) = newPolyFnSyms(newRefId(ref.uid, f))(f)
        k(Value.Ref(bms, S(tSym)))
      case _ => super.applyPath(p)(k)

    override def applyValue(v: Value)(k: Value => Block): Block = v match
      case ref@Value.Ref(l: VarSymbol, _) if activeEliminatedParams(l) =>
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
      case c@Call(fun, args) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableArgsFor(c.uid, instId)
        applyPath(fun): fun2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (fun2 is fun) && (args2 is args) then c
              else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall).withLocOf(c)
            )
      case i@Instantiate(mut, cls, args) if args.forall(_.spread.isEmpty) =>
        val eliminable = deadParamElimSolver.eliminableArgsFor(i.uid, instId)
        applyPath(cls): cls2 =>
          rewriteArgs(args, eliminable): args2 =>
            k(
              if (cls2 is cls) && (args2 is args) then i
              else Instantiate(mut, cls2, args2).withLocOf(i)
            )
      case _ => super.applyResult(r)(k)
    
    override def applyLam(lam: Lambda): Lambda =
      val (params2, removed) = filterParamList(lam.params, deadParamElimSolver.eliminableParamsFor(lam.uid, instId))
      val body2 = withEliminatedParams(removed):
        applyFunBodyLikeBlock(lam.body)
      if (params2 is lam.params) && (body2 is lam.body) then lam else Lambda(params2, body2)
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      val own2 = fun.owner.mapConserve(_.subst)
      val sym2 = fun.sym.subst
      val dSym2 = fun.dSym.subst
      val (params2, removed) = filterFunParams(fun.dSym, fun.params)
      val body2 = withEliminatedParams(removed):
        applyFunBodyLikeBlock(fun.body)
      if (own2 is fun.owner) && (sym2 is fun.sym) && (dSym2 is fun.dSym) &&
          (params2 is fun.params) && (body2 is fun.body)
      then fun else FunDefn(own2, sym2, dSym2, params2, body2)(fun.forceTailRec)
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
          filterParamList(pl, deadParamElimSolver.eliminableParamsFor((funSym, whichParamList), instId))
    end filterFunParams
    
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
        case Continue(label) => Continue(mapping.getOrElse(label, label).asInstanceOf[LabelSymbol])
        case _ => super.applyBlock(b)

      override def applyDefn(defn: Defn)(k: Defn => Block): Block =
        defn match
        case fun: FunDefn =>
          assert(fun.owner.isEmpty)
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
            case ParamList(flags, params, restParam) =>
              def handleSingleParam(p: Param) =
                val Param(flags, sym, sign, modulefulness) = p
                oldParamSyms.append(sym)
                val newSym = new VarSymbol(sym.id)
                assert(!mapping.isDefinedAt(sym))
                mapping(sym) = newSym
                Param(flags, newSym, sign, modulefulness)
              val params2 = params.map(handleSingleParam)
              val rest2 = restParam.map(handleSingleParam)
              ParamList(flags, params2, rest2)
          val body2 = applyFunBodyLikeBlock(fun.body)
          for s <- oldParamSyms do mapping.remove(s)
          if newlyCreated then
            Scoped(Set.single(sym2), k(FunDefn(N, sym2, dSym2, params2, body2)(fun.forceTailRec)))
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
        val bodyWithCorrectSymbols = new RefreshSymbol(refreshParamMap).applyBlock(transformedBody)
        FunDefn(
          N, bms, tSym, refreshedParams,
          bodyWithCorrectSymbols)(fDefn.forceTailRec)
    
    val inplaceRewrittenFunBodies = Map.from[TermSymbol, Block]:
      for (selfInstId, funSym) <- collector.synthesizedInstIdToFunSym yield
        val fDefn = pre.res.funSymToFunDefn(funSym)
        funSym -> new Rewriter(selfInstId).rewriteFunBody(funSym, fDefn.params, fDefn.body)
    
    val newMainBody =
      object mainRewriter extends Rewriter(Nil):
        override def applyFunDefn(fun: FunDefn): FunDefn =
          inplaceRewrittenFunBodies.get(fun.dSym) match
            case Some(rewrittenBody) =>
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, rewrittenBody)(fun.forceTailRec)
            case None => super.applyFunDefn(fun)
      Scoped(
        Set.from(newPolyFuns.map(_.sym)),
        mainRewriter.applyBlock(pre.b))
    
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
  ): Program =
    val fState = new FlowAnalysis.State
    val flowAnalysisRes = FlowAnalysis(p.main, mono = cfg.deadParamElim.exists(_.mono))
    val deadParamElimSolver = new DeadParamElimSolver(flowAnalysisRes)
    val rewrite = new Rewrite(deadParamElimSolver)
    Program(p.imports, rewrite.newBody)
