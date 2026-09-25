package hkmc2
package codegen

import utils.*
import hkmc2.utils.*, shorthands.*
import semantics.*
import hkmc2.codegen.flowAnalysis.*
import scala.collection.mutable.{LinkedHashMap, Buffer}


type ConcreteFunId = ConcreteId[FunId]
type ConcreteCallSiteId = ConcreteId[ResultId]



abstract class DeadParamElimResult extends FlowAnalysisSolverResult:
  def eliminableParamsById: collection.Map[ConcreteFunId, Set[Int]]
  def eliminableCallSiteArgsById: collection.Map[ConcreteCallSiteId, Set[Int]]

  final def hasWorkToDo: Bool =
    eliminableParamsById.nonEmpty || eliminableCallSiteArgsById.nonEmpty

  final def polyInstIds: Iterator[InstantiationId] =
    eliminableParamsById.keysIterator.map(_.instId) ++
    eliminableCallSiteArgsById.keysIterator.map(_.instId)

  final def eliminableParams(id: ConcreteFunId): Set[Int] =
    eliminableParamsById.getOrElse(id, Set.empty)
    
  final def eliminableCallSiteArgs(id: ConcreteCallSiteId): Set[Int] =
    eliminableCallSiteArgsById.getOrElse(id, Set.empty)

end DeadParamElimResult


object NoDeadParamElim extends DeadParamElimResult:
  val eliminableParamsById = Map.empty[ConcreteFunId, Set[Int]]
  val eliminableCallSiteArgsById = Map.empty[ConcreteCallSiteId, Set[Int]]


class DeadParamElimSolver(val constraintSolver: FlowConstraintSolver, traceLogger: TraceLogger) extends DeadParamElimResult:
  given tl: TraceLogger = traceLogger
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
  
  val eliminableParamsById: LinkedHashMap[ConcreteFunId, Set[Int]] = LinkedHashMap.empty
  val eliminableCallSiteArgsById: LinkedHashMap[ConcreteCallSiteId, Set[Int]] = LinkedHashMap.empty
  
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
    def showProdFun(prodFun: ProdFun): Str =
      def showFunId(funId: FunId): Str = funId match
        case (funSym: Symbol, whichParamList) => s"${funSym.nme}#$whichParamList"
        case exprId: ResultId => exprId.getResult match
          case Lambda(_, _) => s"lambda@$exprId"
          case _ => exprId.showRefSite
      val inst = prodFun.instantiationId.fold("")(instId => s" @ ${instId.showInstId}")
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


object DeadParamElim:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    ctx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
  ): Program = cfg.flowBasedOpt.fold(p):
    FlowAnalysisBasedRewrite.rewriteWith(p, _, eta = false, dce = false)
