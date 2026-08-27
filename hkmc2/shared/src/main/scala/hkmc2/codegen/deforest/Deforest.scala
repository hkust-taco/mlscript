package hkmc2
package codegen
package deforest

import utils.*
import hkmc2.utils.*, shorthands.*
import semantics.*
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap}
import hkmc2.codegen.flowAnalysis.*
import hkmc2.utils.Scope

type CtorDtorId = ConcreteId[ResultId]

sealed abstract class FinalDest
case class FinalDestMatch(dtor: CtorDtorId, sels: Set[CtorDtorId]) extends FinalDest
case class FinalDestSel(dtors: Set[CtorDtorId], field: SelField) extends FinalDest

class DeforestFusionSolver(val constraintSolver: FlowConstraintSolver)(using val cfg: Config):
  given preAnalyzer: FlowPreAnalyzer = constraintSolver.preAnalyzer
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  given tl: TraceLogger = constraintSolver.tl
  given Raise = preAnalyzer.raise

  private def pp(id: CtorDtorId): Str =
    given ShowCfg = ShowCfg.internal
    given symbolPrinter: SymbolPrinter = constraintSolver.preAnalyzer.symbolPrinter
    given dbgScope: Scope = symbolPrinter.dbgScp
    new codegen.Printer().print(id.exprId.getResult).mkString()

  private def pp(field: SelField): Str =
    field match
      case field: TermSymbol => field.nme
      case idx: Int => idx.toString

  private def selAndDtorIsSameConsumer(dtor: CtorDtorId, sels: Iterable[CtorDtorId]): Boolean =
    sels.forall:
      case ConcreteId(selExpr, instId) =>
        instId == dtor.instId &&
        preAnalyzer.res.getEnclosingMatchesForSel(selExpr).exists(_._1 == dtor.exprId) &&
        selExpr.getResult.matches:
          case TrackableSelect(from, _, _) => from === dtor.exprId.getResult
  
  val finalCtorDests = LinkedHashMap.empty[CtorDtorId, FinalDest]
  val finalDtorSrcs = LinkedHashMap.empty[CtorDtorId, Set[CtorDtorId]]
  val fusingCtorInfo = MutMap.empty[CtorDtorId, Ctor]
  val fusingDtorInfo = MutMap.empty[CtorDtorId, ConcreteCtorConsumer]
  
  locally {
    def mergeDests(dests: Set[ConcreteCtorConsumer | MarkerConsStrat]): Opt[FinalDest] =
      def selsSelectingTheSameSymbol(sels: Set[FieldSel]) =
        sels.map(s => s.field).size == 1
      if dests.exists(_.isInstanceOf[MarkerConsStrat]) then
        N
      else
        val (dtors, sels) = dests.partitionMap:
          case d: Dtor => Left(d)
          case fs: FieldSel => Right(fs)
          case _ => die
        if dtors.size == 0 && selsSelectingTheSameSymbol(sels) then
          S(FinalDestSel(
            sels.map(_.concreteId),
            sels.head.field
          ))
        else if dtors.size != 1 then N
        else
          val dtor = dtors.head
          if selAndDtorIsSameConsumer(
            dtor.concreteId,
            sels.map(s => s.concreteId)
          ) then
            S(FinalDestMatch(
              dtor.concreteId,
              sels.map(_.concreteId)
            ))
          else N
    end mergeDests

    val prodRoots =
      for
        ctor <- constraintSolver.ctorsWithDests
        if mergeDests(ctor.dests.toSet).isEmpty
      yield ctor
    val consRoots =
      for
        dtor <- constraintSolver.consumersWithSrcs
        if dtor.srcs.contains(UnknownProd)
      yield dtor

    val result = FlowWebComputation[Ctor, ConcreteCtorConsumer](
      p => p.dests.collect:
        case c: ConcreteCtorConsumer => c,
      c => c.srcs.collect:
        case p: Ctor => p,
      prodRoots,
      consRoots,
    )
    val toRemoveCtor = result.markedProducers
    val toRemoveDtor = result.markedConsumers

    for
      ctor <- constraintSolver.ctorsWithDests
      if !toRemoveCtor(ctor)
    do
      finalCtorDests(ctor.concreteId) = mergeDests(ctor.dests.toSet).get
      fusingCtorInfo(ctor.concreteId) = ctor
    for
      dtor <- constraintSolver.consumersWithSrcs
      if !toRemoveDtor(dtor)
    do
      finalDtorSrcs(dtor.concreteId) =
        // srcs are always Ctors after constraint solving
        dtor.srcs.iterator.map(_.asInstanceOf[Ctor].concreteId).toSet
      fusingDtorInfo(dtor.concreteId) = dtor
  }

  tl.log(">>> fusing >>>")
  for case (c, dest) <- finalCtorDests do
    tl.log(s"${pp(c)} ->")
    dest match
    case FinalDestMatch(dtor, sels) =>
      tl.log(s"\tmatch: ${pp(dtor)}")
      for s <- sels.toSeq.sortBy(_.exprId.uid) do tl.log(s"\tfields: ${pp(s)}")
    case FinalDestSel(dtors, field) =>
      tl.log(s"\tselect: ${pp(field)}")
  tl.log("<<< fusing <<<")
end DeforestFusionSolver


object Deforest:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    symbolPrinter: SymbolPrinter,
  ): Program =
    // TODO: handle see through imported modules
    val dCfg = cfg.deforest.getOrElse(lastWords("deforestation is disabled in Config"))
    val flowAnalysisRes = FlowAnalysis(
      p,
      mono = dCfg.mono,
      nonAffineTracking = dCfg.effectiveTrackNonAffine,
      accumulatorTracking = dCfg.effectiveTrackAccumulator,
    )
    val solver = new DeforestFusionSolver(flowAnalysisRes)
    if solver.finalCtorDests.isEmpty && solver.finalDtorSrcs.isEmpty then p
    else
      val rewrite = new DeforestRewriter(solver)
      rewrite()

