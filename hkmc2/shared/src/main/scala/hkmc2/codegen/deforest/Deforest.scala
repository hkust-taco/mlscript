package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap}
import hkmc2.codegen.flowAnalysis.*

sealed abstract class FinalDest
case class FinalDestMatch(dtor: CtorDtorId, sels: Set[CtorDtorId]) extends FinalDest
case class FinalDestSel(dtors: Set[CtorDtorId], field: SelField) extends FinalDest

class DeforestFusionSolver(val constraintSolver: FlowConstraintSolver):
  given preAnalyzer: FlowPreAnalyzer = constraintSolver.preAnalyzer
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  given tl: TraceLogger = constraintSolver.tl

  private def selAndDtorIsSameConsumer(dtor: CtorDtorId, sels: Iterable[CtorDtorId]): Boolean =
    sels.forall:
      case CtorDtorId(selExpr, instId) =>
        instId == dtor.instId &&
        preAnalyzer.res.getEnclosingMatchesForSel(selExpr).exists(_._1 == dtor.exprId) &&
        selExpr.getResult.matches:
          case TrackableSelect(from, _, _) => from === dtor.exprId.getResult
  
  val finalCtorDests = LinkedHashMap.empty[CtorDtorId, FinalDest]
  val finalDtorSrcs = LinkedHashMap.empty[CtorDtorId, Set[CtorDtorId]]
  val fusingCtorInfo = MutMap.empty[CtorDtorId, ConcreteProducer]
  val fusingDtorInfo = MutMap.empty[CtorDtorId, ConcreteConsumer]
  
  locally {
    def mergeDests(dests: Set[ConcreteConsumer | NoCons.type]): Opt[FinalDest] =
      def selsSelectingTheSameSymbol(sels: Set[FieldSel]) =
        sels.map(s => s.field).size == 1
      if dests.contains(NoCons) then N
      else
        val (dtors, sels) = dests.partitionMap:
          case d: Dtor => Left(d)
          case fs: FieldSel => Right(fs)
          case _ => die
        if dtors.size == 0 && selsSelectingTheSameSymbol(sels) then
          S(FinalDestSel(
            sels.map(_.toCtorDtorId),
            sels.head.field
          ))
        else if dtors.size != 1 then N
        else
          val dtor = dtors.head
          if selAndDtorIsSameConsumer(
            dtor.toCtorDtorId,
            sels.map(s => s.toCtorDtorId)
          ) then
            S(FinalDestMatch(
              CtorDtorId(dtor.scrutExprId, dtor.instantiationId.get),
              sels.map: s =>
                CtorDtorId(s.exprId, s.instantiationId.get)
            ))
          else N
    end mergeDests

    val prodRoots =
      for
        (ctor, dests) <- constraintSolver.ctorDests
        if mergeDests(dests).isEmpty
      yield ctor
    val consRoots =
      for
        (dtor, srcs) <- constraintSolver.dtorSrcs
        if srcs.contains(NoProd)
      yield dtor

    val result = FlowWebComputation[ConcreteProducer, ConcreteConsumer](
      p => constraintSolver.ctorDests(p).collect:
        case c: ConcreteConsumer => c,
      c => constraintSolver.dtorSrcs(c).collect:
        case p: ConcreteProducer => p,
      prodRoots,
      consRoots,
    )
    val toRemoveCtor = result.markedProducers
    val toRemoveDtor = result.markedConsumers

    for
      (ctor, dests) <- constraintSolver.ctorDests
      if !toRemoveCtor(ctor)
    do
      finalCtorDests(ctor.toCtorDtorId) = mergeDests(dests).get
      fusingCtorInfo(ctor.toCtorDtorId) = ctor
    for
      (dtor, srcs) <- constraintSolver.dtorSrcs
      if !toRemoveDtor(dtor)
    do
      finalDtorSrcs(dtor.toCtorDtorId) =
        // srcs are always ConcreteProducers after constraint solving
        srcs.map(_.asInstanceOf[ConcreteProducer].toCtorDtorId)
      fusingDtorInfo(dtor.toCtorDtorId) = dtor
  }

  tl.log(">>> fusing >>>")
  for case (c, dest) <- finalCtorDests do
    tl.log(s"${c.pp} ->")
    dest match
    case FinalDestMatch(dtor, sels) =>
      tl.log(s"\t${dtor.pp}")
      for s <- sels.toSeq.sortBy(_.exprId) do tl.log(s"\t${s.pp}")
    case FinalDestSel(dtors, field) =>
      tl.log(s"\t${field}")
  tl.log("<<< fusing <<<")
end DeforestFusionSolver


object Deforest:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
  ): Program =
    // TODO: handle see through imported modules
    val flowAnalysisRes = FlowAnalysis(p, mono = cfg.deforest.exists(_.mono))
    val solver = new DeforestFusionSolver(flowAnalysisRes)
    if solver.finalCtorDests.isEmpty && solver.finalDtorSrcs.isEmpty then p
    else
      val rewrite = new DeforestRewriter(solver)
      rewrite()

