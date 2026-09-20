package hkmc2
package codegen
package flowAnalysis

import hkmc2.semantics.*
import hkmc2.utils.*, shorthands.*
import utils.*


enum EffectSummary:
  case Pure, MayRaise


case class EffectAnalysisResult(
  latentEffects: Map[ConcreteId[FunId], EffectSummary],
  callEffects: Map[ConcreteId[ResultId], EffectSummary],
)


object EffectAnalysis:
  def apply(pgrm: Program, cfg: Config.EffectAnalysis)(using
    Config,
    TraceLogger,
    Elaborator.State,
    Raise,
    SymbolPrinter,
  ): EffectAnalysisResult =
    analyze(FlowAnalysis(
      pgrm,
      mono = cfg.mono,
      nonAffineTracking = false,
      accumulatorTracking = false,
      effectTracking = true,
      instantiateMayRaise = config.checkInstantiateEffect,
    ))

  def mkTraceLogger(cfg: Config.EffectAnalysis, outerTl: TL): TraceLogger =
    new TraceLogger(using outerTl.debugPrinter):
      override def doTrace: Bool = scope match
        case S(FlowAnalysis.TraceScope.NonAffineSyms | FlowAnalysis.TraceScope.AccumulatorSym) => false
        case _ => cfg.debug
      override def emitDbg(str: Str): Unit =
        outerTl.emitDbg(s"effect-analysis > $str")

  private def analyze(solver: FlowConstraintSolver): EffectAnalysisResult =
    given fState: FlowAnalysis.State = solver.fState
    given eState: Elaborator.State = solver.eState
    given tl: TraceLogger = solver.tl

    def summary(effect: StratVar): EffectSummary =
      if effect.lowerBounds.contains(MayRaise)
      then EffectSummary.MayRaise
      else EffectSummary.Pure

    val result = EffectAnalysisResult(
      solver.functionEffectVars.iterator.map((id, effect) => id -> summary(effect)).toMap,
      solver.callEffectVars.iterator.map((id, effect) => id -> summary(effect)).toMap,
    )

    if tl.doTrace then logResult(result)
    result
  end analyze

  private def logResult(result: EffectAnalysisResult)(using
    tl: TraceLogger,
    fState: FlowAnalysis.State,
    eState: Elaborator.State,
  ): Unit =
    def showRefSite(resultId: ResultId): Str =
      resultId.getReferredFun match
        case Some(fun) => s"${fun.nme}@$resultId"
        case None => s"${resultId.getResult}@$resultId"

    def showInstId(instId: InstantiationId): Str =
      if instId.isEmpty then "<root>" else instId.map(showRefSite).mkString(".")

    def showFunction(id: ConcreteId[FunId]): Str =
      val name = id.exprId match
        case (funSym: TermSymbol, whichParamList) => s"${funSym.nme}#$whichParamList"
        case exprId: ResultId => s"lambda@$exprId"
      s"function $name @ ${showInstId(id.instId)}"

    def showPath(path: Path): Str = path match
      case Value.SimpleRef(sym) => sym.nme
      case Value.MemberRef(_, disamb) => disamb.nme
      case Select(_, name) => name.name
      case _ => "<dynamic>"

    def showCall(id: ConcreteId[ResultId]): Str =
      val call = id.exprId.getResult match
        case Call(fun, _) => s"call ${showPath(fun)}@${id.exprId}"
        case Instantiate(_, cls, _) => s"instantiate ${showPath(cls)}@${id.exprId}"
        case other => s"call $other@${id.exprId}"
      s"$call @ ${showInstId(id.instId)}"

    tl.log(">>> effect-analysis results >>>")
    result.latentEffects.toSeq.sortBy((id, _) => showFunction(id)).foreach: (id, effect) =>
      tl.log(s"${showFunction(id)} -> $effect")
    result.callEffects.toSeq.sortBy((id, _) => showCall(id)).foreach: (id, effect) =>
      tl.log(s"${showCall(id)} -> $effect")
    tl.log("<<< effect-analysis results <<<")
  end logResult
end EffectAnalysis
