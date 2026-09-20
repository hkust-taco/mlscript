package hkmc2
package codegen
package flowAnalysis

import hkmc2.semantics.*
import hkmc2.utils.*, shorthands.*
import utils.*


enum EffectSummary:
  case Pure, UnsafeEta


case class EffectAnalysisResult(
  latentEffects: Map[ConcreteId[FunId], EffectSummary],
  callEffects: Map[ConcreteId[ResultId], EffectSummary],
)


object EffectAnalysis:


  def summarize(effectVar: StratVar): EffectSummary =
    if effectVar.lowerBounds.contains(UnsafeEta)
    then EffectSummary.UnsafeEta
    else EffectSummary.Pure

  def apply(solver: FlowConstraintSolver)(using tl: TraceLogger): EffectAnalysisResult =
    given fState: FlowAnalysis.State = solver.fState
    given eState: Elaborator.State = solver.eState


    val result = EffectAnalysisResult(
      solver.functionEffectVars.iterator.map((id, effect) => id -> summarize(effect)).toMap,
      solver.callEffectVars.iterator.map((id, effect) => id -> summarize(effect)).toMap,
    )

    if tl.doTrace then logResult(result)
    result
  end apply

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
    result.latentEffects.iterator.map: (id, effect) =>
      s"${showFunction(id)} -> $effect"
    .toSeq.sorted.foreach(tl.log(_))
    result.callEffects.iterator.map: (id, effect) =>
      s"${showCall(id)} -> $effect"
    .toSeq.sorted.foreach(tl.log(_))
    tl.log("<<< effect-analysis results <<<")
  end logResult
end EffectAnalysis
