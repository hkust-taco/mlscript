package hkmc2
package codegen
package flowAnalysis

import hkmc2.semantics.*
import hkmc2.utils.*, shorthands.*
import utils.*


enum EffectSummary:
  case Pure, UnsafeEta


object EffectAnalysis:


  def summarize(effectVar: StratVar): EffectSummary =
    if effectVar.lowerBounds.forall(_.isInstanceOf[StratVar])
    then EffectSummary.Pure
    else EffectSummary.UnsafeEta

  def logResults(solver: FlowConstraintSolver)(using tl: TraceLogger): Unit =
    given fState: FlowAnalysis.State = solver.fState
    given raise: Raise = solver.preAnalyzer.raise
    given symbolPrinter: SymbolPrinter = solver.preAnalyzer.traceSymbolPrinter
    given ShowCfg = ShowCfg.internal

    def showFunction(id: ConcreteId[FunId]): Str =
      s"function ${id.showConcreteFunId}"

    def showPath(path: Path): Str = path match
      case Value.SimpleRef(sym) => symbolPrinter.printSymbol(sym)
      case Value.MemberRef(_, disamb) => symbolPrinter.printSymbol(disamb)
      case Select(_, name) => name.name
      case _ => "<dynamic>"

    def showCall(id: ConcreteId[ResultId]): Str =
      val call = id.exprId.getResult match
        case Call(fun, _) => s"call ${showPath(fun)}@${id.exprId.showRefSite}"
        case Instantiate(_, cls, _) => s"instantiate ${showPath(cls)}@${id.exprId.showRefSite}"
        case other => s"call $other@${id.exprId.showRefSite}"
      s"$call @ ${id.instId.showInstId}"

    tl.log(">>> effect-analysis results >>>")
    solver.functionEffectVars.iterator.map: (id, effect) =>
      s"${showFunction(id)} -> ${summarize(effect)}"
    .toSeq.sorted.foreach(tl.log(_))
    solver.callEffectVars.iterator.map: (id, effect) =>
      s"${showCall(id)} -> ${summarize(effect)}"
    .toSeq.sorted.foreach(tl.log(_))
    tl.log("<<< effect-analysis results <<<")
  end logResults
end EffectAnalysis
