package hkmc2
package codegen

import scala.annotation.tailrec
import scala.collection.mutable.{Map as MutMap, LinkedHashMap}

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.flowAnalysis.*
import semantics.*

case class EtaTargets(paramCount: Int, hasRestParam: Bool, prodFuns: Set[ProdFun]):
  def paramInfo: (Int, Bool) = paramCount -> hasRestParam
  def ppParamInfo: Str = if hasRestParam then s"$paramCount+rest" else s"$paramCount"
  def pp: Str = s"$ppParamInfo${prodFuns.map(_.exprId).mkString("<", ", ", ">")}"

abstract class EtaExpansionResult extends FlowAnalysisSolverResult:
  def etaExpandedFunShape: collection.Map[ConcreteFunId, Ls[EtaTargets]]

  final def hasWorkToDo: Bool = etaExpandedFunShape.nonEmpty

  final def polyInstIds: Iterator[InstantiationId] =
    etaExpandedFunShape.keysIterator.map(_.instId)

end EtaExpansionResult


object NoEtaExpansion extends EtaExpansionResult:
  val etaExpandedFunShape = Map.empty[ConcreteFunId, Ls[EtaTargets]]


class EtaExpansionSolver(val constraintSolver: FlowConstraintSolver, tl: TraceLogger) extends EtaExpansionResult:
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  
  private val cache = MutMap.empty[ProdFun, Ls[EtaTargets]]
  
  // the result is a list describing the target shape
  // e.g., entries with arities of 1, 0, 2, 3 means
  // fun f(x) = x
  // will be expanded to
  // fun f(x)()(p1, p2)(p3, p4, p5) = x()(p1, p2)(p3, p4, p5)
  private def etaExpansionTargetShapes(pf: ProdFun)(using processing: Set[ProdFun]): Ls[EtaTargets] =
    given newProcessing: Set[ProdFun] = processing + pf
    def funResShape(res: ProdStrat) =
      def isDeclaredNextParamList(resPf: ProdFun): Bool =
        (pf.exprId, resPf.exprId) match
        case ((funSym1: TermSymbol, idx1: Int), (funSym2: TermSymbol, idx2: Int)) =>
          (funSym1 is funSym2) && idx2 === (idx1 + 1)
        case _ => false
      end isDeclaredNextParamList
      
      def prodFunIsAffine(pf: ProdFun) =
        pf.exprId match
        case lamId: ResultId =>
          lamId.getResult match
            case lamDef: Lambda => lamDef.affine
            case other => lastWords(s"expected lambda result, got $other")
        case (fSym: TermSymbol, whichPl: Int) =>
          val fnDefn = constraintSolver.collector.preAnalyzer.res.funSymToFunDefn(fSym)
          fnDefn.affineInfo.contains(whichPl)
        case (sym, _) => lastWords(s"prodFunIsAffine: expected TermSymbol funId, got $sym")
      end prodFunIsAffine
      
      res match
      case resPf: ProdFun =>
        if isDeclaredNextParamList(resPf) || prodFunIsAffine(resPf) then
          etaExpansionTargetShapes(resPf)
        else Nil
      case v: StratVar =>
        // iterate through all the lower bounds of prodvar
        val lbs = v.lowerBounds.iterator
        @tailrec
        def go(res: Opt[Ls[EtaTargets]]): Ls[EtaTargets] =
          if !lbs.hasNext then res.getOrElse(Nil)
          else lbs.next() match
            case pv: StratVar => go(res)
            case pf: ProdFun =>
              if isDeclaredNextParamList(pf) then
                etaExpansionTargetShapes(pf)
              else if prodFunIsAffine(pf) then
                val curRes = etaExpansionTargetShapes(pf)
                val mergedRes = res match
                  case N => curRes
                  case S(prevRes) => prevRes.zip(curRes).map: (a, b) =>
                    assert(a.paramInfo === b.paramInfo,
                      s"eta expansion targets disagree on arity: ${a.pp} vs ${b.pp}")
                    EtaTargets(a.paramCount, a.hasRestParam, a.prodFuns ++ b.prodFuns)
                go(S(mergedRes))
              else Nil
            case UnknownProd => Nil
            case _: Ctor => Nil
        end go
        
        val ubs = constraintSolver.AllUpperBounds(v)
        if ubs.exists:
          case _: ConsFun | UnknownCons => true
          case _ => false
        then go(N)
        else Nil
      case UnknownProd => Nil
      case _: Ctor => Nil
    end funResShape

    cache.get(pf) match
    case S(res) => res
    case N =>
      val targets = EtaTargets(pf.params.size, pf.restParam.isDefined, Set.single(pf))
      if !processing.contains(pf) then
        val res = targets :: funResShape(pf.res)
        cache(pf) = res
        res
      else
        cache(pf) = targets :: Nil
        Nil
  end etaExpansionTargetShapes

  val etaExpandedFunShape: LinkedHashMap[ConcreteFunId, Ls[EtaTargets]] = LinkedHashMap.empty


  for pf <- constraintSolver.prodFunsWithDests do
    def addFunShapeIfChanged(): Unit =
      def isEtaExpanded(funId: FunId, shape: Ls[EtaTargets]): Bool = funId match
        case (funSym: TermSymbol, _) =>
          val prev = constraintSolver.preAnalyzer.res.funSymToFunDefn(funSym).params.size
          val now = shape.size
          now > prev
        case _: ResultId => shape.size > 1
      end isEtaExpanded
      val id = pf.concreteId
      if !etaExpandedFunShape.contains(id) then
        val shape = etaExpansionTargetShapes(pf)(using Set.empty)
        if isEtaExpanded(id.exprId, shape) then etaExpandedFunShape(id) = shape
    end addFunShapeIfChanged
    pf.exprId match
    case _: ResultId => addFunShapeIfChanged()
    case (_: TermSymbol, 0) => addFunShapeIfChanged()
    case _ => ()

  if tl.doTrace then
    def showFunShapeId(id: ConcreteFunId): Str =
      val funStr = id.exprId match
        case (funSym: TermSymbol, _) => funSym.nme
        case lamId: ResultId =>
          lamId.getResult match
          case Lambda(_, _) => s"lambda@$lamId"
          case r => lastWords(s"not lambda $r")
      if id.instId.isEmpty then funStr else s"$funStr @ ${id.instId.showInstId}"
    end showFunShapeId
    
    tl.log(">>> eta-expansion targets shapes >>>")
    for (id, shape) <- etaExpandedFunShape do
      tl.log(s"${showFunShapeId(id)}: ${shape.map(_.ppParamInfo).mkString("[", ", ", "]")}")
    tl.log("<<< eta-expansion targets shapes <<<")
  end if
end EtaExpansionSolver


object EtaExpansion:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    ctx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
  ): Program = cfg.flowBasedOpt.fold(p):
    FlowAnalysisBasedRewrite.rewriteWith(p, _, dpe = false, dce = false)
