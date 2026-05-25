package hkmc2
package codegen

import scala.annotation.tailrec
import scala.collection.mutable.{Map as MutMap, Set as MutSet}

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.flowAnalysis.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.LinkedHashMap


class EtaExpansionSolver(val constraintSolver: FlowConstraintSolver):
  private val tl = constraintSolver.tl
  given FlowAnalysis.State = constraintSolver.collector.fState
  assert(constraintSolver.collector.mono)


  private val cache = MutMap.empty[ProdFun, Ls[Int]]

  // the result is a list describing the target shape
  // e.g., 1 :: 0 :: 2 :: 3 :: Nil means
  // fun f(x) = x
  // will be expanded to
  // fun f(x)()(p1, p2)(p3, p4, p5) = x()(p1, p2)(p3, p4, p5)
  private def etaExpansionTargetShapes(pf: ProdFun)(using processing: Set[ProdFun]): Ls[Int] =
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
      end prodFunIsAffine
      
      res match
      case resPf: ProdFun =>
        if isDeclaredNextParamList(resPf) || prodFunIsAffine(resPf) then
          etaExpansionTargetShapes(resPf)
        else Nil
      case ProdVar(s) =>
        // iterate through all the lower bounds of prodvar
        @tailrec
        def go(lbs: Ls[ProdStrat], res: Opt[Ls[Int]]): Ls[Int] =
          lbs match
          case Nil => res.getOrElse(Nil)
          case h :: t =>
            h match
            case ProdVar(s) => go(t, res)
            case pf: ProdFun =>
              if isDeclaredNextParamList(pf) then
                etaExpansionTargetShapes(pf)
              else if prodFunIsAffine(pf) then
                val curRes = etaExpansionTargetShapes(pf)
                val mergedRes = res match
                  case N => curRes
                  case S(prevRes) => prevRes.zip(curRes).map: (a, b) =>
                    assert(a === b)
                    a
                go(t, S(mergedRes))
              else Nil
            case UnknownProd => Nil
            case _: Ctor => Nil
        end go
        
        go(constraintSolver.lowerBounds(s.uid), N)
      case UnknownProd => Nil
      case _: Ctor => Nil
    end funResShape

    cache.get(pf) match
    case S(res) => res
    case N =>
      val paramCount = pf.params.size + pf.restParam.fold(0)(_ => 1)
      if !processing.contains(pf) then
        val res = paramCount :: funResShape(pf.res)
        cache(pf) = res
        res
      else
        cache(pf) = paramCount :: Nil
        Nil
  end etaExpansionTargetShapes

  val funShape = LinkedHashMap.empty[TermSymbol | ResultId, Ls[Int]]

  for pf <- constraintSolver.funDests.keysIterator do
    pf.exprId match
    case lamId: ResultId => funShape.getOrElseUpdate(lamId, etaExpansionTargetShapes(pf)(using Set.empty))
    case (funSym: TermSymbol, 0) => funShape.getOrElseUpdate(funSym, etaExpansionTargetShapes(pf)(using Set.empty))
    case _ => ()


  private def showFunShapeId(id: TermSymbol | ResultId): Str = id match
    case funSym: TermSymbol => funSym.nme
    case lamId: ResultId =>
      lamId.getResult match
      case Lambda(_, _) => s"lambda@$lamId"
      case r => lastWords(s"not lambda $r")

  private def checkIsEtaExpanded(
    id: TermSymbol | ResultId,
    shape: Ls[Int]
  ): Bool = id match
    case funSym: TermSymbol =>
      val prev = constraintSolver.preAnalyzer.res.funSymToFunDefn(funSym).params.size
      val now = shape.size
      now > prev
    case lamId: ResultId => shape.size > 1

  def hasEtaExpansionTargets: Bool =
    funShape.exists:
      case (id, shape) => checkIsEtaExpanded(id, shape)

  if tl.doTrace then
    tl.log(">>> eta-expansion targets shapes >>>")
    for
      (id, shape) <- funShape
      if checkIsEtaExpanded(id, shape)
    do
      tl.log(s"${showFunShapeId(id)}: ${shape.mkString("[", ", ", "]")}")
    tl.log("<<< eta-expansion targets shapes <<<")
  end if
end EtaExpansionSolver


class EtaExpansionRewrite(val etaExpansionSolver: EtaExpansionSolver)(using Raise):
  private val constraintSolver = etaExpansionSolver.constraintSolver
  private val pre = constraintSolver.preAnalyzer
  given eState: Elaborator.State = constraintSolver.eState
  given fState: FlowAnalysis.State = constraintSolver.fState

  private case class EtaParamList(params: ParamList, args: Ls[Arg])

  def apply(): Program =
    if etaExpansionSolver.hasEtaExpansionTargets then
      val newBody = Rewriter().applyBlock(pre.pgrm.main)
      if newBody is pre.pgrm.main then pre.pgrm
      else Program(pre.pgrm.imports, newBody)
    else pre.pgrm

  class Rewriter extends BlockTransformer(SymbolSubst.Id):
    private var activeEtaArgss: Ls[Ls[Arg]] = Nil
    
    private def withEtaArgss[A](etaArgss: Ls[Ls[Arg]])(thunk: => A): A =
      val saved = activeEtaArgss
      activeEtaArgss = etaArgss
      val res = thunk
      activeEtaArgss = saved
      res
    
    private def paramCount(pl: ParamList): Int =
      pl.params.size + pl.restParam.fold(0)(_ => 1)
    
    private def etaParamLists(id: TermSymbol | ResultId, existingParams: Ls[ParamList]): Ls[EtaParamList] =
      etaExpansionSolver.funShape.get(id).toList.flatMap: targetShape =>
        val existingShape = existingParams.map(paramCount)
        if targetShape.startsWith(existingShape) then
          targetShape.drop(existingShape.size).zipWithIndex.map:
            case (count, idx) =>
              val params = (0 until count).toList.map: i =>
                Param.simple(new VarSymbol(new Tree.Ident(s"eta$$$idx$$$i")))
              EtaParamList(
                ParamList(ParamListFlags.empty, params, N),
                params.map(p => Arg(N, p.sym.asSimpleRef)),
              )
        else
          lastWords("not the same shape?")
    
    private def etaCall(base: Path): Call =
      Call(base, activeEtaArgss.ne_!)(isMlsFun = true, mayRaiseEffects = true, explicitTailCall = false)
    
    override def applyBlock(b: Block): Block = b match
      case Return(res) if activeEtaArgss.nonEmpty =>
        applyResult(res): res2 =>
          if activeEtaArgss.isEmpty then Return(res2)
          else res2 match
          case p: Path =>
            Return(etaCall(p).withLocOf(res2))
          case c @ Call(fun, argss) =>
            Return(
              Call(fun, (argss ++ activeEtaArgss).ne_!)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
          case _ =>
            val tmp = TempSymbol(N, "eta$res")
            Scoped(
              Set.single(tmp),
              Assign(tmp, res2, Return(etaCall(tmp.asPath).withLocOf(res2))))
      case _ => super.applyBlock(b)
    
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
      val etaParams = etaParamLists(fun.dSym, fun.params)
      val params2 = fun.params.mapConserve(applyParamList) ::: etaParams.map(_.params)
      val body2 = withEtaArgss(etaParams.map(_.args)):
        applyFunBodyLikeBlock(fun.body)
      if (params2 is fun.params) && (body2 is fun.body) then fun
      else FunDefn(fun.owner, fun.sym, fun.dSym, params2, body2)(fun.configOverride, fun.annotations)
    
    override def applyLam(lam: Lambda): Lambda =
      val etaParams = etaParamLists(lam.uid, lam.params :: Nil)
      val body2 = withEtaArgss(etaParams.map(_.args)):
        applyFunBodyLikeBlock(lam.body)
      val wrappedBody = etaParams.map(_.params).foldRight(body2): (params, body) =>
        Return(Lambda(params, body)(Nil))
      if (wrappedBody is lam.body) then lam
      else Lambda(lam.params, wrappedBody)(lam.annot).withLocOf(lam)
  end Rewriter
  
end EtaExpansionRewrite


object EtaExpansion:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    symbolPrinter: SymbolPrinter,
  ): Program =
    cfg.etaExpansion match
    case N => p
    case S(eCfg) =>
      FlowAnalysis.mkTraceLogger(eCfg.config, "eta-expansion > ", tl).givenIn:
        val flowAnalysisRes = FlowAnalysis(
          p,
          mono = true,
          nonAffineTracking = false,
          accumulatorTracking = false,
        )
        new EtaExpansionRewrite(new EtaExpansionSolver(flowAnalysisRes)).apply()
