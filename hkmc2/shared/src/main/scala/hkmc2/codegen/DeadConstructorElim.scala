package hkmc2
package codegen

import scala.collection.mutable.LinkedHashSet

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.flowAnalysis.*
import semantics.*


type ConcreteCtorId = ConcreteId[ResultId]


abstract class DeadConstructorElimResult extends FlowAnalysisSolverResult:
  def deadCtors: collection.Set[ConcreteCtorId]
  
  final def hasWorkToDo: Bool = deadCtors.nonEmpty
  
  final def polyInstIds: Iterator[InstantiationId] = deadCtors.iterator.map(_.instId)
  
end DeadConstructorElimResult


object NoDeadConstructorElim extends DeadConstructorElimResult:
  val deadCtors = Set.empty[ConcreteCtorId]


class DeadConstructorElimSolver(val constraintSolver: FlowConstraintSolver, traceLogger: TraceLogger) extends DeadConstructorElimResult:
  given tl: TraceLogger = traceLogger
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  
  val collector: FlowConstraintsCollector = constraintSolver.collector
  
  val deadCtors =
      
    def isRemovable(ctorSite: Result): Bool = ctorSite match
      case _: Tuple => true
      case CtorProducer(cls: ClassSymbol, args, selectedFrom) =>
        // TODO: should be able to remove this later when we can reason about
        // ctor flow and side effect properly
        def hasSimpleCtor(cls: ClsLikeDefn): Bool =
          val params = (cls.paramsOpt.toList ::: cls.auxParams).flatMap(_.allParams).map(_.sym).toSet[Symbol]
          @annotation.tailrec
          def onlyStoresParams(b: Block): Bool = b match
            case AssignField(Value.This(self), _, Value.SimpleRef(p), rest) if self is cls.isym =>
              onlyStoresParams(rest)
            case Define(ValDefn(_, _, Value.SimpleRef(p)), rest) =>
              onlyStoresParams(rest)
            case End(_) => true
            case _ => false
          onlyStoresParams(cls.preCtor) && onlyStoresParams(cls.ctor)
        end hasSimpleCtor
        cls.irClsLikeDefn.exists(hasSimpleCtor)
      case _ => false
    
    val allCtorStrats = collector.allRealCtors.filter(_.instantiationId.isDefined)
    
    val liveCtorConcreteIds = allCtorStrats.iterator
      .filter: c =>
        c.dests.exists:
          case NonAffine | Accumulator => false
          case UnknownCons => true
          case _: FieldSel | _: Dtor => true
      .map(_.concreteId)
      .toSet
    
    LinkedHashSet.from:
      allCtorStrats.iterator
        .filter(c => isRemovable(c.exprId.getResult))
        .map(_.concreteId)
        .filterNot(liveCtorConcreteIds)
  end deadCtors
  
  if tl.doTrace then
    tl.log(">>> dead-constructor-elim results >>>")
    for ctorStr <- deadCtors.toSeq.map(_.exprId.getResult.showDbg).sorted do
      tl.log(s"eliminable: $ctorStr")
    tl.log("<<< dead-constructor-elim results <<<")
  end if
end DeadConstructorElimSolver


object DeadConstructorElim:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    ctx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
  ): Program = cfg.flowBasedOpt.fold(p):
    FlowAnalysisBasedRewrite.rewriteWith(p, _, eta = false, dpe = false)
