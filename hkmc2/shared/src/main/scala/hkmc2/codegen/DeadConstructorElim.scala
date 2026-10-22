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


/** Prove that skipping construction omits only initialization of the discarded instance and
  * its local slots. This reads the current IR definition, including superclass construction;
  * missing definitions, cycles, calls, checks, and control flow are not assumed harmless.
  * Callers separately preserve argument evaluation and any qualified constructor lookup.
  */
private[codegen] object ConstructorElision:
  def isHarmless(ctor: CtorCls)(using Elaborator.State): Bool = ctor match
    case _: Int => true
    // A singleton producer refers to an already initialized object/module.
    case _: ModuleOrObjectSymbol => true
    case cls: ClassSymbol => cls.irClsLikeDefn.exists(harmlessClass(_, Set.empty))

  /** Field projection additionally relies on the flow analysis's positional mapping from source
    * fields to constructor arguments. Validate that mapping against the current IR parameter list
    * and stores; harmless updates to an instance can still change the value of a projected field.
    */
  def preservesParameterFields(ctor: Ctor)(using Elaborator.State): Bool = ctor.ctor match
    case cls: ClassSymbol => cls.irClsLikeDefn.exists: definition =>
      val params = (definition.paramsOpt.toList ::: definition.auxParams).flatMap(_.allParams).map(_.sym)
      val expected = ctor.args.zip(params).collect { case ((field: TermSymbol, _), param) => field -> param }.toMap
      if params.length != ctor.args.length || expected.size != ctor.args.length then false
      else
        def isParameter(value: Result, param: VarSymbol): Bool = value match
          case Value.SimpleRef(sym) => sym is param
          case Cast(value, _, false) => isParameter(value, param)
          case _ => false
        def stores(block: Block, inBody: Bool): Opt[Set[TermSymbol]] = block match
          case assign @ AssignField(Value.This(self), _, value, rest) if inBody && (self is definition.isym) =>
            for
              field <- assign.symbol.flatMap(_.asTrm)
              param <- expected.get(field)
              if isParameter(value, param)
              restFields <- stores(rest, inBody)
            yield restFields + field
          case Define(value: ValDefn, rest) if inBody =>
            for
              param <- expected.get(value.tsym)
              if isParameter(value.rhs, param)
              restFields <- stores(rest, inBody)
            yield restFields + value.tsym
          case Assign(sym: VarSymbol, _, _) if params.contains(sym) => N
          case Assign(NoSymbol, Call(Value.SimpleRef(parentCall), _), rest)
              if parentCall is Elaborator.State.superSymbol =>
            if inBody then N else stores(rest, inBody)
          case Assign(_, _: Path, rest) => stores(rest, inBody)
          case Scoped(_, body) => stores(body, inBody)
          case Begin(first, rest) =>
            for
              firstFields <- stores(first, inBody)
              restFields <- stores(rest, inBody)
            yield firstFields ++ restFields
          case End(_) => S(Set.empty)
          case _ => N
        stores(definition.preCtor, false).isDefined && stores(definition.ctor, true).exists(expected.keySet.subsetOf)
    case _ => true

  private def harmlessClass(cls: ClsLikeDefn, visiting: Set[Symbol])(using Elaborator.State): Bool =
    if visiting(cls.isym) then false
    else
      val next = visiting + cls.isym
      val params = (cls.paramsOpt.toList ::: cls.auxParams).flatMap(_.allParams).map(_.sym).toSet[Symbol]
      def harmlessBlock(block: Block, locals: Set[Symbol]): Bool = block match
        case AssignField(Value.This(self), _, value: Path, rest) if (self is cls.isym) && value.isPure =>
          harmlessBlock(rest, locals)
        case Define(value: ValDefn, rest) if value.owner.contains(cls.isym) && value.rhs.isPure =>
          harmlessBlock(rest, locals)
        case Assign(local, value: Path, rest) if value.isPure && (local match
            case sym: LocalVarSymbol => locals(sym)
            case NoSymbol => true) =>
          harmlessBlock(rest, locals)
        case Assign(NoSymbol, Call(Value.SimpleRef(parentCall), argss), rest)
            if (parentCall is Elaborator.State.superSymbol) && argss.forall(_.forall(arg => arg.spread.isEmpty && arg.value.isPure)) =>
          cls.parentPath.flatMap(_.targetSymbol).collect { case parent: ClassSymbol => parent }
            .flatMap(_.irClsLikeDefn).exists(harmlessClass(_, next)) && harmlessBlock(rest, locals)
        case Scoped(symbols, body) => harmlessBlock(body, locals ++ symbols)
        case Begin(first, rest) => harmlessBlock(first, locals) && harmlessBlock(rest, locals)
        case End(_) => true
        case _ => false
      harmlessBlock(cls.preCtor, params) && harmlessBlock(cls.ctor, params)
  end harmlessClass


class DeadConstructorElimSolver(val constraintSolver: FlowConstraintSolver, traceLogger: TraceLogger) extends DeadConstructorElimResult:
  given tl: TraceLogger = traceLogger
  given fState: FlowAnalysis.State = constraintSolver.fState
  given eState: Elaborator.State = constraintSolver.eState
  
  val collector: FlowConstraintsCollector = constraintSolver.collector
  
  val deadCtors =
      
    def isRemovable(ctorSite: Result): Bool = ctorSite match
      case _: Tuple => true
      case CtorProducer(cls: ClassSymbol, _, _) => ConstructorElision.isHarmless(cls)
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
  
  if tl.isTracing then
    tl.log(">>> dead-constructor-elim results >>>")
    for ctorStr <- deadCtors.toSeq.map(_.exprId.getResult.showDbg).sorted do
      tl.log(dbg"eliminable: $ctorStr")
    tl.log("<<< dead-constructor-elim results <<<")
  end if
end DeadConstructorElimSolver


object DeadConstructorElim:
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: Elaborator.State,
    eCtx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
  ): Program = cfg.flowBasedOpt.fold(p):
    FlowAnalysisBasedRewrite.rewriteWith(p, _, eta = false, dpe = false)
