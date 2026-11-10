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

extension (f: SelField) def erasedFieldType(using Raise): Opt[ErasedValueType] = f match
  case tSym: TermSymbol => tSym.erasedType
  case _: Int => N

class DeforestFusionSolver(val constraintSolver: FlowConstraintSolver)(using Config, Elaborator.Ctx)
  extends FlowAnalysisSolverResult:
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
  
  /** Determines whether a constructor's result satisfies a match case without creating the value.
    * Returns `N` when its class or tuple length does not determine the answer.
    */
  private def matches(ctor: CtorCls, cse: Case): Opt[Bool] = (ctor, cse) match
    case (cls: TypeSymbol, Case.Cls(expected: TypeSymbol, _)) => ErasedType.isSubtypeOf(cls, expected)
    case (_: Int, Case.Cls(expected: TypeSymbol, _)) => ErasedType.isSubtypeOf(summon[Elaborator.Ctx].builtins.Array, expected)
    case (length: Int, Case.Tup(expected, inf)) => S(if inf then length >= expected else length == expected)
    // Objects and tuples cannot satisfy a primitive literal case.
    case (_, Case.Lit(_)) => S(false)
    case _ => N

  /** Finds the body selected by match `dtor` for a value constructed by `ctor`.
    * This lets fusion replace the match with the selected body.
    * Returns `N` if the choice is unknown, or an empty block if the match falls through.
    */
  def selectedBranch(ctor: CtorCls, dtor: CtorDtorId): Opt[Block] =
    val matched = preAnalyzer.res.matchScrutToMatchBlock(dtor.exprId)
    def loop(arms: Ls[Case -> Block]): Opt[Block] = arms match
      case (cse, body) :: rest => matches(ctor, cse) match
        case S(true) => S(body)
        case S(false) => loop(rest)
        // An earlier case may still win even when a later case is known to match.
        case N => N
      case Nil => S(matched.dflt.getOrElse(End()))
    loop(matched.arms)

  val finalCtorDests = LinkedHashMap.empty[CtorDtorId, FinalDest]
  val finalDtorSrcs = LinkedHashMap.empty[CtorDtorId, Set[CtorDtorId]]
  val fusingCtorInfo = MutMap.empty[CtorDtorId, Ctor]
  val fusingDtorInfo = MutMap.empty[CtorDtorId, ConcreteCtorConsumer]

  def hasWorkToDo: Bool = finalCtorDests.nonEmpty || finalDtorSrcs.nonEmpty

  def polyInstIds: Iterator[InstantiationId] = finalCtorDests.iterator.flatMap:
    case (ctor, FinalDestSel(dtors, _)) =>
      (dtors + ctor).toList.sortBy(_.exprId.uid).map(_.instId)
    case (ctor, FinalDestMatch(dtor, _)) =>
      ctor.instId :: dtor.instId :: Nil

  locally {
    // TODO: improve this code – inefficient (useless intermediate sets) and nondeterministic (set `head` access)
    def mergeDests(ctor: Ctor, dests: Set[ConcreteCtorConsumer | MarkerConsStrat]): Opt[FinalDest] =
      def selsSelectingTheSameSymbol(sels: Set[FieldSel]) =
        sels.map(s => s.field).size == 1
      val canSkipConstruction = ctor.exprId.getResult match
        // Fusion omits the constructor body and qualifier, so neither may have effects.
        // Matching argument counts prevents the rewrite from dropping argument evaluations.
        case CtorProducer(_, args, selectedFrom) => args.length == ctor.args.length &&
          selectedFrom.forall(_.isPure) && ConstructorElision.isHarmless(ctor.ctor)
        case _ => false
      if !canSkipConstruction || dests.exists(_.isInstanceOf[MarkerConsStrat]) then
        N
      else
        val (dtors, sels) = dests.partitionMap:
          case d: Dtor => Left(d)
          case fs: FieldSel => Right(fs)
          case _ => die
        if sels.nonEmpty && !ConstructorElision.preservesParameterFields(ctor) then N
        else if dtors.size == 0 && selsSelectingTheSameSymbol(sels) then
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
          ) && selectedBranch(ctor.ctor, dtor.concreteId).isDefined then
            S(FinalDestMatch(
              dtor.concreteId,
              sels.map(_.concreteId)
            ))
          else N
    end mergeDests

    val prodRoots =
      for
        ctor <- constraintSolver.ctorsWithDests
        if mergeDests(ctor, ctor.dests.toSet).isEmpty
      yield ctor
    val consRoots =
      for
        dtor <- constraintSolver.consumersWithSrcs
        if dtor.srcs.contains(UnknownProd)
      yield dtor

    val unconsumed = constraintSolver.collector.allRealCtors.iterator.filter: ctor =>
      ctor.instantiationId.isDefined && ctor.dests.isEmpty

    // constructors stored in `c`'s field that must stay unfused when `c` is unfused,
    // as `c`'s fields keep their declared types
    def storedCtorsKeptUnfused(c: Ctor): Iterator[Ctor] =
      for
        (field, arg) <- c.args.iterator
        stored <- arg match
          case stored: Ctor => Iterator.single(stored)
          case v: StratVar => v.lowerBounds.iterator.collect:
            case stored: Ctor => stored
          case _ => Iterator.empty
        // Only match fusion replaces a producer with a closure. Unmergeable producers
        // are already roots; field-projection fusion stays conservative at storage boundaries.
        if !stored.dests.exists(_.isInstanceOf[Dtor]) || field.erasedFieldType.exists: tpe =>
          !ErasedType.needsCast(
            ErasedType.Function(S(false)).canonicalize,
            tpe.canonicalize).contains(false)
      yield stored

    val result = FlowWebComputation[Ctor, ConcreteCtorConsumer](
      p => p.dests.collect:
        case c: ConcreteCtorConsumer => c,
      c => c.srcs.collect:
        case p: Ctor => p,
      storedCtorsKeptUnfused,
      prodRoots.iterator ++ unconsumed,
      consRoots,
    )
    val toRemoveCtor = result.markedProducers
    val toRemoveDtor = result.markedConsumers

    for
      ctor <- constraintSolver.ctorsWithDests
      if !toRemoveCtor(ctor)
    do
      finalCtorDests(ctor.concreteId) = mergeDests(ctor, ctor.dests.toSet).get
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
    tl.log(dbg"${pp(c)} ->")
    dest match
    case FinalDestMatch(dtor, sels) =>
      tl.log(dbg"\tmatch: ${pp(dtor)}")
      for s <- sels.toSeq.sortBy(_.exprId.uid) do tl.log(dbg"\tfields: ${pp(s)}")
    case FinalDestSel(dtors, field) =>
      tl.log(dbg"\tselect: ${pp(field)}")
  tl.log("<<< fusing <<<")
end DeforestFusionSolver


object Deforest:
  def apply(p: Program, additionalTopLevelSymbols: Set[LocalVarSymbol])(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eCtx: Elaborator.Ctx,
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
      logEffects = dCfg.config.logEffects,
    )
    val solver = new DeforestFusionSolver(flowAnalysisRes)
    if !solver.hasWorkToDo then p
    else
      val rewrite = new DeforestRewriter(solver, additionalTopLevelSymbols)
      rewrite()

