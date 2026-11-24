package hkmc2
package codegen
package deforest

import utils.*
import hkmc2.utils.*, shorthands.*
import semantics.*
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, LinkedHashSet, Buffer}
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

  // Fusion replaces a constructor with a closure or with the value of one of its fields, so each slot that
  // such a value reaches takes the types of what now flows into it. The maps below hold these types for the
  // final set of fused constructors. A slot that no fused value reaches keeps its declared type and has no
  // entry in the first two maps.

  /** The types of the variables, parameters and stored values that fused values reach, in each instance. */
  val retypedVariables = LinkedHashMap.empty[(InstantiationId, ValueSymbol), ErasedValueType]
  /** The types of the function results that fused values reach, in each instance of the function. */
  val retypedResults = LinkedHashMap.empty[(InstantiationId, TermSymbol), ErasedValueType]
  /** The types of the values that each fused constructor receives, in the order of its arguments. */
  val fusedFieldTypes = MutMap.empty[CtorDtorId, Ls[Opt[ErasedValueType]]]
  /** The types of the values that a fused match receives from all the constructors of one class, in the
    * order of their arguments. The key pairs the match with the class. */
  val branchParamTypes = MutMap.empty[(CtorDtorId, CtorCls), Ls[Opt[ErasedValueType]]]

  def hasWorkToDo: Bool = finalCtorDests.nonEmpty || finalDtorSrcs.nonEmpty

  def polyInstIds: Iterator[InstantiationId] = finalCtorDests.iterator.flatMap:
    case (ctor, FinalDestSel(dtors, _)) =>
      (dtors + ctor).toList.sortBy(_.exprId.uid).map(_.instId)
    case (ctor, FinalDestMatch(dtor, _)) =>
      ctor.instId :: dtor.instId :: Nil

  /** Whether fusion replaces the values that `p` produces. */
  def isFused(p: ProdStrat): Bool = p match
    case c: Ctor => finalCtorDests.contains(c.concreteId)
    case _: ProdFun | UnknownProd => false
    case UnsafeEta => lastWords("effect producer in value flow")
    case _: StratVar => lastWords("unexpected strat var")

  private def producersOf(values: ProdStrat): Ls[ProdStrat] = values match
    case v: StratVar => v.lowerBounds.toList
    case p => p :: Nil

  // The type of the values that `p` produces once the fused constructors are replaced, or `N` for unknown
  // values, which have the declared type of the slot they reach. `seen` holds the constructors whose
  // projected field is being typed: one that reaches its own field takes the field's declared type there.
  private def producedType(p: ProdStrat, seen: Set[Ctor]): Opt[ErasedValueType] = p match
    case c: Ctor => finalCtorDests.get(c.concreteId) match
      case S(_: FinalDestMatch) => S(ErasedType.Function(S(false)))
      case S(FinalDestSel(_, field)) =>
        val fieldType =
          if seen(c) then field.erasedFieldType
          else slotTypeFromFlow(producersOf(c.args.find(_._1 == field).get._2), field.erasedFieldType, seen + c)
        S(fieldType.getOrElse(ErasedType.Unknown))
      case N => S(c.allocatedType)
    case _: ProdFun => S(ErasedType.Function(S(false)))
    case UnknownProd => N
    case UnsafeEta => lastWords("effect producer in value flow")
    case _: StratVar => lastWords("unexpected strat var")

  // compute the updated erased type of a local variable, a function param or a function return,
  // using all the concrete producers that flows into that slot
  private def slotTypeFromFlow(producers: Ls[ProdStrat], declared: Opt[ErasedValueType], seen: Set[Ctor]): Opt[ErasedValueType] =
    val types = producers.map(producedType(_, seen))
    if types.forall(_.isEmpty) then declared
    else S(ErasedType.Union.mk(types.map(_.orElse(declared).getOrElse(ErasedType.Unknown))))

  // N when the existing slot keeps its declaration, as no fused value reaches it
  private def retypedSlotType(producers: Iterable[ProdStrat], declared: Opt[ErasedValueType]): Opt[ErasedValueType] =
    if producers.exists(isFused) then slotTypeFromFlow(producers.toList, declared, Set.empty) else N

  /** The producers of the values that one instance of `fun` returns, where `v` is the variable of the
    * definition symbol in that instance. A definition without parameter lists returns into `v` itself.
    * Any other definition binds `v` to the closure of its first parameter list, whose last parameter list
    * holds the result of the body. `N` when the analysis does not model the definition, as for class
    * methods, whose variables are opaque.
    */
  private def returnedProducers(fun: FunDefn, v: StratVar): Opt[Ls[ProdStrat]] =
    def isParamList(pf: ProdFun, idx: Int): Bool = pf.exprId match
      case (sym: TermSymbol, `idx`) => sym is fun.dSym
      case _ => false
    def lastParamList(pf: ProdFun, idx: Int): ProdFun =
      if idx == fun.params.size - 1 then pf else pf.res match
        case next: ProdFun if isParamList(next, idx + 1) => lastParamList(next, idx + 1)
        case res => lastWords(s"parameter list ${idx + 1} of ${fun.dSym.nme} has no closure in $res")
    if fun.params.isEmpty then S(v.lowerBounds.toList)
    else v.lowerBounds.iterator.collectFirst:
      case pf: ProdFun if isParamList(pf, 0) => producersOf(lastParamList(pf, 0).res)

  // Whether fusion replaces `c` with a value that is not a reference: the value of an unboxed field.
  private def projectsUnboxedValue(c: Ctor): Bool = finalCtorDests.get(c.concreteId) match
    case S(_: FinalDestSel) => producedType(c, Set.empty).exists: tpe =>
      tpe.canonicalize match
        case _: ErasedType.Primitive | _: ErasedType.Incompatible => true
        case _ => false
    case _ => false

  /** Types the slots that fused values reach, for the current set of fused constructors, and returns the
    * fused constructors that leave one of these slots without a representation.
    *
    * Projecting a field replaces an object with the value of that field, which is unboxed when the field is.
    * An unboxed value shares no representation with a reference or with an unboxed value of another type,
    * so it can only reach slots that hold nothing else. When such a slot also receives another value, like
    * an object that stays allocated or a value of unknown origin, the projected constructor is returned:
    * it has to stay an object, which every reference slot can hold.
    */
  private def typeSlots(): collection.Set[Ctor] =
    retypedVariables.clear()
    retypedResults.clear()
    fusedFieldTypes.clear()
    branchParamTypes.clear()
    val unrepresentable = LinkedHashSet.empty[Ctor]
    def check(tpe: Opt[ErasedValueType], producers: => IterableOnce[ProdStrat]): Unit =
      if tpe.exists(_.canonicalize.isInstanceOf[ErasedType.Incompatible]) then
        unrepresentable ++= producers.iterator.collect:
          case c: Ctor if projectsUnboxedValue(c) => c
    val definitions = preAnalyzer.res.funSymToFunDefn
    for (sym, instId, v) <- constraintSolver.collector.symbolFlows do sym match
      // The variable of a function definition holds what a reference to it evaluates to: its closure, or
      // the result of a definition without parameter lists. That result belongs to the function's signature.
      case fun: TermSymbol if definitions.contains(fun) =>
        val definition = definitions(fun)
        for returned <- returnedProducers(definition, v) do
          val tpe = retypedSlotType(returned, definition.signature.result.bodyType)
          tpe.foreach(tpe => retypedResults(instId -> fun) = tpe)
          check(tpe, returned)
      case sym: (VarSymbol | TempSymbol | TermSymbol) =>
        val declared = sym match
          case sym: LocalVarSymbol => sym.erasedType
          case sym: TermSymbol => sym.erasedType
        val tpe = retypedSlotType(v.lowerBounds, declared)
        tpe.foreach(tpe => retypedVariables(instId -> sym) = tpe)
        check(tpe, v.lowerBounds)
      case _ => ()
    for (id, ctor) <- fusingCtorInfo do
      fusedFieldTypes(id) = ctor.args.map: (field, prod) =>
        val producers = producersOf(prod)
        val tpe = slotTypeFromFlow(producers, field.erasedFieldType, Set.empty)
        check(tpe, producers)
        tpe
    val branches = LinkedHashMap.empty[(CtorDtorId, CtorCls), Buffer[Ctor]]
    for case (id, FinalDestMatch(dtor, _)) <- finalCtorDests do
      val ctor = fusingCtorInfo(id)
      branches.getOrElseUpdate(dtor -> ctor.ctor, Buffer.empty) += ctor
    for (branch, ctors) <- branches do
      branchParamTypes(branch) = ctors.head.args.indices.iterator.map: index =>
        val types = ctors.map(ctor => fusedFieldTypes(ctor.concreteId)(index))
        val tpe = if types.forall(_.isEmpty) then N
          else S(ErasedType.Union.mk(types.map(_.getOrElse(ErasedType.Unknown))))
        check(tpe, ctors.iterator.flatMap(ctor => producersOf(ctor.args(index)._2)))
        tpe
      .toList
    unrepresentable

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

    def unconsumed = constraintSolver.collector.allRealCtors.iterator.filter: ctor =>
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

    // fuses every constructor that the flow lets fusion replace, except those of `kept`
    def fuse(kept: collection.Set[Ctor]): Unit =
      finalCtorDests.clear()
      finalDtorSrcs.clear()
      fusingCtorInfo.clear()
      fusingDtorInfo.clear()
      val result = FlowWebComputation[Ctor, ConcreteCtorConsumer](
        p => p.dests.collect:
          case c: ConcreteCtorConsumer => c,
        c => c.srcs.collect:
          case p: Ctor => p,
        storedCtorsKeptUnfused,
        prodRoots.iterator ++ unconsumed ++ kept,
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

    // Whether a fused constructor leaves a slot without a representation only shows once the slots are
    // typed for a whole set of fused constructors (see `typeSlots`). Keeping such a constructor can also
    // keep others, as the constructors that reach a common consumer fuse together, and the slots these
    // reach change types in turn. So fuse and type again until every slot has a representation.
    // Each round keeps at least one more constructor, which bounds their number.
    val kept = MutSet.empty[Ctor]
    fuse(kept)
    var unrepresentable: collection.Set[Ctor] = if finalCtorDests.isEmpty then Set.empty else typeSlots()
    while unrepresentable.nonEmpty do
      assert(unrepresentable.forall(isFused), "only a fused constructor can change the type of a slot")
      kept ++= unrepresentable
      fuse(kept)
      unrepresentable = typeSlots()
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

