package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*
import Message.MessageContext

import semantics.*
import flowAnalysis.*

import hkmc2.semantics.Elaborator.State

import scala.collection.mutable.{Set as MutSet, Map as MutMap}
import scala.collection.mutable.ListBuffer

type Web = FlowWebComputation.Result[Ctor, ConcreteCtorConsumer]

private object DataRepFlattenDebug:
  def showCtor(ctor: CtorCls): Str = ctor match
    case cls: ClassLikeSymbol => cls.nme
    case size: Int => s"tup(size $size)"

  def showField(field: SelField): Str = field match
    case sym: TermSymbol => sym.nme
    case index: Int => index.toString

  def showProducer(producer: Ctor): Str =
    s"${showCtor(producer.ctor)}@${producer.exprId}"

  def showFieldAccess(access: FieldSel): Str =
    s"${{showCtor(access.selectsFrom)}}.${showField(access.field)}@${access.exprId}"

  def showPatternMatch(patternMatch: Dtor): Str =
    s"match@${patternMatch.exprId}"

  def showConsumer(consumer: ConcreteCtorConsumer): Str = consumer match
    case access: FieldSel => showFieldAccess(access)
    case patternMatch: Dtor => showPatternMatch(patternMatch)

class ProducersCollector(val flowRes: FlowConstraintSolver)(using val tl: TL) extends BlockTraverser:
  private given fState: FlowAnalysis.State = flowRes.fState
  private given eState: State = flowRes.eState

  private val entryPoints = ListBuffer.empty[ProducersCollector.EntryPoints]
  private val concreteCtorsByResultId = MutMap.empty[ResultId, Ctor]
  for ctor <- flowRes.ctorsWithDests do
    concreteCtorsByResultId.addOne(ctor.exprId, ctor)
  private val concreteConsumersByResultId = MutMap.empty[ResultId, ListBuffer[ConcreteCtorConsumer]]
  for consumer <- flowRes.consumersWithSrcs do
    concreteConsumersByResultId.getOrElseUpdate(consumer.exprId, ListBuffer.empty) += consumer

  private class AllocationCollector extends BlockTraverserShallow:
    val allocations: ListBuffer[ResultId -> CtorCls] = ListBuffer.empty
    val resultIds: ListBuffer[ResultId] = ListBuffer.empty

    override def applyResult(r: Result): Unit =
      resultIds += r.uid
      r match
        case CtorProducer(ctor, _, _) => allocations += r.uid -> ctor
        case _ => ()
      super.applyResult(r)
  end AllocationCollector

  override def applyFunDefn(fun: FunDefn): Unit =
    val funName = fun.owner.fold(fun.dSym.nme)(owner => s"${owner.nme}.${fun.dSym.nme}")
    val collector = new AllocationCollector()
    collector.applyBlock(fun.body)

    val seenProducerEntryPoints = MutSet.empty[Ctor]
    for
      (allocationId, _) <- collector.allocations
      ctor <- concreteCtorsByResultId.get(allocationId)
      if !ctor.dests.contains(UnknownCons)
    do seenProducerEntryPoints.add(ctor)

    if !seenProducerEntryPoints.isEmpty then
      tl.log(s"track construction of ${seenProducerEntryPoints.map(DataRepFlattenDebug.showProducer).mkString(", ")} in $funName")

    val seenConsumerEntryPoints = MutSet.empty[ConcreteCtorConsumer]
    for
      resultId <- collector.resultIds
      consumer <- concreteConsumersByResultId.getOrElse(resultId, Nil)
      if !consumer.srcs.contains(UnknownProd)
      if consumer.srcs.exists:
        case _: Ctor => true
        case _ => false
    do seenConsumerEntryPoints.add(consumer)

    if !seenConsumerEntryPoints.isEmpty then
      tl.log(s"track consumption at ${seenConsumerEntryPoints.map(DataRepFlattenDebug.showConsumer).mkString(", ")} in $funName")

    entryPoints += ProducersCollector.EntryPoints(
      seenProducerEntryPoints.toList,
      Nil,
    )

  override def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
    defn.companion.foreach(applyCompanionModule)

  def result: (List[ProducersCollector.EntryPoints], Map[ResultId, Ctor]) =
    (entryPoints.toList, concreteCtorsByResultId.toMap)

object ProducersCollector:
  case class EntryPoints(
    producers: List[Ctor],
    consumers: List[ConcreteCtorConsumer],
  )

  def apply(p: Program, flowRes: FlowConstraintSolver)(using TL): (List[EntryPoints], Map[ResultId, Ctor]) =
    val collector = new ProducersCollector(flowRes)
    collector.applyProgram(p)
    collector.result


private sealed abstract class Shape:
  def show: Str

  def flattenShape: List[Shape]

private case class LitShape(lit: Value.Lit) extends Shape:
  def show: Str = lit match
    case Value.Lit(lit) => lit.idStr

  def flattenShape: List[Shape] = this :: Nil

private case class ClassShape(ctor: ClassLikeSymbol, fields: Map[TermSymbol, Shape]) extends Shape:
  def show: Str =
    if fields.isEmpty then DataRepFlattenDebug.showCtor(ctor)
    else
      val shownFields = fields.iterator
        .map((field, shape) => s"${DataRepFlattenDebug.showField(field)}: ${shape.show}")
      s"${DataRepFlattenDebug.showCtor(ctor)}${shownFields.mkString("(", ", ", ")")}"

  def flattenShape: List[Shape] =
    val alternatives = fields.iterator.foldLeft(List(Map.empty[TermSymbol, Shape])):
      case (alternatives, (field, fieldShape)) =>
        for
          alternative <- alternatives
          concreteFieldShape <- fieldShape.flattenShape
        yield alternative.updated(field, concreteFieldShape)
    alternatives.map(ClassShape(ctor, _)).distinct

private case class TupleShape(length: Int, elements: List[Shape]) extends Shape:
  require(elements.length === length)
  def show: Str =
    if elements.isEmpty then DataRepFlattenDebug.showCtor(length)
    else s"${DataRepFlattenDebug.showCtor(length)}${elements.map(_.show).mkString("(", ", ", ")")}"

  def flattenShape: List[Shape] =
    val alternatives = elements.foldLeft(List(List.empty[Shape])):
      case (alternatives, element) =>
        for
          alternative <- alternatives
          concreteElement <- element.flattenShape
        yield alternative :+ concreteElement
    alternatives.map(TupleShape(length, _)).distinct

private case class UnionShape(subshapes: List[Shape]) extends Shape:
  def show: Str = subshapes.map(_.show).mkString("(", " | ", ")")

  def flattenShape: List[Shape] =
    subshapes.flatMap(_.flattenShape).distinct

private object DynamicShape extends Shape:
  def show: Str = "_"

  def flattenShape: List[Shape] = this :: Nil

class DataRepFlattener(
  val webs: List[Web],
  val concreteCtorsByResultId: Map[ResultId, Ctor],
  val flowRes: FlowConstraintSolver,
  val debug: Bool,
)(using State, TL, Raise) extends BlockTransformer(SymbolSubst.Id):
  private given fState: FlowAnalysis.State = flowRes.fState

  private val producersInWeb = webs.iterator.flatMap(_.markedProducers).toSet

  private val shapeTags = MutMap.empty[Shape, Int]

  private val tagField = new syntax.Tree.Ident("__tag")

  private def allocateShapeTags() =
    val shapes = producersInWeb.iterator.map: producer =>
      producer.exprId.uid -> shapeOfProducer(producer)
    for (_, shape) <- shapes.toList.sortBy((id, shape) => id -> shape.show) do
      shape match
        case shape: ClassShape if !containsUnion(shape) =>
          val tag = shapeTags.getOrElseUpdate(shape, shapeTags.size)
          if debug then
            summon[TL].emitDbg(
              s"data-rep-flatten transform-phase > allocated tag $tag for ${shape.show}")
        case _ => ()

  private def getCtorArgs(producer: Ctor) =
    producer.exprId.getResult match
      case CtorProducer(_, args, _) =>
        softAssert(
          args.size === producer.args.size,
          s"Mismatched constructor arguments for ${DataRepFlattenDebug.showProducer(producer)}",
        )
        args
      case result =>
        softAssert(
          false,
          s"Missing constructor result for ${DataRepFlattenDebug.showProducer(producer)}: ${result.showDbg}",
        )
        Nil

  private def shapeOfProducer(producer: Ctor): Shape =
    val args = getCtorArgs(producer)
    val fieldsOrElements = producer.args.zipWithIndex.map:
      case ((field, value), index) =>
        val original = args.lift(index).map(_.value)
        field -> shapeOf(value, original)
    producer.ctor match
      case cls: ClassLikeSymbol =>
        val fields = fieldsOrElements.collect:
          case (field: TermSymbol, shape) => field -> shape
        softAssert(
          fields.size === fieldsOrElements.size,
          s"Unexpected class fields in ${DataRepFlattenDebug.showProducer(producer)}",
        )
        ClassShape(cls, fields.toMap)
      case length: Int =>
        softAssert(
          fieldsOrElements.size === length,
          s"Mismatched tuple arity for ${DataRepFlattenDebug.showProducer(producer)}",
        )
        TupleShape(length, fieldsOrElements.map(_._2))

  private def shapeOf(producer: ProdStrat, original: Opt[Path]): Shape =
    original match
      case S(lit: Value.Lit) => LitShape(lit)
      case _ => producer match
        case ctor: Ctor => shapeOfProducer(ctor)
        case variable: StratVar =>
          DataRepFlattener.mkUnion:
            variable.lowerBounds.map: lowerBound =>
              shapeOf(lowerBound, N)
        case _ => DynamicShape

  private def containsUnion(shape: Shape): Bool = shape match
    case ClassShape(_, fields) => fields.valuesIterator.exists(containsUnion)
    case TupleShape(_, elements) => elements.exists(containsUnion)
    case _: UnionShape => true
    case _ => false

  private def allocateShape(fun: FunDefn, producer: Ctor) =
    val shape = shapeOfProducer(producer)
    shape match
      case shape: ClassShape if !containsUnion(shape) =>
        val tag = shapeTags.get(shape)
        softAssert(tag.isDefined, s"Missing tag for shape ${shape.show}")
        tag
      case _ => N

  private def insertTag(result: Result, tag: Int)(k: Path => Block): Block =
    val instance = new TempSymbol(N, "tmp")
    val instanceRef = instance.asSimpleRef.withLocOf(result)
    Scoped(Set.single(instance), Assign(
      instance, result, AssignField(
        instanceRef, tagField, Value.Lit(syntax.Tree.IntLit(tag)), k(instanceRef),
      )(N)))

  override def applyProgram(program: Program): Program =
    if debug then
      summon[TL].emitDbg(">>> start data-rep-flatten transform-phase")
    allocateShapeTags()
    val result = super.applyProgram(program)
    if debug then
      summon[TL].emitDbg("<<< end data-rep-flatten transform-phase")
    result

  override def applyFunDefn(fun: FunDefn): FunDefn =
    val transformer = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyResult(result: Result)(k: Result => Block): Block =
        result match
          case CtorProducer(_, _, _) =>
            concreteCtorsByResultId.get(result.uid).filter(producersInWeb) match
              case S(ctor) =>
                super.applyResult(result): transformed =>
                  allocateShape(fun, ctor) match
                    case S(tag) => insertTag(transformed, tag)(k)
                    case N => k(transformed)
              case N => super.applyResult(result)(k)
          case _ => super.applyResult(result)(k)
    val body = transformer.applyFunBodyLikeBlock(fun.body)
    val transformed =
      if body is fun.body then fun
      else FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, body)(fun.configOverride, fun.annotations)
    super.applyFunDefn(transformed)
end DataRepFlattener


object DataRepFlattener:
  private def mkUnion(shapes: Iterable[Shape]): Shape =
    val flattened = shapes.iterator.flatMap:
      case UnionShape(subshapes) if subshapes.nonEmpty => subshapes
      case shape => shape :: Nil
    val normalized = flattened.toList.distinct.sortBy(_.show)
    normalized match
      case Nil => DynamicShape
      case shape :: Nil => shape
      case shapes => UnionShape(shapes)

  private def mkShapeByPattern(pattern: Pattern)(using raise: Raise): Shape =
    pattern match
      case ctorPattern @ Pattern.Constructor(_, arguments) =>
        ctorPattern.symbol.flatMap(_.asClsLike) match
          case S(cls: ClassSymbol) =>
            cls.tree.clsParams match
              case fields :: Nil =>
                val argumentShapes = arguments match
                  case S(patterns) => patterns.map(mkShapeByPattern)
                  case N => Nil
                softAssert(
                  argumentShapes.size === fields.size,
                  s"Mismatched arity for class pattern $pattern.",
                )
                ClassShape(cls, fields.zip(argumentShapes).toMap)
              case _ =>
                raise(ErrorReport(
                  msg"This pattern is not supported by @matchShapes yet." -> pattern.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation,
                ))
                DynamicShape
          case S(obj: ModuleOrObjectSymbol) =>
            ClassShape(obj, Map.empty)
          case _ => DynamicShape
      case Pattern.Tuple(leading, N) =>
        TupleShape(leading.size, leading.map(mkShapeByPattern))
      case Pattern.Literal(literal) => LitShape(Value.Lit(literal))
      case Pattern.Wildcard() => DynamicShape
      case _ =>
        raise(ErrorReport(
          msg"This pattern is not supported by @matchShapes yet." -> pattern.toLoc :: Nil,
          source = Diagnostic.Source.Compilation,
        ))
        DynamicShape

  private def mkWeb(entries: ProducersCollector.EntryPoints): Web =
    FlowWebComputation[Ctor, ConcreteCtorConsumer](
      producer => producer.dests.collect:
        case consumer: ConcreteCtorConsumer => consumer,
      consumer => consumer.srcs.collect:
        case producer: Ctor => producer,
      entries.producers,
      entries.consumers,
    )

  private def mkWebs(entryPoints: List[ProducersCollector.EntryPoints]) =
    val coveredProducers = MutSet.empty[Ctor]
    val coveredConsumers = MutSet.empty[ConcreteCtorConsumer]
    val webs = ListBuffer.empty[Web]
    for entries <- entryPoints do
      if
        (entries.producers.nonEmpty || entries.consumers.nonEmpty)
          && !entries.producers.exists(coveredProducers)
          && !entries.consumers.exists(coveredConsumers)
      then
        val web = mkWeb(entries)
        coveredProducers ++= web.markedProducers
        coveredConsumers ++= web.markedConsumers
        webs += web
    webs.toList

  private def logWebs(webs: List[Web])(using tl: TL): Unit =
    if webs.nonEmpty then
      tl.emitDbg(">>> start data-rep-flatten web-computation-phase")
      for (web, index) <- webs.zipWithIndex do
        val producers = web.markedProducers.toList.sortBy(_.exprId.uid)
        val fieldAccesses = web.markedConsumers.collect:
          case access: FieldSel => access
        val patternMatches = web.markedConsumers.collect:
          case patternMatch: Dtor => patternMatch
        tl.emitDbg(s"data-rep-flatten web-computation-phase > web $index:")
        tl.emitDbg(s"data-rep-flatten web-computation-phase >   producers: ${producers.map(DataRepFlattenDebug.showProducer).mkString(", ")}")
        if fieldAccesses.nonEmpty then
          tl.emitDbg(s"data-rep-flatten web-computation-phase >   field accesses: ${fieldAccesses.toList.sortBy(_.exprId.uid).map(DataRepFlattenDebug.showFieldAccess).mkString(", ")}")
        if patternMatches.nonEmpty then
          tl.emitDbg(s"data-rep-flatten web-computation-phase >   pattern matches: ${patternMatches.toList.sortBy(_.exprId.uid).map(DataRepFlattenDebug.showPatternMatch).mkString(", ")}")
      tl.emitDbg("<<< end data-rep-flatten web-computation-phase")

  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: State,
    ctx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
  ): Program =
    cfg.dataRepFlatten match
      case N => p
      case S(dCfg) =>
        val flowCfg = Config.FlowAnalysisConfig(
          debug = false,
          mono = dCfg.mono,
          trackNonAffine = false,
          trackAccumulator = false,
          logNonAffine = false,
          logAccumulator = false,
        )
        val flowAnalysisRes =
          FlowAnalysis.mkTraceLogger(flowCfg, "data-rep-flatten flow-analysis-phase > ", tl).givenIn:
            FlowAnalysis(
              p,
              mono = flowCfg.mono,
              nonAffineTracking = false,
              accumulatorTracking = false,
            )
        val collectorTl = new TraceLogger(using tl.debugPrinter):
          override def doTrace: Bool = dCfg.debug
          override def emitDbg(str: Str): Unit =
            tl.emitDbg(s"data-rep-flatten collection-phase > $str")
        val (entryPoints, concreteCtorsByResultId) = collectorTl.givenIn:
          if dCfg.debug then tl.emitDbg(">>> start data-rep-flatten collection-phase")
          val result = ProducersCollector(p, flowAnalysisRes)
          if dCfg.debug then tl.emitDbg("<<< end data-rep-flatten collection-phase")
          result
        val webs = mkWebs(entryPoints)
        if dCfg.debug then logWebs(webs)
        new DataRepFlattener(webs, concreteCtorsByResultId, flowAnalysisRes, dCfg.debug).applyProgram(p)
