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

private object ClassTagsDebug:
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

// * Collect all producers & consumers in the given function to build the web
class WebEntryCollector(val flowRes: FlowConstraintSolver)(using val tl: TL) extends BlockTraverser:
  private given fState: FlowAnalysis.State = flowRes.fState
  private given eState: State = flowRes.eState

  private val entryPoints = ListBuffer.empty[WebEntryCollector.EntryPoints]
  private val concreteCtorsByResultId = MutMap.empty[ResultId, Ctor]
  for ctor <- flowRes.ctorsWithDests do
    concreteCtorsByResultId.addOne(ctor.exprId, ctor)
  private val concreteConsumersByResultId = MutMap.empty[ResultId, ListBuffer[ConcreteCtorConsumer]]
  for consumer <- flowRes.consumersWithSrcs do
    concreteConsumersByResultId.getOrElseUpdate(consumer.exprId, ListBuffer.empty) += consumer

  private class ResultCollector extends BlockTraverserShallow:
    val resultIds: ListBuffer[ResultId] = ListBuffer.empty

    override def applyResult(r: Result): Unit =
      resultIds += r.uid
      super.applyResult(r)
  end ResultCollector

  override def applyFunDefn(fun: FunDefn): Unit =
    val funName = fun.owner.fold(fun.dSym.nme)(owner => s"${owner.nme}.${fun.dSym.nme}")
    val collector = new ResultCollector()
    collector.applyBlock(fun.body)

    val seenProducerEntryPoints = MutSet.empty[Ctor]
    for
      resultId <- collector.resultIds
      ctor <- concreteCtorsByResultId.get(resultId)
      if !ctor.dests.contains(UnknownCons) // does not leak out of the web
    do seenProducerEntryPoints.add(ctor)

    if !seenProducerEntryPoints.isEmpty then
      tl.log(s"track construction of ${seenProducerEntryPoints.map(ClassTagsDebug.showProducer).mkString(", ")} in $funName")

    val seenConsumerEntryPoints = MutSet.empty[ConcreteCtorConsumer]
    for
      resultId <- collector.resultIds
      consumer <- concreteConsumersByResultId.getOrElse(resultId, Nil)
      if !consumer.srcs.contains(UnknownProd) // not allocated out of the web
      if consumer.srcs.exists:
        case _: Ctor => true
        case _ => false
    do seenConsumerEntryPoints.add(consumer)

    if !seenConsumerEntryPoints.isEmpty then
      tl.log(s"track consumption at ${seenConsumerEntryPoints.map(ClassTagsDebug.showConsumer).mkString(", ")} in $funName")

    entryPoints += WebEntryCollector.EntryPoints(
      seenProducerEntryPoints.toList,
      seenConsumerEntryPoints.toList,
    )

  def result: List[WebEntryCollector.EntryPoints] = entryPoints.toList

object WebEntryCollector:
  case class EntryPoints(producers: List[Ctor], consumers: List[ConcreteCtorConsumer])

  def apply(p: Program, flowRes: FlowConstraintSolver)(using TL): List[EntryPoints] =
    val collector = new WebEntryCollector(flowRes)
    collector.applyProgram(p)
    collector.result


private sealed abstract class Shape:
  def show: Str

  def flattenShape: List[Shape]

  def containsUnion: Bool

  // * This shape subsumption is only used for wildcards (dynamic shapes) checking.
  // * i.e., if the pattern is a wildcard, it can accept any scrutinee
  // * We do not support a union shape for pattern
  // * and we flattern unions in Ctor to insert different tags
  // * We also track precise information so we do not need to check if a class is a subclass of another.
  // * i.e., if a variable has shape C, then it is impossible that the variable is instantiated to a subclass D in runtime.
  final infix def <=(that: Shape): Bool = (this, that) match
    case (_, DynamicShape) => true
    case (LitShape(left), LitShape(right)) => left === right
    case (ClassShape(leftCtor, leftFields), ClassShape(rightCtor, rightFields)) =>
      leftCtor === rightCtor
        && leftFields.keySet === rightFields.keySet
        && leftFields.forall: (field, shape) =>
          shape <= rightFields(field)
    case (TupleShape(leftLength, leftElements), TupleShape(rightLength, rightElements)) =>
      leftLength === rightLength
        && leftElements.zip(rightElements).forall((left, right) => left <= right)
    case _ => false

private object Shape:
  def mkShapeByPattern(pattern: Pattern)(using raise: Raise): Shape =
    pattern match
      case ctorPattern @ Pattern.Constructor(_, arguments) =>
        val ctor = ctorPattern.symbol.flatMap:
          case ctor: ClassCtorSymbol => S(ctor.associatedCls)
          case symbol => symbol.asClsLike
        ctor match
          case S(cls: ClassSymbol) =>
            cls.tree.clsParams match
              case fields :: Nil =>
                val argumentShapes = arguments match
                  case S(patterns) => patterns.map(mkShapeByPattern)
                  case N => Nil
                if argumentShapes.size =/= fields.size then
                  raise(ErrorReport(
                    msg"Expected constructor arity ${fields.size} in @matchShapes pattern for ${cls.nme}, but found ${argumentShapes.size}." -> pattern.toLoc :: Nil,
                    source = Diagnostic.Source.Compilation,
                  ))
                  DynamicShape
                else ClassShape(cls, fields.zip(argumentShapes).toMap)
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

private case class LitShape(lit: Value.Lit) extends Shape:
  def show: Str = lit match
    case Value.Lit(lit) => lit.idStr

  def flattenShape: List[Shape] = this :: Nil

  def containsUnion: Bool = false

private case class ClassShape(ctor: ClassLikeSymbol, fields: Map[TermSymbol, Shape]) extends Shape:
  def show: Str =
    if fields.isEmpty then ClassTagsDebug.showCtor(ctor)
    else
      val shownFields = fields.iterator
        .map((field, shape) => s"${ClassTagsDebug.showField(field)}: ${shape.show}")
      s"${ClassTagsDebug.showCtor(ctor)}${shownFields.mkString("(", ", ", ")")}"

  def flattenShape: List[Shape] =
    val alternatives = fields.iterator.foldLeft(List(Map.empty[TermSymbol, Shape])):
      case (alternatives, (field, fieldShape)) =>
        for
          alternative <- alternatives
          concreteFieldShape <- fieldShape.flattenShape
        yield alternative.updated(field, concreteFieldShape)
    alternatives.map(ClassShape(ctor, _)).distinct

  def containsUnion: Bool = fields.valuesIterator.exists(_.containsUnion)

private case class TupleShape(length: Int, elements: List[Shape]) extends Shape:
  require(elements.length === length)
  def show: Str =
    if elements.isEmpty then ClassTagsDebug.showCtor(length)
    else s"${ClassTagsDebug.showCtor(length)}${elements.map(_.show).mkString("(", ", ", ")")}"

  def flattenShape: List[Shape] =
    val alternatives = elements.foldLeft(List(List.empty[Shape])):
      case (alternatives, element) =>
        for
          alternative <- alternatives
          concreteElement <- element.flattenShape
        yield alternative :+ concreteElement
    alternatives.map(TupleShape(length, _)).distinct

  def containsUnion: Bool = elements.exists(_.containsUnion)

private case class UnionShape(subshapes: List[Shape]) extends Shape:
  def show: Str = subshapes.map(_.show).mkString("(", " | ", ")")

  def flattenShape: List[Shape] =
    subshapes.flatMap(_.flattenShape).distinct

  def containsUnion: Bool = true

private object UnionShape:
  def mkUnion(shapes: Iterable[Shape]): Shape =
    val flattened = shapes.iterator.flatMap:
      case UnionShape(subshapes) if subshapes.nonEmpty => subshapes
      case shape => shape :: Nil
    val normalized = flattened.toList.distinct.sortBy(_.show)
    normalized match
      case Nil => DynamicShape
      case shape :: Nil => shape
      case shapes => UnionShape(shapes)

private object DynamicShape extends Shape:
  def show: Str = "_"

  def flattenShape: List[Shape] = this :: Nil

  def containsUnion: Bool = false

class ClassTagsTransformer(
  val webs: List[Web],
  val flowRes: FlowConstraintSolver,
  val debug: Bool,
)(using State, Elaborator.Ctx, TL, Raise) extends BlockTransformer(SymbolSubst.Id):
  private given fState: FlowAnalysis.State = flowRes.fState

  private val producersInWeb = webs.iterator.flatMap(_.markedProducers).toSet

  private val ctorsByResultId = producersInWeb.iterator.map(ctor => ctor.exprId -> ctor).toMap

  private val patternMatchesByResultId =
    flowRes.consumersWithSrcs.iterator.collect:
      case patternMatch: Dtor => patternMatch
    .toList.groupBy(_.exprId)

  private val shapeTags = MutMap.empty[Shape, Int]

  private val tagField = new syntax.Tree.Ident("__tag$")

  // * Allocate a tag for a shape in the web
  private def allocateTag(shape: Shape): Int =
    shapeTags.getOrElseUpdate(shape, {
      val tag = shapeTags.size
      if debug then
        summon[TL].emitDbg(
          s"class-tags transform-phase > allocated tag $tag for ${shape.show}")
      tag
    })

  private lazy val taggedShapesByProducer: Map[Ctor, List[ClassShape -> Int]] =
    given visit: Set[ProdStrat] = Set.empty
    producersInWeb.toList.sortBy(_.exprId.uid).flatMap: producer =>
      val shapes = shapeOfProducer(producer) match
        case shape: ClassShape =>
          shape.flattenShape.collect:
            case shape: ClassShape => shape
        case _ => Nil
      val taggedShapes = shapes.map(shape => shape -> allocateTag(shape))
      if taggedShapes.isEmpty then Nil
      else (producer -> taggedShapes) :: Nil
    .toMap

  private def getCtorArgs(producer: Ctor) =
    producer.exprId.getResult match
      case CtorProducer(_, args, _) =>
        softAssert(
          args.size === producer.args.size,
          s"Mismatched constructor arguments for ${ClassTagsDebug.showProducer(producer)}",
        )
        args
      case result =>
        softAssert(
          false,
          s"Missing constructor result for ${ClassTagsDebug.showProducer(producer)}: ${result.showDbg}",
        )
        Nil

  private def shapeOfProducer(producer: Ctor)(using visit: Set[ProdStrat]): Shape =
    if visit.contains(producer) then DynamicShape
    else
      given next: Set[ProdStrat] = visit + producer
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
            s"Unexpected class fields in ${ClassTagsDebug.showProducer(producer)}",
          )
          ClassShape(cls, fields.toMap)
        case length: Int =>
          softAssert(
            fieldsOrElements.size === length,
            s"Mismatched tuple arity for ${ClassTagsDebug.showProducer(producer)}",
          )
          TupleShape(length, fieldsOrElements.map(_._2))

  private def shapeOf(producer: ProdStrat, original: Opt[Path])(using visit: Set[ProdStrat]): Shape =
    original match
      case S(lit: Value.Lit) => LitShape(lit)
      case _ => producer match
        case ctor: Ctor => shapeOfProducer(ctor)
        case variable: StratVar =>
          if visit.contains(variable) then DynamicShape
          else
            given next: Set[ProdStrat] = visit + variable
            UnionShape.mkUnion:
              variable.lowerBounds.map: lowerBound =>
                shapeOf(lowerBound, N)
        case _ => DynamicShape

  // * Get all (shape, tag) pair of the given scrutinee
  private def taggedShapesOfMatchScrutinee(matchResultId: ResultId): List[Shape -> Int] =
    val taggedShapes = patternMatchesByResultId.getOrElse(matchResultId, Nil).iterator
      .flatMap(_.srcs)
      .collect:
        case ctor: Ctor => ctor
      .toList.distinct.flatMap: ctor =>
        taggedShapesByProducer.getOrElse(ctor, Nil)
    taggedShapes.distinct.sortBy(_._2) // sort to avoid changing debug printing everytime

  private def bindResult(result: Result)(k: Path => Block): Block = result match
    case path: Path => k(path)
    case result =>
      val symbol = new TempSymbol(N, erasedType = result.erasedValueType, "tmp")
      val reference = symbol.asSimpleRef.withLocOf(result)
      Scoped(Set.single(symbol), Assign(symbol, result, k(reference)))

  private def assignTag(instance: Path, tag: Int)(next: Block): Block = // TODO: make __tag$ a real field and fill the symbol for selections
    AssignField(instance, tagField, Value.Lit(syntax.Tree.IntLit(tag)), next)(N)

  private def insertTagForMultiShapes(
    result: Result, args: List[Arg], producer: Ctor, taggedShapes: List[ClassShape -> Int]
  )(k: Path => Block): Block =
    val arguments = producer.args.iterator.map(_._1).zip(args.iterator.map(_.value)).collect:
      case (field: TermSymbol, path) => field -> path
    .toList

    def checkTagEq(left: Path, right: Path)(k: Path => Block) =
      bindResult(Call(State.builtinOpsMap("===").asSimpleRef, (left.asArg :: right.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun))(k)

    def checkShape(argument: Path, shape: Shape)(k: Path => Block) =
      shapeTags.get(shape) match
        case S(tag) => checkTagEq(
          Select(argument, tagField)(N)(false).withLocOf(argument), Value.Lit(syntax.Tree.IntLit(tag))
        )(k)
        case N => shape match
          case LitShape(lit) => checkTagEq(argument, lit)(k)
          case TupleShape(length, elements) =>
            val condition = new TempSymbol(N, erasedType = S(ErasedType.Bool), "tmp")
            val conditionRef = condition.asSimpleRef.withLocOf(argument)
            val elementChecks = elements.zipWithIndex.map: (element, index) =>
              DynSelect(argument, Value.Lit(syntax.Tree.IntLit(index)), true).withLocOf(argument) -> element
            val matched = mkConjunction(elementChecks): elementsMatch =>
              Assign(condition, elementsMatch, End())
            Scoped(Set.single(condition),
              new Match(argument, Case.Tup(length, false) -> matched :: Nil,
                S(Assign(condition, Value.Lit(syntax.Tree.BoolLit(false)), End())),
                k(conditionRef)))
          case DynamicShape => k(Value.Lit(syntax.Tree.BoolLit(true)))
          case _ => lastWords(s"Shape ${shape.show} cannot be checked directly.")

    // * Generate tag checks for each parameter and form a conjunction condition
    def mkConjunction(checks: List[Path -> Shape])(k: Path => Block): Block =
      def rec(checks: List[Path -> Shape])(k: Path => Block): Block = checks match
        case Nil => k(Value.Lit(syntax.Tree.BoolLit(true)))
        case (argument, shape) :: Nil => checkShape(argument, shape)(k)
        case (argument, shape) :: checks =>
          checkShape(argument, shape): condition =>
            condition match
              case Value.Lit(syntax.Tree.BoolLit(true)) => rec(checks)(k)
              case Value.Lit(syntax.Tree.BoolLit(false)) => k(condition)
              case _ =>
                val result = new TempSymbol(N, erasedType = S(ErasedType.Bool), "tmp")
                val reference = result.asSimpleRef.withLocOf(condition)
                val matched = rec(checks): remainingCondition =>
                  Assign(result, remainingCondition, End())
                Scoped(Set.single(result),
                  new Match(
                    condition,
                    Case.Lit(syntax.Tree.BoolLit(true)) -> matched :: Nil,
                    S(Assign(result, Value.Lit(syntax.Tree.BoolLit(false)), End())),
                    k(reference),
                  ))
      // remove conditions that are already true
      rec(checks.filterNot:
        case (_, DynamicShape) => true
        case (argument, LitShape(lit)) => argument === lit
        case _ => false)(k)

    def assign(remainingShapes: List[ClassShape -> Int], instance: Path): Block =
      remainingShapes match
        case (shape, tag) :: remainingShapes =>
          val checks = arguments.map: (field, argument) =>
            argument -> shape.fields(field)
          mkConjunction(checks): condition =>
            new Match(
              condition,
              Case.Lit(syntax.Tree.BoolLit(true)) -> assignTag(instance, tag)(End()) :: Nil,
              if remainingShapes.isEmpty then N else S(assign(remainingShapes, instance)),
              End(),
            )
        case Nil => End()

    bindResult(result): instance =>
      Begin(assign(taggedShapes, instance), k(instance))

  private def insertShapeTag(
    result: Result, producer: Ctor, taggedShapes: List[ClassShape -> Int]
  )(k: Path => Block): Block =
    taggedShapes match
      case (_, tag) :: Nil =>
        bindResult(result): instance =>
          assignTag(instance, tag)(k(instance))
      case _ :: _ => result match
        case CtorProducer(_, args, _) =>
          insertTagForMultiShapes(result, args, producer, taggedShapes)(k)
        case _ =>
          lastWords(s"Missing constructor result for ${ClassTagsDebug.showProducer(producer)}")
      case Nil =>
        lastWords(s"Missing concrete shape for ${ClassTagsDebug.showProducer(producer)}")

  override def applyProgram(program: Program): Program =
    if debug then
      summon[TL].emitDbg(">>> start class-tags transform-phase")
    val _ = taggedShapesByProducer
    val result = super.applyProgram(program)
    if debug then
      summon[TL].emitDbg("<<< end class-tags transform-phase")
    result

  override def applyFunDefn(fun: FunDefn): FunDefn =
    val transformer = new BlockTransformerShallow(SymbolSubst.Id):
      private def isShapeMatch(path: Path): Bool =
        path.targetSymbol.flatMap(_.asBlkMember).contains(Elaborator.ctx.builtins.shape.`match`)

      // * get the branch body defined as a FunDefn
      private def getBranch(path: Path): Opt[FunDefn] =
        path.targetSymbol.collect:
          case symbol: TermSymbol => symbol
        .flatMap(flowRes.preAnalyzer.res.funSymToFunDefn.get)

      // * Generate branch based on the branch function
      private def mkBranch(branch: FunDefn, resultSymbol: TempSymbol): Block =
        SymbolRefresher(Map.empty).apply(applyFunBodyLikeBlock(branch.body)).mapReturn:
          case Return(result) => Assign(resultSymbol, result, End())

      private def rewriteShapeMatch(call: Call, scrutinee: Path, branchArgs: List[Arg])(k: Result => Block): Opt[Block] =
        call.metadata.annotations.collectFirst:
          case Annot.MatchShapes(patterns) => patterns
        .flatMap: patterns =>
          val branches = branchArgs.map(arg => getBranch(arg.value))
          val malformedReasons =
            (if patterns.size =/= branchArgs.size then
              msg"The number of @matchShapes patterns (${patterns.size}) does not match the number of shape.match branches (${branchArgs.size})." -> call.toLoc :: Nil
            else Nil) ++
            branchArgs.zip(branches).collect:
              case (arg, N) =>
                msg"This shape.match branch does not resolve to a function." -> arg.value.toLoc
          if malformedReasons.nonEmpty then
            summon[Raise].apply(ErrorReport(
              msg"Malformed annotated shape.match call." -> call.toLoc :: malformedReasons,
              source = Diagnostic.Source.Compilation,
            ))
            N
          else
            val branchDefns = branches.flatten
            val branchesWithParams = branchArgs.zip(branchDefns).collect:
              case (arg, branch)
                  if branch.params.exists(paramList => paramList.params.nonEmpty || paramList.restParam.nonEmpty) =>
                arg.value
            if branchesWithParams.nonEmpty then
              summon[Raise].apply(ErrorReport(
                msg"Annotated shape.match branches must take no arguments." -> call.toLoc ::
                branchesWithParams.map: branch =>
                  msg"This branch takes arguments." -> branch.toLoc,
                source = Diagnostic.Source.Compilation,
              ))
              N
            else
              val patternShapes = patterns.map(Shape.mkShapeByPattern)
              val taggedShapes = taggedShapesOfMatchScrutinee(call.uid)
              if debug then
                val shownTaggedShapes =
                  if taggedShapes.isEmpty then "<none>"
                  else taggedShapes.map((shape, tag) => s"${shape.show}@$tag").mkString(", ")
                summon[TL].emitDbg(
                  s"class-tags transform-phase > match shapes ${patternShapes.map(_.show).mkString(", ")} against $shownTaggedShapes")
              if patternShapes.exists(_.containsUnion) then
                softAssert(false, "@matchShapes patterns must not contain union shapes.")
                N
              else
                val ambiguousTags = taggedShapes.flatMap: (taggedShape, tag) =>
                  val branchIndices = taggedShape.flattenShape.flatMap: concreteShape =>
                    patternShapes.zipWithIndex.collect:
                      case (patternShape, index) if concreteShape <= patternShape => index
                  .distinct
                  if branchIndices.size > 1 then S((taggedShape, tag, branchIndices)) else N
                if ambiguousTags.nonEmpty then
                  for (taggedShape, tag, branchIndices) <- ambiguousTags do
                    val messages =
                      msg"Shape tag $tag for ${taggedShape.show} can fall into more than one shape.match branch." -> call.toLoc ::
                      branchIndices.map: index =>
                        msg"It can fall into branch ${index + 1}, matched by ${patternShapes(index).show}." -> patterns(index).toLoc
                    summon[Raise].apply(WarningReport(messages))
                  N
                else
                  val matchingBranches = patternShapes.zip(branchDefns).flatMap: (patternShape, branch) =>
                    taggedShapes.collect:
                      case (taggedShape, tag) if taggedShape <= patternShape =>
                        (taggedShape, tag, branch)
                  val matchedTags = matchingBranches.iterator.map(_._2).toSet
                  val unmatchedShapes = taggedShapes.filter((_, tag) => !matchedTags.contains(tag))
                  if taggedShapes.isEmpty then
                    summon[Raise].apply(ErrorReport(
                      msg"Annotated shape.match has no tagged class shapes for its scrutinee." -> call.toLoc :: Nil,
                      source = Diagnostic.Source.Compilation,
                    ))
                    N
                  else if unmatchedShapes.nonEmpty then
                    summon[Raise].apply(ErrorReport(
                      msg"Annotated shape.match does not cover every possible scrutinee shape." -> call.toLoc ::
                      unmatchedShapes.map: (shape, tag) =>
                        msg"Shape ${shape.show} with tag $tag does not match any @matchShapes pattern." -> call.toLoc,
                      source = Diagnostic.Source.Compilation,
                    ))
                    N
                  else
                    val resultSymbol = new TempSymbol(N, erasedType = call.erasedValueType, "shapeMatchResult")
                    val resultRef = resultSymbol.asSimpleRef.withLocOf(call)
                    val tagAccess = Select(scrutinee, tagField)(N)(false).withLocOf(scrutinee)
                    val arms = matchingBranches.map: (_, tag, branch) =>
                      Case.Lit(syntax.Tree.IntLit(tag)) -> mkBranch(branch, resultSymbol)
                    S(Scoped(Set.single(resultSymbol), new Match(tagAccess, arms, N, k(resultRef))))

      override def applyResult(result: Result)(k: Result => Block): Block =
        result match
          case call @ Call(fun, (Arg(N, scrutinee) :: branches) :: Nil) if branches.nonEmpty && isShapeMatch(fun) =>
            // Rewrite annotated shape.match calls
            rewriteShapeMatch(call, scrutinee, branches)(k).getOrElse:
              super.applyResult(result)(k)
          case CtorProducer(_, _, _) =>
            // Insert tags for instantiations
            // TODO: make the tag a real field? 
            (ctorsByResultId.get(result.uid).flatMap: ctor =>
              taggedShapesByProducer.get(ctor).map(ctor -> _)
            ) match
              case S((ctor, taggedShapes)) =>
                super.applyResult(result): transformed =>
                  insertShapeTag(transformed, ctor, taggedShapes)(k)
              case N => super.applyResult(result)(k)
          case _ => super.applyResult(result)(k)
    val body = transformer.applyFunBodyLikeBlock(fun.body)
    val transformed =
      if body is fun.body then fun
      else FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, body)(fun.configOverride, fun.annotations)
    super.applyFunDefn(transformed)
end ClassTagsTransformer


object ClassTagsTransformer:
  private def mkWeb(entries: WebEntryCollector.EntryPoints): Web =
    val result = FlowWebComputation[ProdStrat, ConcreteCtorConsumer | ProdStrat](
      producer => producer match
        case ctor: Ctor =>
          val consumers = ctor.dests.iterator.collect:
            case consumer: ConcreteCtorConsumer =>
              consumer: ConcreteCtorConsumer | ProdStrat
          consumers ++ ctor.args.iterator.map(_._2)
        case variable: StratVar => variable.lowerBounds
        case _ => Nil,
      consumer => consumer match
        case consumer: ConcreteCtorConsumer => consumer.srcs
        case variable: StratVar => variable.lowerBounds
        case producer: ProdStrat => producer :: Nil,
      entries.producers,
      entries.consumers,
    )
    FlowWebComputation.Result[Ctor, ConcreteCtorConsumer](
      result.markedProducers.collect:
        case ctor: Ctor => ctor,
      result.markedConsumers.collect:
        case consumer: ConcreteCtorConsumer => consumer,
    )

  private def mkWebs(entryPoints: List[WebEntryCollector.EntryPoints]) =
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
      tl.emitDbg(">>> start class-tags web-computation-phase")
      for (web, index) <- webs.zipWithIndex do
        val producers = web.markedProducers.toList.sortBy(_.exprId.uid)
        val fieldAccesses = web.markedConsumers.collect:
          case access: FieldSel => access
        val patternMatches = web.markedConsumers.collect:
          case patternMatch: Dtor => patternMatch
        tl.emitDbg(s"class-tags web-computation-phase > web $index:")
        tl.emitDbg(s"class-tags web-computation-phase >   producers: ${producers.map(ClassTagsDebug.showProducer).mkString(", ")}")
        if fieldAccesses.nonEmpty then
          tl.emitDbg(s"class-tags web-computation-phase >   field accesses: ${fieldAccesses.toList.sortBy(_.exprId.uid).map(ClassTagsDebug.showFieldAccess).mkString(", ")}")
        if patternMatches.nonEmpty then
          tl.emitDbg(s"class-tags web-computation-phase >   pattern matches: ${patternMatches.toList.sortBy(_.exprId.uid).map(ClassTagsDebug.showPatternMatch).mkString(", ")}")
      tl.emitDbg("<<< end class-tags web-computation-phase")

  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: State,
    ctx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
  ): Program =
    cfg.classTags match
      case N => p
      case S(_) if !cfg.noFreeze => // TODO: make the tag a real field and remove this restriction.
        raise(ErrorReport(
          msg"Class tag insertion requires :noFreeze." -> N :: Nil,
          source = Diagnostic.Source.Compilation,
        ))
        p
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
          FlowAnalysis.mkTraceLogger(flowCfg, "class-tags flow-analysis-phase > ", tl).givenIn:
            FlowAnalysis(
              p,
              mono = flowCfg.mono,
              nonAffineTracking = false,
              accumulatorTracking = false,
            )
        val collectorTl = new TraceLogger(using tl.debugPrinter):
          override def doTrace: Bool = dCfg.debug
          override def emitDbg(str: Str): Unit =
            tl.emitDbg(s"class-tags collection-phase > $str")
        val entryPoints = collectorTl.givenIn:
          if dCfg.debug then tl.emitDbg(">>> start class-tags collection-phase")
          val result = WebEntryCollector(p, flowAnalysisRes)
          if dCfg.debug then tl.emitDbg("<<< end class-tags collection-phase")
          result
        val webs = mkWebs(entryPoints)
        if dCfg.debug then logWebs(webs)
        new ClassTagsTransformer(webs, flowAnalysisRes, dCfg.debug).applyProgram(p)
