package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*
import Message.MessageContext

import semantics.*
import flowAnalysis.*

import hkmc2.semantics.Elaborator.State

import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashSet as MutLinkedHashSet}
import scala.collection.mutable.ListBuffer
import scala.util.boundary

type Web = FlowWebComputation.Result[Ctor, ConcreteCtorConsumer]

private object ClassTagsDebug:
  def showCtor(ctor: CtorCls): Str = ctor match
    case cls: ClassLikeSymbol => cls.nme
    case size: Int => s"tup(size $size)"

  def showField(field: SelField): Str = field match
    case sym: TermSymbol => sym.nme
    case index: Int => index.toString

  def showProducer(producer: Ctor): Str =
    s"${showCtor(producer.ctor)}@${producer.exprId.uid}"

  def showFieldAccess(access: FieldSel): Str =
    s"${{showCtor(access.selectsFrom)}}.${showField(access.field)}@${access.exprId.uid}"

  def showPatternMatch(patternMatch: Dtor): Str =
    s"match@${patternMatch.exprId.uid}"

  def showConsumer(consumer: ConcreteCtorConsumer): Str = consumer match
    case access: FieldSel => showFieldAccess(access)
    case patternMatch: Dtor => showPatternMatch(patternMatch)

// * Collect all producers & consumers in the given function to build the web
class WebEntryCollector(val flowRes: FlowConstraintSolver)(using val tl: TL) extends BlockTraverser:
  private given fState: FlowAnalysis.State = flowRes.fState
  private given eState: State = flowRes.eState

  private val entryPoints = ListBuffer.empty[WebEntryCollector.EntryPoints]
  private val concreteCtorsByResultId = MutMap.empty[ResultId, ListBuffer[Ctor]]
  for ctor <- flowRes.ctorsWithDests do
    concreteCtorsByResultId.getOrElseUpdate(ctor.exprId, ListBuffer.empty) += ctor
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
      ctor <- concreteCtorsByResultId.getOrElse(resultId, Nil)
      if !ctor.dests.contains(UnknownCons) // does not leak out of the web
      if !ctor.dests.exists:
        case consumer: ConcreteCtorConsumer => consumer.srcs.contains(UnknownProd)
        case _ => false
    do seenProducerEntryPoints.add(ctor)

    if !seenProducerEntryPoints.isEmpty then
      tl.log(s"track construction of ${seenProducerEntryPoints.map(ClassTagsDebug.showProducer).mkString(", ")} in $funName")

    val seenConsumerEntryPoints = MutSet.empty[ConcreteCtorConsumer]
    for
      resultId <- collector.resultIds
      consumer <- concreteConsumersByResultId.getOrElse(resultId, Nil)
      if !consumer.srcs.contains(UnknownProd) // not allocated out of the web
      if !consumer.srcs.exists:
        case ctor: Ctor => ctor.dests.contains(UnknownCons)
        case _ => false
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

  def flattenWithin(budget: Int): Opt[List[Shape]]

  def flat: List[Shape] = this :: Nil

  final def tupleLength: Opt[Int] =
    val alternatives = flat
    val lengths = alternatives.collect:
      case TupleShape(length, _) => length
    .distinct
    if lengths.sizeCompare(1) === 0 && alternatives.sizeCompare(alternatives.count {
      case TupleShape(_, _) => true
      case _ => false
    }) === 0 then S(lengths.head) else N

  def containsUnion: Bool

  // * This shape subsumption is only used for wildcards (dynamic shapes) checking.
  // * i.e., if the pattern is a wildcard, it can accept any scrutinee
  // * We do not support a union shape for pattern
  // * and we flattern unions in Ctor to insert different tags
  // * We also track precise information so we do not need to check if a class is a subclass of another.
  // * i.e., if a variable has shape C, then it is impossible that the variable is instantiated to a subclass D in runtime.
  final infix def <=(that: Shape): Bool = (this, that) match
    case (BotShape, _) => true
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
  import ClassTagsTransformer.classFields

  val flattenBudget: Int = 256

  def mkShapeByPattern(pattern: Pattern)(using Config, Erasure, Raise): Shape =
    pattern match
      case ctorPattern @ Pattern.Constructor(_, arguments) =>
        // New resolution records the constructor selected in pattern context separately
        // from its target term, which may also denote a term companion.
        val symbol =
          if config.language.useNewResolution then ctorPattern.resolvedTargets.distinct match
            case sym :: Nil if !ctorPattern.isErroneous => S(sym)
            case _ => N
          else ctorPattern.target.resolvedSym
        val ctor = symbol.flatMap:
          case ctor: ClassCtorSymbol => S(ctor.associatedCls)
          case symbol => symbol.asClsLike
        ctor match
          case S(cls: ClassSymbol) =>
            cls.classFields match
              case S(fields) =>
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
              case N =>
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
      case Pattern.Literal(literal) => LitShape(Value.Lit(literal)(literal.toLoc))
      case Pattern.Wildcard() => DynamicShape
      case _ =>
        raise(ErrorReport(
          msg"This pattern is not supported by @matchShapes yet." -> pattern.toLoc :: Nil,
          source = Diagnostic.Source.Compilation,
        ))
        DynamicShape

private case class LitShape(lit: Value.Lit) extends Shape:
  override lazy val show: Str = lit match
    case Value.Lit(lit) => lit.idStr

  def flattenWithin(budget: Int): Opt[List[Shape]] = S(this :: Nil)

  def containsUnion: Bool = false

private case class ClassShape(ctor: ClassLikeSymbol, fields: Map[TermSymbol, Shape]) extends Shape:
  require(!fields.valuesIterator.contains(BotShape))
  override lazy val show: Str =
    if fields.isEmpty then ClassTagsDebug.showCtor(ctor)
    else
      val shownFields = fields.iterator
        .map((field, shape) => s"${ClassTagsDebug.showField(field)}: ${shape.show}")
      s"${ClassTagsDebug.showCtor(ctor)}${shownFields.mkString("(", ", ", ")")}"

  def flattenWithin(budget: Int): Opt[List[Shape]] = boundary:
    var alternatives = MutLinkedHashSet(Map.empty[TermSymbol, Shape])
    val remainingFields = fields.iterator
    while remainingFields.hasNext do
      val (field, fieldShape) = remainingFields.next()
      fieldShape.flattenWithin(budget) match
        case N => boundary.break(N)
        case S(concreteFieldShapes) =>
          val extended = MutLinkedHashSet.empty[Map[TermSymbol, Shape]]
          for alternative <- alternatives; concrete <- concreteFieldShapes do
            extended += alternative.updated(field, concrete)
            if extended.size > budget then boundary.break(N)
          alternatives = extended
    S(alternatives.iterator.map(ClassShape(ctor, _)).toList)

  def containsUnion: Bool = fields.valuesIterator.exists(_.containsUnion)

private case class TupleShape(length: Int, elements: List[Shape]) extends Shape:
  require(elements.length === length)
  require(!elements.contains(BotShape))
  override lazy val show: Str =
    if elements.isEmpty then ClassTagsDebug.showCtor(length)
    else s"${ClassTagsDebug.showCtor(length)}${elements.map(_.show).mkString("(", ", ", ")")}"

  def flattenWithin(budget: Int): Opt[List[Shape]] = boundary:
    var alternatives = MutLinkedHashSet(List.empty[Shape])
    val remainingElements = elements.iterator
    while remainingElements.hasNext do
      val element = remainingElements.next()
      element.flattenWithin(budget) match
        case N => boundary.break(N)
        case S(concreteElements) =>
          val extended = MutLinkedHashSet.empty[List[Shape]]
          for alternative <- alternatives; concrete <- concreteElements do
            extended += concrete :: alternative
            if extended.size > budget then boundary.break(N)
          alternatives = extended
    S(alternatives.iterator.map(prefix => TupleShape(length, prefix.reverse)).toList)

  def containsUnion: Bool = elements.exists(_.containsUnion)

private case class UnionShape(subshapes: List[Shape]) extends Shape:
  require(!subshapes.contains(BotShape))
  override lazy val show: Str = subshapes.map(_.show).mkString("(", " | ", ")")

  def flattenWithin(budget: Int): Opt[List[Shape]] =
    val alternatives = MutLinkedHashSet.empty[Shape]
    val remaining = subshapes.iterator
    while remaining.hasNext do
      remaining.next().flattenWithin(budget) match
        case N => return N
        case S(flattened) =>
          alternatives ++= flattened
          if alternatives.size > budget then return N
    S(alternatives.toList)

  override def flat: List[Shape] = subshapes

  def containsUnion: Bool = true

private object UnionShape:
  val classDecayThreshold: Int = 8

  def mkUnion(shapes: Iterable[Shape], rank: Shape => Int): Shape =
    val normalized = MutLinkedHashSet.empty[Shape]
    shapes.iterator.foreach:
      case UnionShape(subshapes) if subshapes.nonEmpty => normalized ++= subshapes
      case BotShape => ()
      case shape => normalized += shape
    val members = decayWideClasses(normalized)
    if members.isEmpty then BotShape
    else if members.size === 1 then members.head
    else UnionShape(members.toList.sortBy(rank))

  private def decayWideClasses(members: MutLinkedHashSet[Shape]): MutLinkedHashSet[Shape] =
    val classMembers = members.toList.collect { case shape: ClassShape => shape }
    val wide = classMembers.groupBy(_.ctor).collect {
      case (ctor, group) if group.size > classDecayThreshold => ctor -> decayedShape(group)
    }
    if wide.isEmpty then members
    else
      val result = MutLinkedHashSet.empty[Shape]
      members.iterator.foreach:
        case shape: ClassShape if wide.contains(shape.ctor) => result += wide(shape.ctor)
        case shape => result += shape
      result

  private def decayedShape(group: List[ClassShape]): Shape =
    val widest = group.maxBy(_.fields.size)
    ClassShape(widest.ctor, widest.fields.map((field, _) => field -> (DynamicShape: Shape)))

private object DynamicShape extends Shape:
  def show: Str = "_"

  def flattenWithin(budget: Int): Opt[List[Shape]] = S(this :: Nil)

  def containsUnion: Bool = false

private object BotShape extends Shape:
  def show: Str = "⊥"

  def flattenWithin(budget: Int): Opt[List[Shape]] = S(Nil)

  override def flat: List[Shape] = Nil

  def containsUnion: Bool = false

private class ShapeProp(
  funDefns: collection.Map[TermSymbol, FunDefn],
  patternShapesByCall: collection.Map[ResultId, List[Shape]],
)(using FlowAnalysis.State, State, Elaborator.Ctx):
  private type Ctx = Map[Path, Shape]

  import ClassTagsTransformer.classFields

  val shapeByResultId: MutMap[ResultId, Shape] = MutMap.empty
  val shapeTags: MutMap[Shape, Int] = MutMap.empty

  private val shapeRanks = MutMap.empty[Shape, Int]
  def rank(shape: Shape): Int = shapeRanks.getOrElseUpdate(shape, shapeRanks.size)

  private val cache = MutMap.empty[(TermSymbol, Shape, List[Shape]), Shape]
  private val visitSet = MutSet.empty[TermSymbol]
  private val entryPoints = ListBuffer.empty[FunDefn]

  def applyProgram(program: Program): Unit =
    collectEntryPoints(program.main)
    for fun <- entryPoints.toList do
      val args = fun.params.flatMap(_.params).map(_ => DynamicShape: Shape)
      propFun(fun, selfShape(fun), args)
    prop(program.main, Map.empty)
    ()

  private def selfShape(fun: FunDefn): Shape = fun.owner match
    case S(cls: ClassSymbol) => silhouette(cls)
    case _ => DynamicShape

  private def silhouette(cls: ClassLikeSymbol): Shape = cls.classFields match
    case S(fields) => ClassShape(cls, fields.map(_ -> (DynamicShape: Shape)).toMap)
    case N => DynamicShape

  private def silhouette(cse: Case): Shape = cse match
    case Case.Lit(lit) => LitShape(Value.Lit(lit)(N))
    case Case.Cls(cls, _) => silhouette(cls)
    case Case.Tup(len, _) => TupleShape(len, List.fill(len)(DynamicShape))
    case Case.Field(_, _) => DynamicShape

  private def subclass(sub: ClassLikeSymbol, sup: ClassLikeSymbol): Opt[Bool] =
    def go(cur: ClassLikeSymbol): Opt[Bool] =
      if cur is sup then S(true)
      else cur.irClassHeader.fold(ClassHeader.Parent.Unknown)(_.parent) match
        case ClassHeader.Parent.Root => S(false)
        case ClassHeader.Parent.Unknown => N
        case ClassHeader.Parent.Known(parent) => parent.asClsOrMod match
          case S(parent) => go(parent)
          case N => N
    go(sub)

  private def collectEntryPoints(block: Block): Unit = block match
    case Define(defn, rest) =>
      defn match
        case fun: FunDefn => entryPoints += fun
        case defn: ClsLikeDefn =>
          entryPoints ++= defn.methods
          defn.companion.foreach(companion => entryPoints ++= companion.methods)
          collectEntryPoints(defn.preCtor)
          collectEntryPoints(defn.ctor)
          defn.companion.foreach(companion => collectEntryPoints(companion.ctor))
        case _ => ()
      collectEntryPoints(rest)
    case Match(_, arms, dflt, rest) =>
      arms.foreach((_, body) => collectEntryPoints(body))
      dflt.foreach(collectEntryPoints)
      collectEntryPoints(rest)
    case Begin(sub, rest) => collectEntryPoints(sub); collectEntryPoints(rest)
    case TryBlock(sub, finallyDo, rest) =>
      collectEntryPoints(sub); collectEntryPoints(finallyDo); collectEntryPoints(rest)
    case Label(_, _, body, rest) => collectEntryPoints(body); collectEntryPoints(rest)
    case Scoped(_, body) => collectEntryPoints(body)
    case Assign(_, _, rest) => collectEntryPoints(rest)
    case AssignField(_, _, _, rest) => collectEntryPoints(rest)
    case AssignDynField(_, _, _, _, rest) => collectEntryPoints(rest)
    case _ => ()

  private def mkUnion(shapes: List[Shape]): Shape =
    if shapes.contains(DynamicShape) then DynamicShape
    else UnionShape.mkUnion(shapes, rank)

  private def filterSet(set: List[Shape], cse: Case): List[Shape] = set.flatMap: alt =>
    (alt, cse) match
      case (LitShape(Value.Lit(left)), Case.Lit(right)) =>
        if left === right then alt :: Nil else Nil
      case (TupleShape(length, _), Case.Tup(len, _)) =>
        if length === len then alt :: Nil else Nil
      case (ClassShape(cls, _), Case.Cls(scrutCls, _)) =>
        if subclass(cls, scrutCls).contains(false) then Nil else alt :: Nil
      case (DynamicShape, _) => silhouette(cse) :: Nil
      case (LitShape(_), Case.Cls(_, _)) => alt :: Nil
      case (_, Case.Field(_, _)) => alt :: Nil
      case _ => Nil

  private def restSet(set: List[Shape], cse: Case): List[Shape] = set.flatMap: alt =>
    (alt, cse) match
      case (LitShape(Value.Lit(left)), Case.Lit(right)) =>
        if left === right then Nil else alt :: Nil
      case (TupleShape(length, _), Case.Tup(len, _)) =>
        if length === len then Nil else alt :: Nil
      case (ClassShape(cls, _), Case.Cls(scrutCls, _)) =>
        if subclass(cls, scrutCls).contains(true) then Nil else alt :: Nil
      case _ => alt :: Nil

  private def refineByPattern(shape: Shape, pattern: Shape): Opt[Shape] = pattern match
    case DynamicShape => S(shape)
    case _ => shape match
      case BotShape => S(BotShape)
      case UnionShape(subshapes) =>
        val kept = subshapes.flatMap(refineByPattern(_, pattern))
        if kept.isEmpty then N else S(mkUnion(kept))
      case DynamicShape => N 
      case LitShape(_) => if shape <= pattern then S(shape) else N
      case ClassShape(cls, fields) => pattern match
        case ClassShape(patternCls, patternFields)
            if cls === patternCls && fields.keySet === patternFields.keySet =>
          val narrowed = fields.toList.map: (field, fieldShape) =>
            field -> refineByPattern(fieldShape, patternFields(field))
          if narrowed.exists(_._2.isEmpty) then N
          else S(ClassShape(cls, narrowed.map((field, kept) => field -> kept.get).toMap))
        case _ => N
      case TupleShape(length, elements) => pattern match
        case TupleShape(patternLength, patternElements) if length === patternLength =>
          val narrowed = elements.zip(patternElements).map(refineByPattern)
          if narrowed.exists(_.isEmpty) then N
          else S(TupleShape(length, narrowed.map(_.get)))
        case _ => N

  private def propFun(fun: FunDefn, selfShape: Shape, argShapes: List[Shape]): Shape =
    val key = (fun.dSym, selfShape, argShapes)
    cache.get(key) match
      case S(shape) => shape
      case N if visitSet.contains(fun.dSym) => DynamicShape
      case N =>
        visitSet += fun.dSym
        val params = fun.params.flatMap(_.params)
        val bound = params.zip(argShapes).foldLeft(Map.empty[Path, Shape]):
          (acc, entry) => acc.updated(entry._1.sym.asSimpleRef, entry._2)
        val ctx = fun.owner match
          case S(owner) => bound.updated(owner.asThis, selfShape)
          case N => bound
        val returned = prop(fun.body, ctx)._1
        visitSet -= fun.dSym
        cache(key) = returned
        returned

  extension (fun: Path) private def resolveCallee: Opt[FunDefn] =
    fun.targetSymbol.collect:
      case sym: TermSymbol => sym
    .flatMap(funDefns.get)

  private def selShape(shape: Shape, name: Str): Shape = shape match
    case ClassShape(_, fields) =>
      fields.collectFirst:
        case (field, fieldShape) if field.nme === name => fieldShape
      .getOrElse(DynamicShape)
    case UnionShape(subshapes) => mkUnion(subshapes.map(selShape(_, name)))
    case BotShape => BotShape
    case _ => DynamicShape

  extension (path: Path) private def classValueOf: Opt[ClassLikeSymbol] = path.targetSymbol match
    case S(target) => target.asClsLike match
      case S(obj: ModuleOrObjectSymbol) => S(obj)
      case S(cls: ClassSymbol) if cls.tree.clsParams.isEmpty => S(cls)
      case _ => N
    case N => N

  private def selShape(shape: Shape, index: Int): Shape = shape match
    case TupleShape(_, elements) => elements.lift(index).getOrElse(DynamicShape)
    case UnionShape(subshapes) => mkUnion(subshapes.map(selShape(_, index)))
    case BotShape => BotShape
    case _ => DynamicShape

  private def shapeOfPath(path: Path, ctx: Ctx): Shape =
    ctx.get(path).orElse(path.classValueOf.map(ClassShape(_, Map.empty))) match
      case S(shape) => shape
      case N => path match
        case lit: Value.Lit => LitShape(lit)
        case sel: Select if sel.name.name === "length" =>
          shapeOfPath(sel.qual, ctx).tupleLength match
            case S(length) => LitShape(Value.Lit(syntax.Tree.IntLit(length))(N))
            case N => DynamicShape
        case sel: Select => selShape(shapeOfPath(sel.qual, ctx), sel.name.name)
        case DynSelect(qual, fld, _) =>
          shapeOfPath(fld, ctx) match
            case LitShape(Value.Lit(syntax.Tree.IntLit(index))) =>
              selShape(shapeOfPath(qual, ctx), index.toInt)
            case LitShape(Value.Lit(syntax.Tree.StrLit(name))) =>
              selShape(shapeOfPath(qual, ctx), name)
            case _ => DynamicShape
        case Cast(value: Path, _, _) => shapeOfPath(value, ctx)
        case _ => DynamicShape

  private def shapeOfResult(result: Result, ctx: Ctx): Shape = result match
    case CtorProducer(ctor, args, _) =>
      val argShapes = args.map(arg => shapeOfPath(arg.value, ctx))
      if argShapes.contains(BotShape) then BotShape
      else ctor match
        case cls: ClassLikeSymbol =>
          cls.classFields match
            case S(fields) if fields.size === argShapes.size =>
              ClassShape(cls, fields.zip(argShapes).toMap)
            case _ => DynamicShape
        case length: Int =>
          if argShapes.size === length then TupleShape(length, argShapes) else DynamicShape
    case path: Path => shapeOfPath(path, ctx)
    case call @ Call(fun, (Arg(N, scrutinee) :: branchArgs) :: Nil)
        if branchArgs.nonEmpty && ClassTagsTransformer.isShapeMatch(fun) =>
      val patternShapes = patternShapesByCall.getOrElse(call.uid, Nil)
      val known = shapeOfPath(scrutinee, ctx)
      val branchResults = branchArgs.zipWithIndex.map: entry =>
        entry._1.value.resolveCallee match
          case S(branch) if visitSet.contains(branch.dSym) => DynamicShape
          case S(branch) =>
            val refined = patternShapes.lift(entry._2) match
              case S(patternShape) =>
                ctx.updated(scrutinee, refineByPattern(known, patternShape).getOrElse(patternShape))
              case N => ctx
            visitSet += branch.dSym
            val shape = prop(branch.body, refined)._1
            visitSet -= branch.dSym
            shape
          case N => DynamicShape
      mkUnion(branchResults)
    case Call(fun, argss) =>
      fun.resolveCallee match
        case S(callee) =>
          val argShapes = argss.toList.flatten.map(arg => shapeOfPath(arg.value, ctx))
          val selfShape = fun match
            case sel: Select => shapeOfPath(sel.qual, ctx)
            case _ => DynamicShape
          propFun(callee, selfShape, argShapes)
        case N => DynamicShape
    case _ => DynamicShape

  private def mergeShapes(previous: Shape, next: Shape): Shape =
    if previous === next then previous
    else if previous === DynamicShape then next
    else if next === DynamicShape then previous
    else UnionShape.mkUnion(previous :: next :: Nil, rank)

  // * propagate shapes for results and mark them if we need to transform them
  private def checkResult(result: Result, ctx: Ctx): Shape =
    val shape = shapeOfResult(result, ctx)
    result match
      case CtorProducer(_, _, _) =>
        val merged = shapeByResultId.get(result.uid) match
          case S(previous) => mergeShapes(previous, shape)
          case N => shape
        shapeByResultId(result.uid) = merged
        for concrete <- merged.flattenWithin(Shape.flattenBudget).getOrElse(Nil) do concrete match
          case concrete: ClassShape => shapeTags.getOrElseUpdate(concrete, shapeTags.size)
          case _ => ()
      case _ => ()
    shape

  private def refine(scrut: Path, set: List[Shape], ctx: Ctx): Ctx =
    ctx.updated(scrut, mkUnion(set))

  private def mergeBranches(ctx: Ctx, branches: List[Ctx]): Ctx =
    val learnt = MutMap.empty[Path, List[Shape]]
    for branch <- branches; (path, shape) <- branch if !ctx.contains(path) do
      learnt(path) = learnt.getOrElse(path, Nil) :+ shape
    learnt.foldLeft(ctx)((acc, entry) => acc.updated(entry._1, mkUnion(entry._2.distinct)))

  private def prop(block: Block, ctx: Ctx): (Shape, Ctx) = block match
    case Assign(lhs, rhs, rest) =>
      val shape = checkResult(rhs, ctx)
      val next = lhs match
        case sym: LocalVarSymbol => ctx.updated(sym.asSimpleRef, shape)
        case _ => ctx
      prop(rest, next)
    case AssignField(_, _, rhs, rest) => checkResult(rhs, ctx); prop(rest, ctx)
    case AssignDynField(_, _, _, rhs, rest) => checkResult(rhs, ctx); prop(rest, ctx)
    case Define(defn, rest) =>
      defn match
        case defn: ValDefn => checkResult(defn.rhs, ctx)
        case _ => ()
      prop(rest, ctx)
    case Match(scrut, arms, dflt, rest) =>
      val branchShapes = ListBuffer.empty[Shape]
      val branchCtxs = ListBuffer.empty[Ctx]
      var remaining = shapeOfPath(scrut, ctx).flat
      for (cse, body) <- arms do
        val matching = filterSet(remaining, cse)
        if matching.nonEmpty then
          val (shape, branchCtx) = prop(body, refine(scrut, matching, ctx))
          branchShapes += shape
          branchCtxs += branchCtx
          remaining = restSet(remaining, cse)
      if remaining.nonEmpty then
        for body <- dflt do
          val (shape, branchCtx) = prop(body, refine(scrut, remaining, ctx))
          branchShapes += shape
          branchCtxs += branchCtx
      val (restShape, restCtx) = prop(rest, mergeBranches(ctx, branchCtxs.toList))
      (mkUnion(branchShapes.toList :+ restShape), restCtx)
    case Begin(sub, rest) =>
      val (subShape, subCtx) = prop(sub, ctx)
      val (restShape, restCtx) = prop(rest, subCtx)
      (mkUnion(subShape :: restShape :: Nil), restCtx)
    case TryBlock(sub, finallyDo, rest) =>
      val (subShape, _) = prop(sub, ctx)
      val (finallyShape, _) = prop(finallyDo, ctx)
      val (restShape, restCtx) = prop(rest, ctx)
      (mkUnion(subShape :: finallyShape :: restShape :: Nil), restCtx)
    case Label(_, _, body, rest) =>
      val (bodyShape, _) = prop(body, ctx)
      val (restShape, restCtx) = prop(rest, ctx)
      (mkUnion(bodyShape :: restShape :: Nil), restCtx)
    case Scoped(_, body) => prop(body, ctx)
    case Return(res) => (checkResult(res, ctx), ctx)
    case Throw(exc) => checkResult(exc, ctx); (BotShape, ctx)
    case _ => (BotShape, ctx)
end ShapeProp


class ClassTagsTransformer private (
  program: Program,
  taggedResultIds: Set[ResultId],
  escapingResultIds: Set[ResultId],
  matchedResultIds: Set[ResultId],
  unknownScrutineeMatchIds: Set[ResultId],
  argProducersByResultId: collection.Map[ResultId, Set[ResultId]],
  shapeByResultId: collection.Map[ResultId, Shape],
  funSymToFunDefn: collection.Map[TermSymbol, FunDefn],
  shapeTags: collection.Map[Shape, Int],
  patternShapesByCall: collection.Map[ResultId, List[Shape]],
  debug: Bool,
)(using Config, Erasure, State, Elaborator.Ctx, TL, Raise, FlowAnalysis.State) extends BlockTransformer(SymbolSubst.Id):
  import ClassTagsTransformer.classFields

  private val tagField = new syntax.Tree.Ident("__tag$")

  private enum ShapeMatchScope:
    case TopLevel, SupportedFunction, NestedFunction, ClassValue

  private def isShapeMatch(path: Path): Bool =
    ClassTagsTransformer.isShapeMatch(path)

  private def rejectUnsupportedShapeMatches(program: Program): Unit =
    class Checker(val scope: ShapeMatchScope) extends BlockTraverser:
      override def applyResult(result: Result): Unit =
        result match
          case call @ Call(fun, _) if isShapeMatch(fun) =>
            val errorMessage = scope match
              case ShapeMatchScope.TopLevel =>
                S(msg"shape.match is not supported at the top level.")
              case ShapeMatchScope.NestedFunction =>
                S(msg"shape.match is not supported in nested functions.")
              case ShapeMatchScope.ClassValue =>
                S(msg"shape.match is not supported in class value initializers.")
              case ShapeMatchScope.SupportedFunction => N
            errorMessage.foreach: message =>
              summon[Raise].apply(ErrorReport(
                message -> call.toLoc :: Nil,
                source = Diagnostic.Source.Compilation,
              ))
          case _ => ()
        super.applyResult(result)

      override def applyFunDefn(fun: FunDefn): Unit =
        // Anonymous functions originate from lambdas and are lifted later.
        val functionScope =
          if !fun.sym.nameIsMeaningful then ShapeMatchScope.SupportedFunction
          else scope match
            case ShapeMatchScope.TopLevel => ShapeMatchScope.SupportedFunction
            case _ => ShapeMatchScope.NestedFunction
        new Checker(functionScope).applyBlock(fun.body)

      override def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
        defn.parentPath.foreach(applyPath)
        defn.methods.foreach: method =>
          new Checker(ShapeMatchScope.SupportedFunction).applyBlock(method.body)
        new Checker(ShapeMatchScope.ClassValue).applyBlock(defn.preCtor)
        new Checker(ShapeMatchScope.ClassValue).applyBlock(defn.ctor)
        defn.companion.foreach: companion =>
          companion.methods.foreach: method =>
            new Checker(ShapeMatchScope.SupportedFunction).applyBlock(method.body)
          new Checker(ShapeMatchScope.ClassValue).applyBlock(companion.ctor)

    new Checker(ShapeMatchScope.TopLevel).applyBlock(program.main)

  private lazy val taggedShapes: List[ClassShape -> Int] =
    val entries = shapeTags.toList.collect:
      case (shape: ClassShape, tag) => shape -> tag
    .sortBy(_._2)
    if debug then
      for (shape, tag) <- entries do
        summon[TL].emitDbg(s"class-tags transform-phase > allocated tag $tag for ${shape.show}")
    entries

  private lazy val tagOfShape: Map[Shape, Int] =
    taggedShapes.iterator.map((shape, tag) => (shape: Shape) -> tag).toMap

  private val candidatesByResultId = MutMap.empty[ResultId, List[ClassShape -> Int]]

  private def orderedCandidates(result: Result): List[ClassShape -> Int] =
    candidatesByResultId.getOrElseUpdate(result.uid, {
      val candidates = shapeByResultId.get(result.uid).toList.flatMap: shape =>
        val alternatives = shape.flattenWithin(Shape.flattenBudget) match
          case S(alternatives) => alternatives
          case N =>
            summon[Raise].apply(ErrorReport(
              msg"Flattening this shape would produce more than ${Shape.flattenBudget.toString} alternatives." -> result.toLoc :: Nil,
              source = Diagnostic.Source.Compilation,
            ))
            Nil
        alternatives.collect:
          case concrete: ClassShape => concrete
      .flatMap(shape => tagOfShape.get(shape).map(shape -> _)).distinct
      candidates.foldLeft(List.empty[ClassShape -> Int]): (acc, entry) =>
        val split = acc.span(other => !(entry._1 <= other._1))
        split._1 ++ (entry :: split._2)
    })

  private lazy val programDefinitions: collection.Map[ClassLikeSymbol, ClsLikeDefn] =
    val definitions = MutMap.empty[ClassLikeSymbol, ClsLikeDefn]
    val collector = new BlockTraverser:
      override def applyDefn(defn: Defn): Unit =
        defn match
          case defn: ClsLikeDefn => defn.isym match
            case cls: ClassSymbol => definitions(cls) = defn
            case obj: ModuleOrObjectSymbol if defn.k is syntax.Obj => definitions(obj) = defn
            case _ => ()
          case _ => ()
        super.applyDefn(defn)
    collector.applyProgram(program)
    definitions

  private object DuplicableCtor:
    private def unapplyTo(
      cls: ClassSymbol, path: Path, args: Ls[Arg], mut: Bool, annotations: Ls[Annot],
    ): Opt[(
      cls: ClassSymbol, clsPath: Path, args: Ls[Arg], mut: Bool, annotations: Ls[Annot],
    )] =
      programDefinitions.get(cls)
        .filter(defn => (defn.k is syntax.Cls)
          && defn.bufferable.isEmpty
          && defn.paramsOpt.isEmpty && (defn.auxParams.sizeIs == 1)
          && defn.auxParams.forall(_.restParam.isEmpty)
          && args.forall(_.spread.isEmpty)
          && args.sizeCompare(defn.auxParams.iterator.map(_.params.size).sum) === 0)
        .map(_ => (cls, path, args, mut, annotations))
    def unapply(result: Result): Opt[(
      cls: ClassSymbol, clsPath: Path, args: Ls[Arg], mut: Bool, annotations: Ls[Annot],
    )] = if escapingResultIds.contains(result.uid) then N else result match
      case inst @ Instantiate(mut, path @ MemberRefTo(cls: ClassSymbol, _), args :: Nil) =>
        unapplyTo(cls, path, args, mut, inst.metadata.annotations)
      case call @ Call(path @ MemberRefTo(ctor: ClassCtorSymbol, _), args :: Nil) =>
        unapplyTo(ctor.associatedCls, path, args, false, call.metadata.annotations)
      case _ => N

  private lazy val duplicates: Map[ClassSymbol, ClsLikeDefn] =
    val needed = MutLinkedHashSet.empty[ClassSymbol]
    val collector = new BlockTraverser:
      override def applyResult(result: Result): Unit =
        result match
          case DuplicableCtor(cls, _, _, _, _)
            if taggedResultIds.contains(result.uid) && orderedCandidates(result).nonEmpty => needed += cls
          case _ => () // TODO: raise an error?
        super.applyResult(result)
    collector.applyProgram(program)
    needed.iterator.map(cls => cls -> mkDuplicate(cls, programDefinitions(cls))).toMap

  private def mkDuplicate(cls: ClassSymbol, defn: ClsLikeDefn): ClsLikeDefn =
    val nme = s"${defn.sym.nme}__Tagged"
    val sym = new BlockMemberSymbol(nme, Nil, nameIsMeaningful = false)
    val isym = ClassSymbol(
      syntax.Tree.DummyTypeDef(syntax.Cls), new syntax.Tree.Ident(nme))
    val ctorSym = ClassCtorSymbol(syntax.Fun, defn.owner, isym)
    val forwarded = defn.auxParams.flatMap(_.params).map: param =>
      Param(param.flags, VarSymbol(param.sym.id, param.sym.erasedType), N, param.modulefulness)(param.toLoc)
    val tagParam = Param(
      FldFlags.empty.copy(isVal = true),
      VarSymbol(tagField, S(ErasedType.Int)),
      N,
      Modulefulness.none,
    )(N)
    tagParam.sym.decl = S(tagParam)

    val (tagPublicField, defineTag) = mkTagField(isym, tagParam.sym.asSimpleRef)
    val superCall = Call(
      State.builtinOpsMap("super").asSimpleRef,
      forwarded.map(_.sym.asSimpleRef.asArg) ne_:: Nil,
    )(CallMetadata.mlsFunWithEffect, N)

    def withTag(ps: ParamList): ParamList = ps.copy(params = ps.params :+ tagParam)(ps.toLoc)
    def withTagLast(auxParams: Ls[ParamList]): Ls[ParamList] =
      if auxParams.isEmpty then Nil else auxParams.init :+ withTag(auxParams.last)
    cls.defn.map:
      case d: ClassDef.Parameterized => d.copy(
        sym = isym, bsym = sym, ctorSym = S(ctorSym), companion = N,
        params = if d.auxParams.isEmpty then withTag(d.params) else d.params,
        auxParams = withTagLast(d.auxParams),
      )(d.toLoc, d.headerLoc, d.ctorLoc)
      case d: ClassDef.Plain => d.copy(
        sym = isym, bsym = sym, ctorSym = S(ctorSym), companion = N,
        auxParams = withTagLast(d.auxParams),
      )(d.toLoc, d.headerLoc, d.ctorLoc)
    .foreach(d => isym.defn = S(d))

    val termCompanion = defn.termCompanion.map(_ => ctorSym)
    sym.tsym = termCompanion
    val parentPath = defn.owner match
      case S(owner) =>
        Select(owner.asThis, new syntax.Tree.Ident(defn.sym.nme))(S(cls), N)(false)
      case N => defn.sym.asMemberRef(cls)
    ClsLikeDefn(
      owner = defn.owner,
      isym = isym,
      sym = sym,
      ctorSym = S(ctorSym),
      k = syntax.Cls,
      paramsOpt = N,
      auxParams = PlainParamList(forwarded :+ tagParam)(N) :: Nil,
      parentPath = S(parentPath),
      methods = Nil,
      privateFields = Nil,
      publicFields = tagPublicField :: Nil,
      preCtor = Assign(NoSymbol, superCall, End()),
      ctor = defineTag(End()),
      companion = N,
      bufferable = N,
      termCompanion = termCompanion,
    )(N, Nil)

  private def mkDuplicatedCtor(result: Result, tag: Path): Opt[Result] = result match
    case DuplicableCtor(cls, clsPath, args, mut, annotations) =>
      duplicates.get(cls).flatMap: duplicate =>
        (clsPath, duplicate.owner) match
          case (sel: Select, _) => S(Select(
            sel.qual, new syntax.Tree.Ident(duplicate.sym.nme),
          )(S(duplicate.isym), clsPath.toLoc)(sel.sanitize))
          case (_: Value.MemberRef, N) =>
            S(duplicate.sym.asMemberRef(duplicate.isym).withLocOf(clsPath))
          case _ => N
      .map: path =>
        Instantiate(mut, path, (args :+ tag.asArg) :: Nil)(
          InstantiateMetadata(annotations), result.toLoc)
    case _ => N // TODO: raise an error?

  private def bindResult(result: Result)(k: Path => Block): Block = result match
    case path: Path => k(path)
    case result =>
      val symbol = new TempSymbol(N, erasedType = result.erasedValueType, "tmp")
      val reference = symbol.asSimpleRef.withLocOf(result)
      Scoped(Set.single(symbol), Assign(symbol, result, k(reference)))

  private def mkTagValue(tag: Int): Path = Value.Lit(syntax.Tree.IntLit(tag))(N)

  private def mkTagField(
    owner: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, value: Path,
  ): (BlockMemberSymbol -> TermSymbol, Block => Block) =
    val tagMember = new BlockMemberSymbol(tagField.name, Nil, nameIsMeaningful = false)
    val tagTerm = TermSymbol(syntax.ImmutVal, S(owner), tagField, erasedType = S(ErasedType.Int))
    (tagMember -> tagTerm, rest => Define(ValDefn(tagTerm, tagMember, value)(N, Nil), rest))

  private lazy val objectTags: Map[ModuleOrObjectSymbol, Int] =
    taggedResultIds.iterator.flatMap: resultId =>
      resultId.getResult match
        case ref @ MemberRefTo(obj: ModuleOrObjectSymbol, _) if programDefinitions.contains(obj) =>
          orderedCandidates(ref) match
            case Nil => N
            case (_, tag) :: rest =>
              softAssert(rest.isEmpty, s"an object has a single shape, but ${obj.nme} has several")
              S(obj -> tag)
        case _ => N
    .toMap

  private def withObjectTag(defn: ClsLikeDefn): ClsLikeDefn = defn.isym match
    case obj: ModuleOrObjectSymbol => objectTags.get(obj) match
      case S(tag) =>
        val (tagPublicField, defineTag) = mkTagField(obj, mkTagValue(tag))
        defn.copy(
          publicFields = defn.publicFields :+ tagPublicField,
          ctor = defineTag(defn.ctor),
        )(defn.configOverride, defn.annotations)
      case N => defn
    case _ => defn

  /** Reports the mutable (`mut val`) parameters of the classes some tagged construction
    * builds, once per class. A tag records the shape of a construction's arguments as
    * they are passed, so it goes stale as soon as one of those fields is reassigned --
    * including by the class's own constructor, which runs before the instance is ever
    * seen: `class Altered(mut val x) with set x = new B(0)` built as
    * `new Altered(new A(0))` would be tagged `Altered(A(..))` while holding a `B`, and a
    * `shape.match` would silently take the `A` branch. The error is what prevents that:
    * the constructions are still rewritten, but a program with an error is not run. */
  private def rejectMutableFields(): Unit =
    val classes = taggedResultIds.iterator.flatMap: resultId =>
      val result = resultId.getResult
      result match
        case CtorProducer(cls: ClassSymbol, _, _) if orderedCandidates(result).nonEmpty => S(cls)
        case _ => N
    .toList.distinct
    for cls <- classes; field <- cls.classFields.getOrElse(Nil) if field.k is syntax.MutVal do
      summon[Raise].apply(ErrorReport(
        msg"Class tags do not support mutable fields yet." -> field.toLoc :: Nil,
        source = Diagnostic.Source.Compilation,
      ))

  private lazy val tagReadResultIds: Set[ResultId] =
    matchedResultIds ++ argProducersByResultId.iterator.flatMap: (outer, inner) =>
      if orderedCandidates(outer.getResult).sizeCompare(1) > 0 then inner else Nil

  // A construction that needs a tag but can be neither replaced by a tagged copy nor
  // refer to a tagged object definition.
  private def leaveUntagged(result: Result, ctor: CtorCls)(k: Result => Block): Block =
    if tagReadResultIds.contains(result.uid) then
      val reason = ctor match
        case _ if escapingResultIds.contains(result.uid) =>
          msg"The constructed value can flow to code outside this module, which must not see a tagged copy of its class."
        case obj: ModuleOrObjectSymbol =>
          msg"The object ${obj.nme} is defined in another compilation unit, so its definition cannot be given a tag field."
        case cls: ClassSymbol if !programDefinitions.contains(cls) =>
          msg"The class ${cls.nme} is defined in another compilation unit, so no tagged copy of it can be defined here."
        case _ =>
          msg"Its class cannot be copied to carry a tag."
      summon[Raise].apply(ErrorReport(
        msg"This construction needs a class tag, but the tag cannot be attached to it." -> result.toLoc ::
        reason -> N :: Nil,
        source = Diagnostic.Source.Compilation,
      ))
    k(result)

  private def mkEquals(left: Path, right: Path)(k: Path => Block): Block =
    bindResult(Call(State.builtinOpsMap("===").asSimpleRef,
      (left.asArg :: right.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun, N))(k)

  private def mkAnd(left: Path, right: Path)(k: Path => Block): Block =
    bindResult(Call(State.builtinOpsMap("&&").asSimpleRef,
      (left.asArg :: right.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun, N))(k)

  private def mkShapeCheck(argument: Path, shape: Shape)(k: Path => Block): Block =
    tagOfShape.get(shape) match
      case S(tag) => mkEquals(
        Select(argument, tagField)(N, argument.toLoc)(false),
        mkTagValue(tag),
      )(k)
      case N => shape match
        case LitShape(lit) => mkEquals(argument, lit)(k)
        case TupleShape(length, _) =>
          val isTuple = new TempSymbol(N, erasedType = S(ErasedType.Bool), "isTuple")
          def set(value: Bool): Block = Assign(isTuple, Value.Lit(syntax.Tree.BoolLit(value))(N), End())
          Scoped(Set.single(isTuple), new Match(
            argument,
            Case.Tup(length, false) -> set(true) :: Nil,
            S(set(false)),
            k(isTuple.asSimpleRef),
          ))
        case _ => k(Value.Lit(syntax.Tree.BoolLit(true))(N))

  private def mkChecks(checks: List[Path -> Shape], acc: Opt[Path])(k: Path => Block): Block =
    checks match
      case Nil => k(acc.getOrElse(Value.Lit(syntax.Tree.BoolLit(true))(N)))
      case (argument, shape) :: rest =>
        mkShapeCheck(argument, shape): condition =>
          acc match
            case N => mkChecks(rest, S(condition))(k)
            case S(previous) =>
              mkAnd(previous, condition): combined =>
                mkChecks(rest, S(combined))(k)

  private def mkLeafChecks(
    argument: Path, expected: Shape, waitlist: IndexedSeq[Shape],
  ): List[(Path, Shape, IndexedSeq[Shape])] = expected match
    case DynamicShape => Nil
    case TupleShape(_, elements) =>
      (argument, expected, waitlist) :: elements.zipWithIndex.flatMap: (element, index) =>
        val elementPath = DynSelect(argument, Value.Lit(syntax.Tree.IntLit(index))(N), true)(argument.toLoc)
        val elementWaitlist = waitlist.map:
          case TupleShape(_, otherElements) => otherElements.lift(index).getOrElse(DynamicShape)
          case _ => DynamicShape
        mkLeafChecks(elementPath, element, elementWaitlist)
    case _ => (argument, expected, waitlist) :: Nil

  private def testExcludes(expected: Shape, actual: Shape): Bool =
    if expected === actual then false
    else tagOfShape.get(expected) match
      // * the check is `argument.__tag$ === tag`, which any other tagged shape fails
      case S(tag) => tagOfShape.get(actual).exists(_ =/= tag)
      case N => (expected, actual) match
        // * the check is `argument === lit`
        case (LitShape(left), LitShape(right)) => left =/= right
        case (TupleShape(left, _), TupleShape(right, _)) => left =/= right
        case _ => false

  private def mkDiscriminatingChecks(
    arguments: List[TermSymbol -> Path], shape: ClassShape, waitlist: List[ClassShape],
  ): List[Path -> Shape] =
    def fieldOf(candidate: ClassShape, field: TermSymbol): Shape =
      candidate.fields.getOrElse(field, DynamicShape)
    val leaves = arguments.flatMap: (field, argument) =>
      mkLeafChecks(argument, fieldOf(shape, field), waitlist.map(fieldOf(_, field)).toIndexedSeq)
    val chosen = ListBuffer.empty[Path -> Shape]
    var surviving = waitlist.indices.toSet
    for (argument, expected, others) <- leaves if surviving.nonEmpty do
      val excluded = surviving.filter(index => testExcludes(expected, others(index)))
      if excluded.nonEmpty then
        chosen += argument -> expected
        surviving --= excluded
    if surviving.isEmpty then chosen.toList
    else leaves.map((argument, expected, _) => argument -> expected)

  private def mkCandidateConditions(
    arguments: List[TermSymbol -> Path],
    candidates: List[ClassShape -> Int],
    acc: List[Opt[Path] -> Int],
  )(k: List[Opt[Path] -> Int] => Block): Block =
    candidates match
      case Nil => k(acc.reverse)
      case (_, tag) :: Nil => k((((N: Opt[Path]) -> tag) :: acc).reverse)
      case (shape, tag) :: remaining =>
        // * only the candidates still to come: the earlier ones have already been ruled
        // * out by their own failed conditions
        val checks = mkDiscriminatingChecks(arguments, shape, remaining.map(_._1))
        mkChecks(checks, N): condition =>
          mkCandidateConditions(arguments, remaining, (S(condition) -> tag) :: acc)(k)

  private def mkTagChoice(
    arguments: List[TermSymbol -> Path], candidates: List[ClassShape -> Int],
  )(chosen: Int => Block): Block =
    def choose(conditions: List[Opt[Path] -> Int]): Block = conditions match
      case Nil => End()
      case (N, tag) :: _ => chosen(tag)
      case (S(condition), tag) :: remaining =>
        new Match(
          condition,
          Case.Lit(syntax.Tree.BoolLit(true)) -> chosen(tag) :: Nil,
          if remaining.isEmpty then N else S(choose(remaining)),
          End(),
        )
    mkCandidateConditions(arguments, candidates, Nil)(choose)

  private def ctorArguments(
    candidates: List[ClassShape -> Int], args: Ls[Arg],
  ): List[TermSymbol -> Path] =
    candidates.head._1.ctor.classFields match
      case S(fields) if fields.size === args.size => fields.zip(args.map(_.value))
      case _ => Nil

  private def insertShapeTag(result: Result)(k: Result => Block): Block =
    result match
      case CtorProducer(ctor, args, _) =>
        val candidates = orderedCandidates(result)
        candidates match
          case Nil =>
            if debug then summon[TL].emitDbg(s"class-tags transform-phase > no tag for ${
              ClassTagsDebug.showCtor(ctor)}@${result.uid} of shape ${
              shapeByResultId.get(result.uid).fold("<unknown>")(_.show.take(160))}")
            k(result)
          case _ if ctor match
            case obj: ModuleOrObjectSymbol => objectTags.contains(obj)
            case _ => false
          => k(result)
          case (_, tag) :: Nil =>
            mkDuplicatedCtor(result, mkTagValue(tag)) match
              case S(construction) => k(construction)
              case N => leaveUntagged(result, ctor)(k)
          case _ =>
            val arguments = ctorArguments(candidates, args)
            val tagSymbol = new TempSymbol(N, erasedType = S(ErasedType.Int), "shapeTag")
            mkDuplicatedCtor(result, tagSymbol.asSimpleRef) match
              case S(construction) =>
                Scoped(Set.single(tagSymbol), Begin(
                  mkTagChoice(arguments, candidates): tag =>
                    Assign(tagSymbol, mkTagValue(tag), End()),
                  k(construction),
                ))
              case N => leaveUntagged(result, ctor)(k)
      case _ => k(result)

  override def applyProgram(program: Program): Program =
    if debug then
      summon[TL].emitDbg(">>> start class-tags transform-phase")
    rejectUnsupportedShapeMatches(program)
    rejectMutableFields()
    // * allocate every tag before any of them is looked up
    if tagOfShape.isEmpty && debug then
      summon[TL].emitDbg("class-tags transform-phase > no shapes to tag")
    if debug then
      for (cls, duplicate) <- duplicates do
        summon[TL].emitDbg(
          s"class-tags transform-phase > duplicated ${cls.nme} as ${duplicate.sym.nme}")
    val transformed = super.applyProgram(program)
    val unownedDuplicates: Set[ScopedSymbol] = duplicates.valuesIterator.collect:
      case duplicate if duplicate.owner.isEmpty => duplicate.sym
    .toSet
    val result =
      if unownedDuplicates.isEmpty then transformed
      else Program(transformed.imports, Scoped(unownedDuplicates, transformed.main))
    if debug then
      summon[TL].emitDbg("<<< end class-tags transform-phase")
    result

  override def applyBlock(block: Block): Block = block match
    case Define(defn: ClsLikeDefn, _) =>
      val duplicate = defn.isym match
        case cls: ClassSymbol => duplicates.get(cls)
        case _ => N
      val transformed = super.applyBlock(block) match
        case define @ Define(defn2: ClsLikeDefn, rest2) =>
          val tagged = withObjectTag(defn2)
          if tagged is defn2 then define else Define(tagged, rest2)
        case transformed => transformed
      (transformed, duplicate) match
        case (Define(defn2, rest2), S(duplicate)) => Define(defn2, Define(duplicate, rest2))
        case (_, S(_)) => ??? // TODO
        case _ => transformed
    case _ => super.applyBlock(block)

  override def applyFunDefn(fun: FunDefn): FunDefn =
    val transformer = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(block: Block): Block =
        block match
          case AssignField(lhs, _, _, _) =>
            summon[Raise].apply(ErrorReport(
              msg"Class tags do not support set operations yet." -> lhs.toLoc :: Nil,
              source = Diagnostic.Source.Compilation,
            ))
          case AssignDynField(lhs, _, _, _, _) =>
            summon[Raise].apply(ErrorReport(
              msg"Class tags do not support set operations yet." -> lhs.toLoc :: Nil,
              source = Diagnostic.Source.Compilation,
            ))
          case _ => ()
        super.applyBlock(block)

      // * get the branch body defined as a FunDefn
      private def getBranch(path: Path): Opt[FunDefn] =
        path.targetSymbol.collect:
          case symbol: TermSymbol => symbol
        .flatMap(funSymToFunDefn.get)

      // * Generate branch based on the branch function
      private def mkBranch(branch: FunDefn, resultSymbol: TempSymbol): Block =
        SymbolRefresher(Map.empty).apply(applyFunBodyLikeBlock(branch.body)).mapReturn:
          case Return(result) => Assign(resultSymbol, result, End())

      private def rewriteShapeMatch(call: Call, scrutinee: Path, branchArgs: List[Arg])(k: Result => Block): Opt[Block] =
        val annotation = call.metadata.annotations.collectFirst:
          case Annot.MatchShapes(patterns) => patterns
        if annotation.isEmpty then
          summon[Raise].apply(ErrorReport(
            msg"shape.match must be annotated with @matchShapes." -> call.toLoc :: Nil,
            source = Diagnostic.Source.Compilation,
          ))
        annotation.flatMap: patterns =>
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
            val namedBranches = branchArgs.zip(branchDefns).collect:
              case (arg, branch) if branch.sym.nameIsMeaningful => arg.value
            if namedBranches.nonEmpty then
              summon[Raise].apply(ErrorReport(
                msg"Annotated shape.match branches must be anonymous functions." -> call.toLoc ::
                namedBranches.map: branch =>
                  msg"This branch is a named function." -> branch.toLoc,
                source = Diagnostic.Source.Compilation,
              ))
              N
            else
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
                val patternShapes = patternShapesByCall.getOrElse(call.uid, Nil)
                val claimed = MutSet.empty[Int]
                val branchTags = patternShapes.map: patternShape =>
                  val tags = taggedShapes.collect:
                    case (shape, tag) if !claimed.contains(tag) && shape <= patternShape => tag
                  claimed ++= tags
                  tags
                if debug then
                  val shown = patternShapes.zip(branchTags).map: entry =>
                    val tags = if entry._2.isEmpty then "<none>" else entry._2.mkString("|")
                    s"${entry._1.show}->$tags"
                  summon[TL].emitDbg(
                    s"class-tags transform-phase > match shapes ${shown.mkString(", ")}")
                if patternShapes.exists(_.containsUnion) then
                  softAssert(false, "@matchShapes patterns must not contain union shapes.")
                  N
                else if unknownScrutineeMatchIds.contains(call.uid) then
                  summon[Raise].apply(ErrorReport(
                    msg"The scrutinee of this shape.match may be a value built outside this module, which carries no class tag." -> call.toLoc ::
                    msg"Only values constructed in this module can be dispatched on by their class tags." -> scrutinee.toLoc :: Nil,
                    source = Diagnostic.Source.Compilation,
                  ))
                  N
                else if branchTags.forall(_.isEmpty) then
                  summon[Raise].apply(ErrorReport(
                    msg"Annotated shape.match has no tagged class shapes for its scrutinee." -> call.toLoc :: Nil,
                    source = Diagnostic.Source.Compilation,
                  ))
                  N
                else
                  val resultSymbol = new TempSymbol(N, erasedType = call.erasedValueType, "shapeMatchResult")
                  val resultRef = resultSymbol.asSimpleRef.withLocOf(call)
                  val tagAccess = Select(scrutinee, tagField)(N, scrutinee.toLoc)(false)
                  S(Scoped(Set.single(resultSymbol),
                    bindResult(tagAccess): tag =>
                      mkTagDispatch(tag, branchTags.zip(branchDefns), resultSymbol, k(resultRef))))

      private def mkTagDispatch(
        tag: Path, branches: List[(List[Int], FunDefn)], resultSymbol: TempSymbol, rest: Block,
      ): Block =
        val reachable = branches.zipWithIndex.filter(_._1._1.nonEmpty)
        val index = new TempSymbol(N, erasedType = S(ErasedType.Int), "shapeMatchBranch")
        val indexRef = index.asSimpleRef
        val arms = reachable.flatMap: entry =>
          entry._1._1.map: expected =>
            Case.Lit(syntax.Tree.IntLit(expected)) ->
              (Assign(index, Value.Lit(syntax.Tree.IntLit(entry._2))(N), End()): Block)
        val bodies = reachable.foldRight(
          Throw.error("Unhandled shape tag in shape.match"): Block
        ): (entry, otherwise) =>
          new Match(
            indexRef,
            Case.Lit(syntax.Tree.IntLit(entry._2)) -> mkBranch(entry._1._2, resultSymbol) :: Nil,
            S(otherwise),
            rest,
          )
        Scoped(Set.single(index), Begin(
          new Match(tag, arms, S(Assign(index, Value.Lit(syntax.Tree.IntLit(-1))(N), End())), End()),
          bodies))

      override def applyResult(result: Result)(k: Result => Block): Block =
        result match
          case call @ Call(fun, (Arg(N, scrutinee) :: branches) :: Nil) if branches.nonEmpty && isShapeMatch(fun) =>
            // Rewrite annotated shape.match calls
            rewriteShapeMatch(call, scrutinee, branches)(k).getOrElse:
              super.applyResult(result)(k)
          case CtorProducer(_, _, _) =>
            // Insert tags for instantiations
            if taggedResultIds.contains(result.uid) then
              super.applyResult(result): transformed =>
                insertShapeTag(transformed)(k)
            else
              super.applyResult(result)(k)
          case _ => super.applyResult(result)(k)
    val body = transformer.applyFunBodyLikeBlock(fun.body)
    val transformed =
      if body is fun.body then fun
      else FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, body)(fun.configOverride, fun.annotations)
    super.applyFunDefn(transformed)
end ClassTagsTransformer


object ClassTagsTransformer:
  private type WebProducer = ProdStrat | WebEntryCollector.EntryPoints
  private type WebConsumer = ConcreteCtorConsumer | ProdStrat | WebEntryCollector.EntryPoints

  def isShapeMatch(path: Path)(using ctx: Elaborator.Ctx): Bool =
    path.targetSymbol.flatMap(_.asBlkMember).contains(ctx.builtins.shape.`match`)

  private def getShapeMatchCalls(program: Program)(using Elaborator.Ctx): List[Call] =
    val calls = ListBuffer.empty[Call]
    val collector = new BlockTraverser:
      override def applyResult(result: Result): Unit =
        result match
          case call: Call if isShapeMatch(call.fun) => calls += call
          case _ => ()
        super.applyResult(result)
    collector.applyProgram(program)
    calls.toList

  private def mkWeb(
    entries: WebEntryCollector.EntryPoints,
    entriesByProducer: Map[Ctor, List[WebEntryCollector.EntryPoints]],
    entriesByConsumer: Map[ConcreteCtorConsumer, List[WebEntryCollector.EntryPoints]],
  ): Web =
    val result = FlowWebComputation[WebProducer, WebConsumer](
      producer => producer match
        case ctor: Ctor =>
          val consumers = ctor.dests.iterator.collect:
            case consumer: ConcreteCtorConsumer => consumer: WebConsumer
          consumers
            ++ ctor.args.iterator.map(arg => arg._2: WebConsumer)
            ++ entriesByProducer.getOrElse(ctor, Nil) // also connect other entries in the same function to the current web
        case variable: StratVar =>
          variable.lowerBounds.iterator.map(producer => producer: WebConsumer)
        case entries: WebEntryCollector.EntryPoints =>
          entries.producers.iterator.map(producer => producer: WebConsumer)
            ++ entries.consumers
        case _ => Nil,
      consumer => consumer match
        case consumer: ConcreteCtorConsumer =>
          consumer.srcs.iterator.map(producer => producer: WebProducer)
            ++ entriesByConsumer.getOrElse(consumer, Nil) // also connect other entries in the same function to the current web
        case variable: StratVar =>
          variable.lowerBounds.iterator.map(producer => producer: WebProducer)
        case producer: ProdStrat => (producer: WebProducer) :: Nil
        case entries: WebEntryCollector.EntryPoints => (entries: WebProducer) :: Nil,
      entries.producers,
      entries.consumers,
    )
    FlowWebComputation.Result[Ctor, ConcreteCtorConsumer](
      result.markedProducers.collect:
        case ctor: Ctor => ctor,
      result.markedConsumers.collect:
        case consumer: ConcreteCtorConsumer => consumer,
    )

  private def mkWebs(
    entryPoints: List[WebEntryCollector.EntryPoints],
    matchConsumers: List[ConcreteCtorConsumer],
  ): List[Web] =
    val entriesByProducer = entryPoints.iterator
      .flatMap(entries => entries.producers.map(_ -> entries))
      .toList.groupMap(_._1)(_._2)
    val entriesByConsumer = entryPoints.iterator
      .flatMap(entries => entries.consumers.map(_ -> entries))
      .toList.groupMap(_._1)(_._2)
    if matchConsumers.isEmpty then Nil
    else
      val seeds = WebEntryCollector.EntryPoints(Nil, matchConsumers)
      mkWeb(seeds, entriesByProducer, entriesByConsumer) :: Nil

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

  extension (cls: ClassLikeSymbol) def classFields: Opt[List[TermSymbol]] = cls match
    case cls: ClassSymbol => cls.tree.clsParams match
      case fields :: Nil => S(fields)
      case Nil => S(Nil)
      case _ => N
    case _: ModuleOrObjectSymbol => S(Nil)

  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    eState: State,
    ctx: Elaborator.Ctx,
    symbolPrinter: SymbolPrinter,
    erasure: Erasure,
  ): Program =
    cfg.classTags match
      case N => p
      case S(dCfg) =>
        val matchCalls = getShapeMatchCalls(p)
        val flowCfg = Config.FlowAnalysisConfig(
          debug = false,
          mono = true,
          trackNonAffine = false,
          trackAccumulator = false,
          logNonAffine = false,
          logAccumulator = false,
        )
        val flowAnalysisRes =
          FlowAnalysis.mkTraceLogger(flowCfg, "class-tags flow-analysis-phase > ", tl).givenIn:
            FlowAnalysis(p, mono = true, nonAffineTracking = false, accumulatorTracking = false)
        given fState: FlowAnalysis.State = flowAnalysisRes.fState
        val matchResultIds = matchCalls.iterator.map(_.uid).toSet
        val collectorTl = new TraceLogger(using tl.debugPrinter):
          override def doTrace: Bool = dCfg.debug
          override def emitDbg(str: Str): Unit =
            tl.emitDbg(s"class-tags collection-phase > $str")
        val entryPoints = collectorTl.givenIn:
          if dCfg.debug then tl.emitDbg(">>> start class-tags collection-phase")
          val result = WebEntryCollector(p, flowAnalysisRes)
          if dCfg.debug then tl.emitDbg("<<< end class-tags collection-phase")
          result
        val matchConsumers = flowAnalysisRes.consumersWithSrcs.iterator.collect:
          case patternMatch: Dtor if matchResultIds.contains(patternMatch.exprId) => patternMatch
        .toList.distinct
        val webs = mkWebs(entryPoints, matchConsumers)
        if dCfg.debug then logWebs(webs)
        val taggedResultIds = webs.iterator
          .flatMap(_.markedProducers.iterator)
          .map(_.exprId).toSet
        val escapingResultIds = webs.iterator
          .flatMap(_.markedProducers.iterator)
          .filter(_.dests.contains(UnknownCons))
          .map(_.exprId).toSet
        val matchedResultIds = matchConsumers.iterator.flatMap(_.srcs).collect:
          case ctor: Ctor => ctor.exprId
        .toSet
        val unknownScrutineeMatchIds = matchConsumers.iterator
          .filter(_.srcs.contains(UnknownProd))
          .map(_.exprId).toSet
        def concreteProducers(producer: ProdStrat, seen: Set[ProdStrat]): Iterator[Ctor] =
          if seen.contains(producer) then Iterator.empty
          else producer match
            case ctor: Ctor => Iterator.single(ctor)
            case variable: StratVar =>
              variable.lowerBounds.iterator.flatMap(concreteProducers(_, seen + variable))
            case _ => Iterator.empty
        val argProducersByResultId = webs.iterator
          .flatMap(_.markedProducers.iterator)
          .map: ctor =>
            ctor.exprId -> ctor.args.iterator
              .flatMap((_, arg) => concreteProducers(arg, Set.empty)).map(_.exprId).toSet
          .toList.groupMapReduce(_._1)(_._2)(_ ++ _)
        val funSymToFunDefn = flowAnalysisRes.preAnalyzer.res.funSymToFunDefn
        val patternShapesByCall = matchCalls.iterator.flatMap: call =>
          call.metadata.annotations.collectFirst:
            case Annot.MatchShapes(patterns) => call.uid -> patterns.map(Shape.mkShapeByPattern)
        .toMap
        val shapeProp = new ShapeProp(funSymToFunDefn, patternShapesByCall)
        shapeProp.applyProgram(p)
        new ClassTagsTransformer(
          p,
          taggedResultIds,
          escapingResultIds,
          matchedResultIds,
          unknownScrutineeMatchIds,
          argProducersByResultId,
          shapeProp.shapeByResultId,
          funSymToFunDefn,
          shapeProp.shapeTags,
          patternShapesByCall,
          dCfg.debug,
        ).applyProgram(p)
