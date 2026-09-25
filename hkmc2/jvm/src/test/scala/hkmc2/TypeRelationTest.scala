package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable.ArrayBuffer
import hkmc2.syntax.{Fun, Tree}
import hkmc2.utils.*, shorthands.*


class TypeRelationTest extends AnyFunSuite:
  private class Harness:
    import io.PlatformPath.given
    given owner: Elaborator.State = new Elaborator.State
    given state: NewResolverState = owner.newResolverState
    given Raise = diagnostic => fail(diagnostic.theMsg)
    given DebugPrinter = new DebugPrinter
    given trace: TraceLogger = new TraceLogger:
      override def doTrace: Boolean = false
    given Config = Config.default(TestFolders.mainTestDir(os.pwd))
    given CompilerCtx = CompilerCtx.fresh(io.FileSystem.default, TestFolders.compilerPaths(os.pwd), summon[Config])
    val resolver = Elaborator(trace, TestFolders.mainTestDir(os.pwd), Elaborator.Ctx.empty)
    def tpe(shape: TypeShape): DeclaredType =
      val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      resolution.publish(shape)
      DeclaredType(resolution, Map.empty, Map.empty, true)
    def parameter(name: String): (VarSymbol, DeclaredType) =
      val symbol = VarSymbol(Tree.Ident(name))
      (symbol, tpe(TypeShape.Parameter(symbol, symbol.inferenceHost)))
    def observe(reference: ContextualType): ArrayBuffer[TermShape] =
      val values = ArrayBuffer.empty[TermShape]
      InstanceShape(reference.tpe).exit(reference.marks) match
        case value: TermShape => resolver.listenInstanceViews(value)(values += _)
        case NoShape => fail("A type reference cannot be unreachable")
      values

  test("symbolic cycles retain early and late bounds without adding listeners on replay"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val ar = ContextualType(at, Nil)
    val br = ContextualType(bt, Nil)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.resolver.publishParameter(a, first)
    h.resolver.constrainTypes(ar, br)
    h.resolver.constrainTypes(br, ar)
    val seen = h.observe(br)
    h.resolver.publishParameter(a, second)
    assert(seen.toSet == Set(first, second))
    val counts = (a.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ar, br)
      h.resolver.constrainTypes(br, ar)
      h.resolver.publishParameter(a, first)
    assert((a.inferenceHost.listeners.size, b.inferenceHost.listeners.size) == counts)
    assert(seen.toList == List(first, second))

  test("reference exit and reentry agree with value transport for wildcard and explicit sites"):
    // Check both publication orders and every combination of wildcard/explicit
    // exit, reentry, and consumer sites against the ordinary value operations.
    for exitSite <- 0 to 2; entrySite <- 0 to 2; consumerSite <- 0 to 2 do
      val h = new Harness
      import h.given
      val (a, at) = h.parameter("A")
      val owner = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("owner")))
      val sites = Vector(N, S(FlowSymbol.app()), S(FlowSymbol.app()))
      val exit = ExitMark(owner, sites(exitSite), NoMarks)
      val entry = EntryMark(owner, sites(entrySite), NoMarks)
      val consumer = ExitMark(owner, sites(consumerSite), NoMarks)
      val first = MarkedShape.enter(IntroShape(Term.UnitVal(), N), owner, sites(1))
      val second = MarkedShape.enter(DynShape(), owner, sites(2))
      val outside = h.resolver.transportType(at, exit :: Nil)
      val inside = h.resolver.transportType(outside, entry :: Nil)
      h.resolver.publishParameter(a, first)
      val observed = h.observe(ContextualType(inside, Nil))
      def expected(values: List[TermShape], path: List[Marks]): Set[TermShape] =
        values.flatMap: value =>
          value.exit(path) match
            case shape: TermShape => Some(shape)
            case NoShape => None
        .toSet
      assert(observed.toSet == expected(List(first), List(exit, entry)))
      h.resolver.publishParameter(a, second)
      assert(observed.toSet == expected(List(first, second), List(exit, entry)))
      val consumed = h.resolver.transportType(inside, consumer :: Nil)
      assert(h.observe(ContextualType(consumed, Nil)).toSet ==
        expected(List(first, second), List(exit, entry, consumer)))

  test("alias argument normalization reaches a fixed point without changing its marks"):
    val h = new Harness
    import h.given
    val (formal, ft) = h.parameter("X")
    val symbol = TypeAliasSymbol(Tree.Ident("Identity"))
    val member = BlockMemberSymbol("Identity", Nil)
    symbol.defn = S(TypeDef(symbol, member, List(TyParam(FldFlags.empty, N, formal)),
      S(ft.resolution.source), N, Nil))
    val alias = h.tpe(TypeShape.Alias(symbol, S(ft.resolution)))
    val (argument, at) = h.parameter("A")
    val application = h.tpe(TypeShape.Applied(alias.resolution, List(at.resolution)))
    val (target, tt) = h.parameter("Target")
    val owner = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("owner")))
    val path = EntryMark(owner, S(FlowSymbol.app()), NoMarks)
    val original = h.resolver.transportType(tt, path :: Nil)
    val seen = h.observe(ContextualType(original, Nil))
    val before = target.inferenceHost.listeners.size
    var current = original
    (1 to 1000).foreach: _ =>
      current = h.resolver.declaredType(application.resolution, Map(argument -> current))
      assert(current == original)
    val value = DynShape()
    h.resolver.publishParameter(target, value)
    assert(seen.toList == List(MarkedShape.enter(value, owner, path.id)))
    assert(target.inferenceHost.listeners.size == before)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("partial captured alias reduction uses ordinary exit and entry including caller identity loss"):
    val h = new Harness
    import h.given
    val (formal, ft) = h.parameter("X")
    val (unused, _) = h.parameter("Unused")
    val symbol = TypeAliasSymbol(Tree.Ident("Identity"))
    val member = BlockMemberSymbol("Identity", Nil)
    symbol.defn = S(TypeDef(symbol, member, List(TyParam(FldFlags.empty, N, formal), TyParam(FldFlags.empty, N, unused)),
      S(ft.resolution.source), N, Nil))
    val alias = h.tpe(TypeShape.Alias(symbol, S(ft.resolution)))
    val scope = TermSymbol(Fun, N, Tree.Ident("owner"))
    val owner = ResolutionBoundary(scope)
    val captured = h.tpe(TypeShape.Captured(alias.resolution, scope))
    val (argument, at) = h.parameter("A")
    val application = h.tpe(TypeShape.Applied(captured.resolution, List(at.resolution)))
    val (target, tt) = h.parameter("Target")
    val original = h.resolver.transportType(tt, EntryMark(owner, S(FlowSymbol.app()), NoMarks) :: Nil)
    val outside = h.resolver.transportType(original, ExitMark(owner, N, NoMarks) :: Nil)
    val expected = h.resolver.transportType(outside, EntryMark(owner, N, NoMarks) :: Nil)
    assert(expected != original)
    val actual = h.resolver.declaredType(application.resolution, Map(argument -> original))
    assert(actual == expected)
    val early = IntroShape(Term.UnitVal(), N)
    val late = DynShape()
    h.resolver.publishParameter(target, early)
    val seen = h.observe(ContextualType(actual, Nil))
    h.resolver.publishParameter(target, late)
    assert(seen.toList == List(early, late).map(MarkedShape.enter(_, owner, N)))
    val count = target.inferenceHost.listeners.size
    (1 to 1000).foreach: _ =>
      assert(h.resolver.declaredType(application.resolution, Map(argument -> actual)) == expected)
    assert(target.inferenceHost.listeners.size == count)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("wildcard normalization bounds recursive environments while retaining late marked bounds"):
    // Unlike a finite number of source projections, this measures saturation of
    // the saved argument graph and its listeners under repeated substitution.
    for input <- List(false, true); output <- List(false, true) do
      val h = new Harness
      import h.given
      val (formal, ft) = h.parameter("A")
      val (target, tt) = h.parameter("Target")
      val scope = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("owner")))
      val site = S(FlowSymbol.app())
      val original = h.resolver.transportType(tt, EntryMark(scope, site, NoMarks) :: Nil)
      val wildcard = h.tpe(TypeShape.Wildcard(Option.when(input)(ft.resolution), Option.when(output)(ft.resolution)))
      val first = h.resolver.declaredType(wildcard.resolution, Map(formal -> original))
      val observed = h.observe(ContextualType(first, Nil))
      val inputObserved = h.observe(ContextualType(h.resolver.selectArgument(first, false), Nil))
      val before = target.inferenceHost.listeners.size
      var current = first
      (1 to 1000).foreach: _ =>
        current = h.resolver.declaredType(wildcard.resolution, Map(formal -> current))
        assert(current eq first)
      val value = DynShape()
      h.resolver.publishParameter(target, value)
      if output then assert(observed.toList == List(MarkedShape.enter(value, scope, site)))
      else assert(!observed.exists(_.applicationHead._1.isInstanceOf[DynShape]))
      if input then assert(inputObserved.toList == List(MarkedShape.enter(value, scope, site)))
      else assert(inputObserved.isEmpty)
      assert(target.inferenceHost.listeners.size == before)
      assert(h.state.allocatedTypeInstanceCount == 0)

  test("recursive Boolean arguments share a fixed point and preserve each atom's marks and late bounds"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val (target, tt) = h.parameter("Target")
    val owner = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("owner")))
    val path = EntryMark(owner, S(FlowSymbol.app()), NoMarks)
    val original = h.resolver.transportType(tt, path :: Nil)
    val source = h.tpe(TypeShape.Union(at.resolution, bt.resolution))
    val expected = h.resolver.declaredType(source.resolution, Map(a -> original))
    val early = IntroShape(Term.UnitVal(), N)
    val late = DynShape()
    h.resolver.publishParameter(target, early)
    val seen = h.observe(ContextualType(expected, Nil))
    val counts = (target.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    var current = expected
    (1 to 1000).foreach: _ =>
      current = h.resolver.declaredType(source.resolution, Map(a -> current))
      assert(current eq expected)
      h.resolver.listenInstanceViews(InstanceShape(current))(_ => ())
    h.resolver.publishParameter(b, late)
    assert(seen.toSet == Set(MarkedShape.enter(early, owner, path.id), late))
    assert((target.inferenceHost.listeners.size, b.inferenceHost.listeners.size) == counts)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("recursive structural projections preserve bounds and reuse their listeners"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    def recursiveRecord(element: DeclaredType): DeclaredType =
      val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      val value = Term.UnitVal()
      value.typeInterpretation = S(element.resolution)
      val next = Term.UnitVal()
      next.typeInterpretation = S(resolution)
      val valueField = RcdField.signature(Term.Lit(Tree.StrLit("value")), value)
      val nextField = RcdField.signature(Term.Lit(Tree.StrLit("next")), next)
      val source: Term.Rcd = Term.Rcd(false, List(valueField, nextField))
      resolution.publish(TypeShape.Record(source, List(valueField -> element.resolution, nextField -> resolution)))
      DeclaredType(resolution, Map.empty, Map.empty, true)
    val left = ContextualType(recursiveRecord(at), Nil)
    val right = ContextualType(recursiveRecord(bt), Nil)
    val first = IntroShape(Term.UnitVal(), N)
    val later = DynShape()
    h.resolver.publishParameter(a, first)
    h.resolver.constrainTypes(left, right)
    val seen = h.observe(ContextualType(bt, Nil))
    assert(seen.toList == List(first))
    def counts = List(left.tpe.resolution.inferenceHost.listeners.size, right.tpe.resolution.inferenceHost.listeners.size,
      a.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    val before = counts
    h.resolver.publishParameter(a, later)
    assert(seen.toList == List(first, later))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(left, right)
    assert(counts == before)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("forward type dependencies retain each observer's substitution until the target is known"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    val early = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val late = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    early.publish(TypeShape.Tuple(List(at.resolution, late)))
    val left = h.resolver.declaredType(early, Map(a -> h.tpe(TypeShape.Inferred(first))))
    val right = h.resolver.declaredType(early, Map(a -> h.tpe(TypeShape.Inferred(second))))
    val leftSeen = h.observe(ContextualType(left, Nil))
    val rightSeen = h.observe(ContextualType(right, Nil))
    assert(leftSeen.isEmpty && rightSeen.isEmpty)
    // Closing a recursive dependency must wake both observers without merging
    // their environments or allocating a parameter for the forward reference.
    late.publish(TypeShape.Tuple(List(at.resolution, early)))
    def firstField(values: ArrayBuffer[TermShape]): Set[TermShape] = values.toList match
      case (tuple: TupleShape) :: Nil => tuple.elements.head match
        case TupleShape.TypedField(tpe, marks) => h.observe(ContextualType(tpe, marks)).toSet
        case _ => fail("Expected a declared tuple field")
      case _ => fail("Expected one declared tuple")
    assert(firstField(leftSeen) == Set(first))
    assert(firstField(rightSeen) == Set(second))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ContextualType(left, Nil), ContextualType(right, Nil))
    val saturated = (early.inferenceHost.listeners.size, late.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ContextualType(left, Nil), ContextualType(right, Nil))
    assert((early.inferenceHost.listeners.size, late.inferenceHost.listeners.size) == saturated)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("delayed argument selection fixes one endpoint for both constraint directions"):
    val h = new Harness
    import h.given
    val (input, inputType) = h.parameter("Input")
    val (output, outputType) = h.parameter("Output")
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val argument = DeclaredType(resolution, Map.empty, Map.empty, true)
    val negative = h.resolver.selectArgument(argument, false)
    val positive = h.resolver.selectArgument(argument, true)
    val neg = ContextualType(negative, Nil)
    val pos = ContextualType(positive, Nil)
    val negativeValues = h.observe(neg)
    val positiveValues = h.observe(pos)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    val lower = ContextualType(h.tpe(TypeShape.Inferred(first)), Nil)
    h.resolver.constrainTypes(lower, neg)
    assert(negativeValues.isEmpty && positiveValues.isEmpty)
    resolution.publish(TypeShape.Argument(TypeArgument(inputType, outputType)))
    assert(negativeValues.toList == List(first))
    assert(positiveValues.isEmpty)
    h.resolver.publishParameter(output, second)
    assert(positiveValues.toList == List(second))
    val counts = (resolution.inferenceHost.listeners.size, input.inferenceHost.listeners.size, output.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      // Re-selecting an interpreted reference must not change its meaning or
      // allocate another node, even when the later use has opposite polarity.
      assert(h.resolver.selectArgument(argument, false) eq negative)
      assert(h.resolver.selectArgument(argument, true) eq positive)
      assert(h.resolver.selectArgument(negative, true) eq negative)
      assert(h.resolver.selectArgument(positive, false) eq positive)
      h.resolver.constrainTypes(lower, neg)
    assert((resolution.inferenceHost.listeners.size, input.inferenceHost.listeners.size, output.inferenceHost.listeners.size) == counts)
    assert(negativeValues.toList == List(first))
    assert(positiveValues.toList == List(second))
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("cyclic argument selections wait for productive bounds without expanding the cycle"):
    val h = new Harness
    import h.given
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val argument = DeclaredType(resolution, Map.empty, Map.empty, true)
    val selected = h.resolver.selectArgument(argument, true)
    val reference = ContextualType(selected, Nil)
    val seen = h.observe(reference)
    resolution.publish(TypeShape.Argument(TypeArgument(selected, selected)))
    assert(seen.isEmpty)
    val (parameter, bound) = h.parameter("Later")
    resolution.publish(TypeShape.Argument(TypeArgument(bound, bound)))
    val value = IntroShape(Term.UnitVal(), N)
    h.resolver.publishParameter(parameter, value)
    assert(seen.toList == List(value))
    h.resolver.constrainTypes(reference, reference)
    val counts = (resolution.inferenceHost.listeners.size, parameter.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(reference, reference)
      assert(h.resolver.selectArgument(argument, true) eq selected)
    assert((resolution.inferenceHost.listeners.size, parameter.inferenceHost.listeners.size) == counts)
    assert(seen.toList == List(value))
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("cyclic hole constraints saturate without allocating parameter instances"):
    val h = new Harness
    import h.given
    val (parameter, _) = h.parameter("T")
    val first = h.resolver.omittedType(h.tpe(TypeShape.Abstract).resolution, parameter)
    val second = h.resolver.omittedType(h.tpe(TypeShape.Abstract).resolution, parameter)
    val left = ContextualType(first, Nil)
    val right = ContextualType(second, Nil)
    h.resolver.constrainTypes(left, right)
    h.resolver.constrainTypes(right, left)
    val seen = h.observe(right)
    assert(seen.isEmpty)
    val bound = IntroShape(Term.UnitVal(), N)
    val input = ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil)
    h.resolver.constrainTypes(input, left)
    def listeners(tpe: DeclaredType): Int = tpe.resolution.currentShapes.toList match
      case TypeShape.Hole(host) :: Nil => host.listeners.size
      case _ => fail("An omitted argument must retain its inference host")
    val counts = (listeners(first), listeners(second))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(left, right)
      h.resolver.constrainTypes(right, left)
      h.resolver.constrainTypes(input, left)
    assert(seen.toList == List(bound))
    assert((listeners(first), listeners(second)) == counts)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("importers share hole identities while keeping inferred bounds private"):
    val h = new Harness
    import h.given
    val (parameter, _) = h.parameter("T")
    val source = h.tpe(TypeShape.Abstract).resolution
    val hole = h.resolver.omittedType(source, parameter)
    val output = new TermShapeHost
    h.resolver.listenInstanceViews(InstanceShape(hole))(output.publish)
    val exporter = ArrayBuffer.empty[TermShape]
    val detach = output.inferenceHost.observe(exporter += _)
    val left = new Elaborator.State().newResolverState.inGraph(h.state)
    val right = new Elaborator.State().newResolverState.inGraph(h.state)
    assert(h.resolver.omittedType(source, parameter)(using left) eq hole)
    assert(h.resolver.omittedType(source, parameter)(using right) eq hole)
    val leftValues = ArrayBuffer.empty[TermShape]
    val rightValues = ArrayBuffer.empty[TermShape]
    h.resolver.listenInstanceViews(InstanceShape(hole))(leftValues += _)(using left)
    h.resolver.listenInstanceViews(InstanceShape(hole))(rightValues += _)(using right)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(first)), Nil), ContextualType(hole, Nil))(using left)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(second)), Nil), ContextualType(hole, Nil))(using right)
    assert(leftValues.toList == List(first))
    assert(rightValues.toList == List(second))
    assert(exporter.isEmpty)
    assert(output.currentShapes.isEmpty)
    assert(h.state.allocatedTypeInstanceCount == 0)
    assert(left.allocatedTypeInstanceCount == 0)
    assert(right.allocatedTypeInstanceCount == 0)
    detach()

  // Primitive incompatibilities do not yet produce diagnostics, so diff tests
  // cannot establish that these input obligations were recorded at all. Check
  // the constraint targets directly, including a whole union versus its parts.
  test("each concrete upper target receives later bounds and a union stays whole"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val one = h.tpe(TypeShape.Unit)
    val two = h.tpe(TypeShape.Abstract)
    val writtenUnion = h.tpe(TypeShape.Union(one.resolution, two.resolution))
    val union = h.resolver.declaredType(writtenUnion.resolution, Map.empty)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.resolver.publishParameter(a, first)
    h.resolver.constrainTypes(ContextualType(at, Nil), ContextualType(one, Nil))
    h.resolver.constrainTypes(ContextualType(at, Nil), ContextualType(two, Nil))
    h.resolver.publishParameter(a, second)
    for target <- List(one, two); bound <- List(first, second) do
      assert(h.state.typeConstraints((target, bound, Nil)))
    val (b, bt) = h.parameter("B")
    val distinct = OpaqueTypeShape(Term.UnitVal())
    h.resolver.constrainTypes(ContextualType(bt, Nil), ContextualType(union, Nil))
    h.resolver.publishParameter(b, distinct)
    assert(h.state.typeConstraints((union, distinct, Nil)))
    assert(!h.state.typeConstraints((one, distinct, Nil)))
    assert(!h.state.typeConstraints((two, distinct, Nil)))

  test("supplied arguments receive input obligations instead of discarding them"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val one = h.tpe(TypeShape.Unit)
    val two = h.tpe(TypeShape.Abstract)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.state.markExplicitTypeArgument(a)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(first)), Nil), ContextualType(at, Nil))
    h.resolver.publishParameter(a, InstanceShape(one))
    h.resolver.publishParameter(a, InstanceShape(two))
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(second)), Nil), ContextualType(at, Nil))
    for target <- List(one, two); bound <- List(first, second) do
      assert(h.state.typeConstraints((target, bound, Nil)))
    assert(a.currentShapes.toSet == Set(InstanceShape(one), InstanceShape(two)))

  test("a supplied union receives an input obligation as one type reference"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val one = h.tpe(TypeShape.Unit)
    val two = h.tpe(TypeShape.Abstract)
    val writtenUnion = h.tpe(TypeShape.Union(one.resolution, two.resolution))
    val union = h.resolver.declaredType(writtenUnion.resolution, Map.empty)
    val bound = IntroShape(Term.UnitVal(), N)
    h.state.markExplicitTypeArgument(a)
    h.resolver.publishParameter(a, InstanceShape(union))
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil), ContextualType(at, Nil))
    assert(h.state.typeConstraints((union, bound, Nil)))
    assert(!h.state.typeConstraints((one, bound, Nil)))
    assert(!h.state.typeConstraints((two, bound, Nil)))

  test("supplied parameter references forward input obligations across marked contexts"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val source = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("source")))
    val outer = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("outer")))
    val target = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("target")))
    val site = FlowSymbol.app()
    val sourceMarks = ExitMark(source, S(site), NoMarks) :: ExitMark(outer, S(site), NoMarks) :: Nil
    val targetMarks = ExitMark(target, S(site), NoMarks) :: Nil
    val concrete = h.tpe(TypeShape.Unit)
    val bound = IntroShape(Term.UnitVal(), N)
    h.state.markExplicitTypeArgument(a)
    h.state.markExplicitTypeArgument(b)
    h.resolver.publishParameter(a, InstanceShape(bt).exit(sourceMarks).enter(targetMarks))
    h.resolver.publishParameter(b, InstanceShape(concrete).enter(sourceMarks))
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil), ContextualType(at, targetMarks))
    assert(h.state.typeConstraints((concrete, bound, Nil)))
    assert(b.currentShapes.toSet == Set(InstanceShape(concrete).enter(sourceMarks)))

  test("a supplied argument receives only obligations for its marked activation"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val owner = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("owner")))
    val firstMarks = ExitMark(owner, S(FlowSymbol.app()), NoMarks) :: Nil
    val secondMarks = ExitMark(owner, S(FlowSymbol.app()), NoMarks) :: Nil
    val one = h.tpe(TypeShape.Unit)
    val two = h.tpe(TypeShape.Abstract)
    val bound = IntroShape(Term.UnitVal(), N)
    h.state.markExplicitTypeArgument(a)
    h.resolver.publishParameter(a, InstanceShape(one).enter(firstMarks))
    h.resolver.publishParameter(a, InstanceShape(two).enter(secondMarks))
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil), ContextualType(at, firstMarks))
    assert(h.state.typeConstraints((one, bound, Nil)))
    assert(!h.state.typeConstraints((two, bound, Nil)))

  test("supplied reference cycles saturate without expanding their arguments"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val concrete = h.tpe(TypeShape.Unit)
    val bound = IntroShape(Term.UnitVal(), N)
    val lower = ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil)
    h.state.markExplicitTypeArgument(a)
    h.state.markExplicitTypeArgument(b)
    h.resolver.publishParameter(a, InstanceShape(bt))
    h.resolver.publishParameter(b, InstanceShape(at))
    h.resolver.constrainTypes(lower, ContextualType(at, Nil))
    h.resolver.publishParameter(b, InstanceShape(concrete))
    assert(h.state.typeConstraints((concrete, bound, Nil)))
    val counts = (a.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(lower, ContextualType(at, Nil))
      h.resolver.publishParameter(a, InstanceShape(bt))
      h.resolver.publishParameter(b, InstanceShape(at))
    assert((a.inferenceHost.listeners.size, b.inferenceHost.listeners.size) == counts)
    assert(a.currentShapes.toSet == Set(InstanceShape(bt)))
    assert(b.currentShapes.toSet == Set(InstanceShape(at), InstanceShape(concrete)))

  test("repeated deferred views reuse source identities for synthesized interfaces"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val substitution = h.state.instantiateTypeParameters(at.resolution, FlowSymbol.app(), List(a))
    val tuple = TupleShape(Term.UnitVal(), TupleShape.TypedField(at, Nil) :: Nil)(h.resolver)
    val view = h.resolver.instantiateShape(tuple, substitution)
    (1 to 1000).foreach: _ =>
      assert(h.resolver.instantiateShape(tuple, substitution) eq view)

  test("importers extend a cyclic relation without mutating the exporter or one another"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val ar = ContextualType(at, Nil)
    val br = ContextualType(bt, Nil)
    h.resolver.constrainTypes(ar, br)
    h.resolver.constrainTypes(br, ar)
    val output = new TermShapeHost
    h.resolver.listenInstanceViews(InstanceShape(bt))(output.publish)
    val exporter = ArrayBuffer.empty[TermShape]
    val detach = output.inferenceHost.observe(exporter += _)
    val left = new Elaborator.State().newResolverState.inGraph(h.state)
    val right = new Elaborator.State().newResolverState.inGraph(h.state)
    val leftValues = ArrayBuffer.empty[TermShape]
    val rightValues = ArrayBuffer.empty[TermShape]
    h.resolver.listenInstanceViews(InstanceShape(bt))(leftValues += _)(using left)
    h.resolver.listenInstanceViews(InstanceShape(bt))(rightValues += _)(using right)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.resolver.publishParameter(a, first)(using left)
    h.resolver.publishParameter(a, second)(using right)
    assert(leftValues.toList == List(first))
    assert(rightValues.toList == List(second))
    assert(exporter.isEmpty)
    assert(output.currentShapes.isEmpty)
    detach()
