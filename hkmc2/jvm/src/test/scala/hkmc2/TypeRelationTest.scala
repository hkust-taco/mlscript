package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable.ArrayBuffer
import hkmc2.syntax.{Cls, Fun, Tree}
import hkmc2.utils.*, shorthands.*


class TypeRelationTest extends AnyFunSuite:
  private class Harness:
    import io.PlatformPath.given
    given owner: Elaborator.State = new Elaborator.State
    given state: ResolutionContext = owner.newResolverState.context
    given Raise = diagnostic => fail(diagnostic.theMsg)
    given DebugPrinter = new DebugPrinter()
    given trace: TraceLogger = TraceLogger.silent
    given Config = Config.default(TestFolders.mainTestDir(os.pwd))
    given CompilerCtx = CompilerCtx.fresh(io.FileSystem.default, TestFolders.compilerPaths(os.pwd), summon[Config])
    val resolver = Elaborator(trace, TestFolders.mainTestDir(os.pwd), Elaborator.Ctx.empty)
    def tpe(shape: TypeShape): DeclaredType =
      val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      resolution.publish(shape)
      DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    private val argumentContext = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    def argument(source: TypeArgumentResolution, bindings: Map[VarSymbol, TypeArgument]): TypeArgument =
      val context = DeclaredType(argumentContext, bindings, TypeSubstitution.empty, true)(N)
      resolver.declaredArgument(source, context, true)
    def parameter(name: String): (VarSymbol, DeclaredType) =
      val symbol = VarSymbol(Tree.Ident(name), mut = false)
      (symbol, tpe(rctx.typeParameter(symbol)))
    def supply(symbol: VarSymbol, argument: TypeArgument, marks: Ls[Marks])(using ResolutionContext): Unit =
      resolver.bindTypeArguments(rctx.typeParameter(symbol) :: Nil, marks, argument :: Nil)
    def parameterValues(symbol: VarSymbol): ArrayBuffer[TermShape] =
      val values = ArrayBuffer.empty[TermShape]
      resolver.listenTypeParameterValues(rctx.typeParameter(symbol))(values += _)
      values
    /** A forwarding alias declared in a module, so it contributes a priority step. */
    def forwarding(name: Str, argument: DeclaredType): DeclaredType =
      val (formal, body) = parameter(s"${name}Parameter")
      val moduleName: Tree.Ident = Tree.Ident(s"${name}Namespace")
      val module = ModuleOrObjectSymbol(Tree.TypeDef(syntax.Mod, moduleName, N), moduleName)
      val symbol = TypeAliasSymbol(Tree.Ident(name))
      symbol.defn = S(TypeDef(S(module), symbol, BlockMemberSymbol(name, Nil),
        List(TyParam(FldFlags.empty, N, formal)(N)), S(body.resolution.source), N, Nil)(N, N))
      val alias = tpe(TypeShape.Alias(symbol, S(body.resolution)))
      tpe(TypeShape.Applied(alias.resolution, List(TypeArgumentResolution.Type(argument.resolution))))
    def observe(reference: ContextualType): ArrayBuffer[TermShape] =
      val values = ArrayBuffer.empty[TermShape]
      resolver.instanceShape(reference.tpe).exit(reference.marks) match
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
    h.resolver.constrainTypes(ar, br, N)
    h.resolver.constrainTypes(br, ar, N)
    val seen = h.observe(br)
    h.resolver.publishParameter(a, second)
    assert(seen.toSet == Set(first, second))
    val counts = (a.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ar, br, N)
      h.resolver.constrainTypes(br, ar, N)
      h.resolver.publishParameter(a, first)
    assert((a.inferenceHost.listeners.size, b.inferenceHost.listeners.size) == counts)
    assert(seen.toList == List(first, second))

  // Symbolic forwarding alone must not construct views of every reachable lower
  // interface. Diff tests cover the resulting namespace choices; these bounds
  // check the observation graph before and after a consumer demands those views.
  test("constraints share probe observations and leave symbolic forwarding unexpanded"):
    val h = new Harness
    import h.given
    val parameters = (1 to 64).map(index => h.parameter(s"T$index"))
    parameters.sliding(2).foreach: pair =>
      h.resolver.constrainTypes(ContextualType(pair(0)._2, Nil), ContextualType(pair(1)._2, Nil), N)
    assert(parameters.forall((_, tpe) => h.state.state.typeViews.get((tpe, false)).isEmpty))
    val (symbol, input) = parameters.head
    val tuple = h.tpe(TypeShape.Tuple(Nil))
    h.resolver.constrainTypes(ContextualType(input, Nil), ContextualType(tuple, Nil), N)
    val view = h.state.state.typeViews.get((input, false)).get
    assert(view.inferenceHost.listeners.size == 1)
    val ref = Term.UnresolvedRef(Nil, Tree.Ident("Missing"))(FlowSymbol.pat(), NameLookup.LeadingDot)
    h.resolver.publishParameter(symbol, ref.namespaceProbe)
    assert(view.currentShapes.exists(_ is ref.namespaceProbe))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ContextualType(input, Nil), ContextualType(tuple, Nil), N)
    assert(view.inferenceHost.listeners.size == 1)

  // The worksheets cannot count canonical references, candidates, or subscriptions.
  // Repeated substitutions exercise the same source graph beyond any finite test depth.
  test("probe-bearing parameter cycles share bounded flow with value-only consumers"):
    for probeFirst <- false :: true :: Nil do
      val h = new Harness
      import h.given
      val (a, at) = h.parameter("A")
      val (b, bt) = h.parameter("B")
      val ar = ContextualType(at, Nil)
      val br = ContextualType(bt, Nil)
      val ref = Term.UnresolvedRef(Nil, Tree.Ident("Missing"))(FlowSymbol.pat(), NameLookup.LeadingDot)
      val probe = ref.namespaceProbe
      val concrete = IntroShape(Term.UnitVal(), N)
      if probeFirst then h.resolver.publishParameter(a, probe)
      h.resolver.constrainTypes(ar, br, N)
      h.resolver.constrainTypes(br, ar, N)
      val seen = h.observe(br)
      if !probeFirst then h.resolver.publishParameter(a, probe)
      h.resolver.publishParameter(a, concrete)
      assert(seen.toList == concrete :: Nil)
      // Value-only observation must not filter the shared hosts: a namespace
      // constraint can subscribe to those same views after this observation.
      val hosts = (at :: bt :: Nil).iterator.flatMap: tpe =>
        (false :: true :: Nil).iterator.flatMap(merge => h.state.state.typeViews.get((tpe, merge)))
      .toList
      assert(hosts.nonEmpty && hosts.forall(_.currentShapes.exists(_ is probe)))
      def counts = (a.inferenceHost.listeners.size, b.inferenceHost.listeners.size,
        h.state.allocatedShapeViewCount,
        hosts.map(host => (host.inferenceHost.listeners.size, host.currentShapes.size)))
      val before = counts
      (1 to 1000).foreach: _ =>
        h.resolver.constrainTypes(ar, br, N)
        h.resolver.constrainTypes(br, ar, N)
        h.resolver.publishParameter(a, probe)
        h.resolver.publishParameter(a, concrete)
      assert(counts == before)
      assert(seen.toList == concrete :: Nil)

  test("namespace-bearing alias and Boolean forwarding saturate without growing the type or value graph"):
    for combination <- 0 to 3 do
      val h = new Harness
      import h.given
      val (argument, at) = h.parameter("A")
      val (_, original) = h.parameter("Target")
      val identity = h.forwarding("Identity", at)
      val source = combination match
        case 0 => identity
        case 1 => h.forwarding("Outer", identity)
        case 2 => h.tpe(TypeShape.Union(at.resolution, identity.resolution))
        case _ =>
          val union = h.tpe(TypeShape.Union(at.resolution, identity.resolution))
          h.tpe(TypeShape.Intersection(union.resolution, at.resolution))
      var current = original
      val host = new TermShapeHost
      def step(): Unit =
        current = h.resolver.declaredType(source.resolution, Map(argument -> TypeArgument.invariant(current)))
        val value = h.resolver.instanceShape(current)
        host.publish(value)
        h.resolver.constrainTypes(ContextualType(current, Nil), ContextualType(current, Nil), N)
      (1 to 10).foreach(_ => step())
      val before = (h.state.state.typeReferences.size, h.state.allocatedShapeViewCount, host.currentShapes.size)
      val observation = current
      (1 to 1000).foreach: _ =>
        step()
        assert(current == observation)
      assert((h.state.state.typeReferences.size, h.state.allocatedShapeViewCount, host.currentShapes.size) == before)
      assert(host.currentShapes.size <= 2)

  test("permuting annotated arguments retains two type uses without growing projection views"):
    val h = new Harness
    import h.given
    val (argument, at) = h.parameter("A")
    val (_, target) = h.parameter("Target")
    val first = h.resolver.declaredType(h.forwarding("First", at).resolution, Map(argument -> TypeArgument.invariant(target)))
    val second = h.resolver.declaredType(h.forwarding("Second", at).resolution, Map(argument -> TypeArgument.invariant(target)))
    assert(first != second)
    val (left, lt) = h.parameter("Left")
    val (right, rt) = h.parameter("Right")
    val wildcard = TypeArgumentResolution.Wildcard(Term.UnitVal(), S(lt.resolution), S(rt.resolution))
    var arguments = (first, second)
    val host = new TermShapeHost
    def step(): Unit =
      val current = h.argument(wildcard, Map(left -> TypeArgument.invariant(arguments._1), right -> TypeArgument.invariant(arguments._2)))
      host.publish(h.resolver.instanceShape(current.output))
      arguments = arguments.swap
    (1 to 10).foreach(_ => step())
    val before = (h.state.state.typeReferences.size, h.state.allocatedShapeViewCount)
    (1 to 1000).foreach(_ => step())
    assert(host.currentShapes.size == 2)
    assert((h.state.state.typeReferences.size, h.state.allocatedShapeViewCount) == before)

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
      def expected(values: List[TermShape], path: List[Marks]): Set[ShapeIdentity.Key] =
        values.flatMap: value =>
          value.exit(path) match
            case shape: TermShape => Some(ShapeIdentity.key(shape))
            case NoShape => None
        .toSet
      assert(observed.map(ShapeIdentity.key(_)).toSet == expected(List(first), List(exit, entry)))
      h.resolver.publishParameter(a, second)
      assert(observed.map(ShapeIdentity.key(_)).toSet == expected(List(first, second), List(exit, entry)))
      val consumed = h.resolver.transportType(inside, consumer :: Nil)
      assert(h.observe(ContextualType(consumed, Nil)).map(ShapeIdentity.key(_)).toSet ==
        expected(List(first, second), List(exit, entry, consumer)))

  test("alias argument normalization reaches a fixed point without changing its marks"):
    val h = new Harness
    import h.given
    val (formal, ft) = h.parameter("X")
    val symbol = TypeAliasSymbol(Tree.Ident("Identity"))
    val member = BlockMemberSymbol("Identity", Nil)
    symbol.defn = S(TypeDef(N, symbol, member, List(TyParam(FldFlags.empty, N, formal)(N)),
      S(ft.resolution.source), N, Nil)(N, N))
    val alias = h.tpe(TypeShape.Alias(symbol, S(ft.resolution)))
    val (argument, at) = h.parameter("A")
    val application = h.tpe(TypeShape.Applied(alias.resolution, List(TypeArgumentResolution.Type(at.resolution))))
    val (target, tt) = h.parameter("Target")
    val owner = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("owner")))
    val path = EntryMark(owner, S(FlowSymbol.app()), NoMarks)
    val original = h.resolver.transportType(tt, path :: Nil)
    val seen = h.observe(ContextualType(original, Nil))
    val before = target.inferenceHost.listeners.size
    var current = original
    var instance = Option.empty[InstanceShape]
    (1 to 1000).foreach: iteration =>
      current = h.resolver.declaredType(application.resolution, Map(argument -> TypeArgument.invariant(current)))
      assert(current == original)
      // Repeated forwarding retains one normalized namespace observation, rather than
      // a history of the applications that produced it.
      val next = h.resolver.instanceShape(current)
      if iteration > 1 then assert(instance.exists(_ eq next))
      instance = S(next)
    val value = DynShape()
    h.resolver.publishParameter(target, value)
    assert(seen.toList.map(ShapeIdentity.key(_)) == List(MarkedShape.enter(value, owner, path.id)).map(ShapeIdentity.key(_)))
    assert(target.inferenceHost.listeners.size == before)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("partial captured alias reduction uses ordinary exit and entry including caller identity loss"):
    val h = new Harness
    import h.given
    val (formal, ft) = h.parameter("X")
    val (unused, _) = h.parameter("Unused")
    val symbol = TypeAliasSymbol(Tree.Ident("Identity"))
    val member = BlockMemberSymbol("Identity", Nil)
    symbol.defn = S(TypeDef(N, symbol, member, List(TyParam(FldFlags.empty, N, formal)(N), TyParam(FldFlags.empty, N, unused)(N)),
      S(ft.resolution.source), N, Nil)(N, N))
    val alias = h.tpe(TypeShape.Alias(symbol, S(ft.resolution)))
    val scope = TermSymbol(Fun, N, Tree.Ident("owner"))
    val owner = ResolutionBoundary(scope)
    val captured = h.tpe(TypeShape.Reference(alias.resolution,
      EntryMark(owner, N, NoMarks) :: Nil, Map.empty, TypeSubstitution.empty))
    val (argument, at) = h.parameter("A")
    val application = h.tpe(TypeShape.Applied(captured.resolution, List(TypeArgumentResolution.Type(at.resolution))))
    val (target, tt) = h.parameter("Target")
    val original = h.resolver.transportType(tt, EntryMark(owner, S(FlowSymbol.app()), NoMarks) :: Nil)
    val outside = h.resolver.transportType(original, ExitMark(owner, N, NoMarks) :: Nil)
    val expected = h.resolver.transportType(outside, EntryMark(owner, N, NoMarks) :: Nil)
    assert(expected != original)
    val actual = h.resolver.declaredType(application.resolution, Map(argument -> TypeArgument.invariant(original)))
    assert(actual == expected)
    val early = IntroShape(Term.UnitVal(), N)
    val late = DynShape()
    h.resolver.publishParameter(target, early)
    val seen = h.observe(ContextualType(actual, Nil))
    h.resolver.publishParameter(target, late)
    assert(seen.toList.map(ShapeIdentity.key(_)) == List(early, late).map(MarkedShape.enter(_, owner, N)).map(ShapeIdentity.key(_)))
    val count = target.inferenceHost.listeners.size
    (1 to 1000).foreach: _ =>
      assert(h.resolver.declaredType(application.resolution, Map(argument -> TypeArgument.invariant(actual))) == expected)
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
      val wildcard = TypeArgumentResolution.Wildcard(Term.UnitVal(), Option.when(input)(ft.resolution), Option.when(output)(ft.resolution))
      val first = h.argument(wildcard, Map(formal -> TypeArgument.invariant(original)))
      val observed = h.observe(ContextualType(first.output, Nil))
      val inputObserved = h.observe(ContextualType(first.input, Nil))
      val before = target.inferenceHost.listeners.size
      var current = first
      (1 to 1000).foreach: _ =>
        current = h.argument(wildcard, Map(formal -> current))
        assert(current.input.reference eq first.input.reference)
        assert(current.output.reference eq first.output.reference)
      val value = DynShape()
      h.resolver.publishParameter(target, value)
      if output then assert(observed.toList.map(ShapeIdentity.key(_)) == List(MarkedShape.enter(value, scope, site)).map(ShapeIdentity.key(_)))
      else assert(!observed.exists(_.applicationHead._1.isInstanceOf[DynShape]))
      if input then assert(inputObserved.toList.map(ShapeIdentity.key(_)) == List(MarkedShape.enter(value, scope, site)).map(ShapeIdentity.key(_)))
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
    val expected = h.resolver.declaredType(source.resolution, Map(a -> TypeArgument.invariant(original)))
    val early = IntroShape(Term.UnitVal(), N)
    val late = DynShape()
    h.resolver.publishParameter(target, early)
    val seen = h.observe(ContextualType(expected, Nil))
    val counts = (target.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    var current = expected
    (1 to 1000).foreach: _ =>
      current = h.resolver.declaredType(source.resolution, Map(a -> TypeArgument.invariant(current)))
      assert(current.reference eq expected.reference)
      h.resolver.listenInstanceViews(h.resolver.instanceShape(current))(_ => ())
    h.resolver.publishParameter(b, late)
    assert(seen.toSet.map(ShapeIdentity.key(_)) == Set(MarkedShape.enter(early, owner, path.id), late).map(ShapeIdentity.key(_)))
    assert((target.inferenceHost.listeners.size, b.inferenceHost.listeners.size) == counts)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("nullable open record views do not multiply across call-site round trips"):
    // Each of n incoming records must return through its own call site. Moving
    // its entry marks into the fields before returning creates n squared record
    // candidates. Diff tests cannot measure this growth or listener saturation.
    for count <- List(2, 8, 16) do
      val h = new Harness
      import h.given
      val (argument, at) = h.parameter("Argument")
      val (element, et) = h.parameter("Element")
      val field = RcdField.signature(Term.Lit(Tree.StrLit("value")), Term.UnitVal())
      val source: Term.Rcd = Term.Rcd(false, List(field))
      val record = RecordTypeShape(Map("value" -> et), Map.empty)(source, Map("value" -> field))
      val nullable = h.tpe(TypeShape.Union(at.resolution, h.tpe(TypeShape.Unit).resolution))
      val boundary = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("forward")))
      val sites = List.fill(count)(FlowSymbol.app())
      val returned = new TermShapeHost
      h.resolver.listenInstanceViews(h.resolver.instanceShape(nullable)):
        case value @ Marked(_: RecordTypeShape, _) => sites.foreach: site =>
          value.exit(ExitMark(boundary, S(site), NoMarks)) match
            case result: TermShape => returned.publish(result)
            case NoShape => ()
        case _ => ()
      val inputs = sites.map(site => MarkedShape.enter(record, boundary, S(site)))
      inputs.foreach(h.resolver.publishParameter(argument, _))
      withClue(s"$count call sites: "):
        assert(returned.currentShapes.size == 1)
      val listeners = argument.inferenceHost.listeners.size
      (1 to 100).foreach: _ =>
        inputs.foreach(h.resolver.publishParameter(argument, _))
      assert(returned.currentShapes.size == 1)
      assert(argument.inferenceHost.listeners.size == listeners)
      // The shared result remains open: a field bound published after every
      // round trip must reach an already installed member observation.
      val fields = ArrayBuffer.empty[TermShape]
      returned.listen: value =>
        value.getMember("value") match
          case MemberLookup.Typed(_, tpe, marks) =>
            h.resolver.listenInstanceViews(h.resolver.instanceShape(h.resolver.transportType(tpe, marks)))(fields += _)
          case _ => fail("Expected a declared record field")
      assert(fields.isEmpty)
      val late = DynShape()
      h.resolver.publishParameter(element, late)
      assert(fields.toList == List(late))
      assert(h.state.allocatedTypeInstanceCount == 0)

  test("transported references share source subscriptions and retain early and late bounds"):
    // Diff tests cannot measure source subscriptions. Distinct return paths must
    // share one source interpretation even as more call sites observe its views.
    for count <- List(2, 8, 16) do
      val h = new Harness
      import h.given
      val (argument, at) = h.parameter("Argument")
      val boundary = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("forward")))
      val sites = List.fill(count)(FlowSymbol.app())
      val early = IntroShape(Term.UnitVal(), N)
      val late = DynShape()
      h.resolver.publishParameter(argument, MarkedShape.enter(early, boundary, S(sites.head)))
      h.observe(ContextualType(at, Nil))
      val listeners = at.resolution.inferenceHost.listeners.size
      assert(listeners > 0)
      val references = sites.map(site => ContextualType(at, ExitMark(boundary, S(site), NoMarks) :: Nil))
      val observations = references.map(h.observe)
      assert(at.resolution.inferenceHost.listeners.size == listeners)
      assert(observations.head.toList == early :: Nil)
      assert(observations.tail.forall(_.isEmpty))
      sites.foreach(site => h.resolver.publishParameter(argument, MarkedShape.enter(late, boundary, S(site))))
      assert(observations.head.toList == List(early, late))
      assert(observations.tail.forall(_.toList == late :: Nil))
      (1 to 100).foreach: _ =>
        references.lazyZip(observations).foreach: (reference, seen) =>
          assert(h.observe(reference).toList == seen.toList)
      assert(at.resolution.inferenceHost.listeners.size == listeners)
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
      DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    val left = ContextualType(recursiveRecord(at), Nil)
    val right = ContextualType(recursiveRecord(bt), Nil)
    val first = IntroShape(Term.UnitVal(), N)
    val later = DynShape()
    h.resolver.publishParameter(a, first)
    h.resolver.constrainTypes(left, right, N)
    val seen = h.observe(ContextualType(bt, Nil))
    assert(seen.toList == List(first))
    def counts = List(left.tpe.resolution.inferenceHost.listeners.size, right.tpe.resolution.inferenceHost.listeners.size,
      a.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    val before = counts
    h.resolver.publishParameter(a, later)
    assert(seen.toList == List(first, later))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(left, right, N)
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
    early.publish(TypeShape.Tuple(List(at.resolution, late).map(TypeShape.TupleField(_, spread = false))))
    val left = h.resolver.declaredType(early, Map(a -> TypeArgument.invariant(h.tpe(TypeShape.Inferred(first)))))
    val right = h.resolver.declaredType(early, Map(a -> TypeArgument.invariant(h.tpe(TypeShape.Inferred(second)))))
    val leftSeen = h.observe(ContextualType(left, Nil))
    val rightSeen = h.observe(ContextualType(right, Nil))
    assert(leftSeen.isEmpty && rightSeen.isEmpty)
    // Closing a recursive dependency must wake both observers without merging
    // their environments or allocating a parameter for the forward reference.
    late.publish(TypeShape.Tuple(List(at.resolution, early).map(TypeShape.TupleField(_, spread = false))))
    def firstField(values: ArrayBuffer[TermShape]): Set[TermShape] = values.toList match
      case (tuple: TupleShape) :: Nil => tuple.elements.head match
        case TupleShape.TypedField(bounds, marks) => h.observe(ContextualType(bounds.output, marks)).toSet
        case _ => fail("Expected a declared tuple field")
      case _ => fail("Expected one declared tuple")
    assert(firstField(leftSeen) == Set(first))
    assert(firstField(rightSeen) == Set(second))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ContextualType(left, Nil), ContextualType(right, Nil), N)
    val saturated = (early.inferenceHost.listeners.size, late.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(ContextualType(left, Nil), ContextualType(right, Nil), N)
    assert((early.inferenceHost.listeners.size, late.inferenceHost.listeners.size) == saturated)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("delayed argument endpoints retain independent flow without growing listeners"):
    val h = new Harness
    import h.given
    val (input, inputType) = h.parameter("Input")
    val (output, outputType) = h.parameter("Output")
    val inputResolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val outputResolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val argument = TypeArgument(
      DeclaredType(inputResolution, Map.empty, TypeSubstitution.empty, true)(N),
      DeclaredType(outputResolution, Map.empty, TypeSubstitution.empty, true)(N))
    val negative = argument.at(false)
    val positive = argument.at(true)
    val neg = ContextualType(negative, Nil)
    val pos = ContextualType(positive, Nil)
    val negativeValues = h.observe(neg)
    val positiveValues = h.observe(pos)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    val lower = ContextualType(h.tpe(TypeShape.Inferred(first)), Nil)
    h.resolver.constrainTypes(lower, neg, N)
    assert(negativeValues.isEmpty && positiveValues.isEmpty)
    inputResolution.publish(TypeShape.Contextual(ContextualType(inputType, Nil)))
    assert(negativeValues.toList == List(first))
    assert(positiveValues.isEmpty)
    h.resolver.publishParameter(output, second)
    assert(positiveValues.isEmpty)
    outputResolution.publish(TypeShape.Contextual(ContextualType(outputType, Nil)))
    assert(positiveValues.toList == List(second))
    def counts = (inputResolution.inferenceHost.listeners.size, outputResolution.inferenceHost.listeners.size,
      input.inferenceHost.listeners.size, output.inferenceHost.listeners.size)
    val before = counts
    (1 to 1000).foreach: _ =>
      // Replaying a constraint must retain the selected endpoint's late bounds
      // without subscribing to its graph again.
      h.resolver.constrainTypes(lower, neg, N)
    assert(counts == before)
    assert(negativeValues.toList == List(first))
    assert(positiveValues.toList == List(second))
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("cyclic argument endpoints wait for productive bounds without expanding the cycle"):
    val h = new Harness
    import h.given
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val argument = TypeArgument.invariant(DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N))
    val selected = argument.output
    val reference = ContextualType(selected, Nil)
    val seen = h.observe(reference)
    resolution.publish(TypeShape.Combined(TypeFormula.atom(selected)))
    assert(seen.isEmpty)
    val (parameter, bound) = h.parameter("Later")
    resolution.publish(TypeShape.Combined(TypeFormula.atom(bound)))
    val value = IntroShape(Term.UnitVal(), N)
    h.resolver.publishParameter(parameter, value)
    assert(seen.toList == List(value))
    h.resolver.constrainTypes(reference, reference, N)
    val counts = (resolution.inferenceHost.listeners.size, parameter.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(reference, reference, N)
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
    h.resolver.constrainTypes(left, right, N)
    h.resolver.constrainTypes(right, left, N)
    val seen = h.observe(right)
    assert(seen.isEmpty)
    val bound = IntroShape(Term.UnitVal(), N)
    val input = ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil)
    h.resolver.constrainTypes(input, left, N)
    def listeners(tpe: DeclaredType): Int = tpe.resolution.currentShapes.toList match
      case TypeShape.Hole(host) :: Nil => host.listeners.size
      case _ => fail("An omitted argument must retain its inference host")
    val counts = (listeners(first), listeners(second))
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(left, right, N)
      h.resolver.constrainTypes(right, left, N)
      h.resolver.constrainTypes(input, left, N)
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
    h.resolver.listenInstanceViews(h.resolver.instanceShape(hole))(output.publish)
    val exporter = ArrayBuffer.empty[TermShape]
    val detach = output.inferenceHost.observe(exporter += _)
    val left = new Elaborator.State().newResolverState.context.inGraph(h.state)
    val right = new Elaborator.State().newResolverState.context.inGraph(h.state)
    assert(h.resolver.omittedType(source, parameter)(using left) eq hole)
    assert(h.resolver.omittedType(source, parameter)(using right) eq hole)
    val leftValues = ArrayBuffer.empty[TermShape]
    val rightValues = ArrayBuffer.empty[TermShape]
    h.resolver.listenInstanceViews(h.resolver.instanceShape(hole)(using left))(leftValues += _)(using left)
    h.resolver.listenInstanceViews(h.resolver.instanceShape(hole)(using right))(rightValues += _)(using right)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(first)), Nil), ContextualType(hole, Nil), N)(using left)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(second)), Nil), ContextualType(hole, Nil), N)(using right)
    assert(leftValues.toList == List(first))
    assert(rightValues.toList == List(second))
    assert(exporter.isEmpty)
    assert(output.currentShapes.isEmpty)
    assert(h.state.allocatedTypeInstanceCount == 0)
    assert(left.allocatedTypeInstanceCount == 0)
    assert(right.allocatedTypeInstanceCount == 0)
    detach()

  test("closed nominal candidates do not multiply along generic substitution paths"):
    // A worksheet can check the selected member, but cannot detect redundant
    // candidates that multiply when a constraint cycle crosses generic callers.
    val h = new Harness
    import h.given
    val name: Tree.Ident = Tree.Ident("Closed")
    val symbol = ClassSymbol(Tree.TypeDef(Cls, name, N), name)
    val defn = ClassDef.Plain(N, Cls, symbol, BlockMemberSymbol("Closed", Nil), Nil, N,
      ObjBody(Term.Blk(Nil, Term.UnitVal())), N, Nil, Nil, N, Nil)(N, N, N)
    h.state.state.lexicalTypeBinders(symbol) = Set.empty
    val original = NominalInstanceView(defn, Map.empty, N)(N, ShapeProvenance.empty)(h.resolver)
    val scheme = h.tpe(TypeShape.Top).resolution
    val substitutions = (1 to 16).map: index =>
      val (parameter, _) = h.parameter(s"A$index")
      h.state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), S(Set.empty))
    val host = new TermShapeHost
    var current: TermShape = original
    (1 to 1000).foreach: index =>
      current = h.resolver.instantiateShape(current, substitutions(index % substitutions.size))
      host.publish(current)
      assert(host.currentShapes.size == 1)
    assert(h.state.allocatedTypeInstanceCount == substitutions.size)

  test("intersection inputs propagate independently and reuse their subscriptions"):
    // Diff tests cover inferred interfaces. This also checks that one intersection
    // component can propagate before the other has any candidates, and that replay
    // of the relation does not grow subscriptions or allocate parameter instances.
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val (_, result) = h.parameter("Result")
    val input = ContextualType(h.tpe(TypeShape.Intersection(at.resolution, bt.resolution)), Nil)
    val expected = ContextualType(h.tpe(TypeShape.Tuple(TypeShape.TupleField(result.resolution, spread = false) :: Nil)), Nil)
    val seen = h.observe(ContextualType(result, Nil))
    def tuple(value: TermShape): TermShape =
      h.resolver.instanceShape(h.tpe(TypeShape.Tuple(TypeShape.TupleField(h.tpe(TypeShape.Inferred(value)).resolution, spread = false) :: Nil)))
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    val left = tuple(first)
    val right = tuple(second)
    h.resolver.constrainTypes(input, expected, N)
    h.resolver.publishParameter(a, left)
    assert(seen.toList == List(first))
    h.resolver.publishParameter(b, right)
    assert(seen.toSet == Set(first, second))
    val counts = (a.inferenceHost.listeners.size, b.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(input, expected, N)
      h.resolver.publishParameter(a, left)
      h.resolver.publishParameter(b, right)
    assert((a.inferenceHost.listeners.size, b.inferenceHost.listeners.size) == counts)
    assert(seen.size == 2)
    assert(h.state.allocatedTypeInstanceCount == 0)

  test("supplied arguments receive input obligations instead of discarding them"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val one = h.tpe(TypeShape.Unit)
    val two = h.tpe(TypeShape.Abstract)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.state.markExplicitTypeArgument(a)
    val outputs = h.parameterValues(a)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(first)), Nil), ContextualType(at, Nil), N)
    h.supply(a, TypeArgument.invariant(one), Nil)
    h.supply(a, TypeArgument.invariant(two), Nil)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(second)), Nil), ContextualType(at, Nil), N)
    for target <- List(one, two); bound <- List(first, second) do
      assert(h.state.hasTypeConstraint(target, bound, Nil))
    assert(outputs.toSet == Set(h.resolver.instanceShape(one), h.resolver.instanceShape(two)))


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
    val outputs = h.parameterValues(b)
    h.supply(a, TypeArgument.invariant(h.resolver.transportType(bt, sourceMarks)), targetMarks)
    h.supply(b, TypeArgument.invariant(concrete), sourceMarks)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil), ContextualType(at, targetMarks), N)
    assert(h.state.hasTypeConstraint(concrete, bound, Nil))
    val expected = h.resolver.instanceShape(concrete).enter(sourceMarks) match
      case value: TermShape => ShapeIdentity.key(value)
      case NoShape => fail("Expected a transported value")
    assert(outputs.map(ShapeIdentity.key(_)).toSet == Set(expected))

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
    h.supply(a, TypeArgument.invariant(one), firstMarks)
    h.supply(a, TypeArgument.invariant(two), secondMarks)
    h.resolver.constrainTypes(ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil), ContextualType(at, firstMarks), N)
    assert(h.state.hasTypeConstraint(one, bound, Nil))
    assert(!h.state.hasTypeConstraint(two, bound, Nil))

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
    val outputsA = h.parameterValues(a)
    val outputsB = h.parameterValues(b)
    h.supply(a, TypeArgument.invariant(bt), Nil)
    h.supply(b, TypeArgument.invariant(at), Nil)
    h.resolver.constrainTypes(lower, ContextualType(at, Nil), N)
    h.supply(b, TypeArgument.invariant(concrete), Nil)
    assert(h.state.hasTypeConstraint(concrete, bound, Nil))
    def counts: (Int, Int, Int, Int) = (a.inferenceHost.listeners.size, b.inferenceHost.listeners.size,
      rctx.typeParameter(a).arguments.listeners.size, rctx.typeParameter(b).arguments.listeners.size)
    val initialCounts = counts
    (1 to 1000).foreach: _ =>
      h.resolver.constrainTypes(lower, ContextualType(at, Nil), N)
      h.supply(a, TypeArgument.invariant(bt), Nil)
      h.supply(b, TypeArgument.invariant(at), Nil)
    assert(counts == initialCounts)
    // Republishing must neither add edges nor redeliver an existing output.
    assert(outputsA.toList == List(h.resolver.instanceShape(bt)))
    assert(outputsB.toList == List(h.resolver.instanceShape(at), h.resolver.instanceShape(concrete)))

  test("repeated deferred views reuse source identities for synthesized interfaces"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val substitution = h.state.instantiateTypeParameters(at.resolution, FlowSymbol.app(), List(a), None)
    val tuple = TupleShape(Term.UnitVal(), TupleShape.TypedField(TypeArgument.invariant(at), Nil) :: Nil)(h.resolver)
    val view = h.resolver.instantiateShape(tuple, substitution)
    (1 to 1000).foreach: _ =>
      assert(h.resolver.instantiateShape(tuple, substitution) eq view)

  test("explicit bindings preserve intermediate exporter constraints and isolate consumer graphs"):
    // Diff tests cover endpoint selection. This checks private graph ownership
    // and listener growth when several bindings share the same output type.
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (_, input) = h.parameter("Input")
    val (_, leftInput) = h.parameter("LeftInput")
    val (_, rightInput) = h.parameter("RightInput")
    val (_, localInput) = h.parameter("LocalInput")
    val output = h.tpe(TypeShape.Unit)
    val values = new TermShapeHost
    h.resolver.listenTypeParameterValues(rctx.typeParameter(a)): value =>
      values.publish(value)
      // Count deliveries with graph-local edges, so an inherited observer does
      // not capture a mutable counter shared by all importing consumers.
      values.addShapeListener(_ => ())
    h.supply(a, TypeArgument(input, output), Nil)
    val left = new Elaborator.State().newResolverState.context.inGraph(h.state)
    val right = new Elaborator.State().newResolverState.context.inGraph(h.state)
    h.supply(a, TypeArgument(leftInput, output), Nil)(using left)
    h.supply(a, TypeArgument(rightInput, output), Nil)(using right)
    val consumer = new Elaborator.State().newResolverState.context.inGraph(left)
    val sibling = new Elaborator.State().newResolverState.context.inGraph(left)
    val bound = IntroShape(Term.UnitVal(), N)
    val lower = ContextualType(h.tpe(TypeShape.Inferred(bound)), Nil)
    h.resolver.constrainTypes(lower, ContextualType(at, Nil), N)(using consumer)
    // Publishing after the constraint must replay it into the consumer's new
    // binding without changing the already observed exporter or its sibling.
    h.supply(a, TypeArgument(localInput, output), Nil)(using consumer)
    def observe(tpe: DeclaredType, context: ResolutionContext): Ls[TermShape] =
      val values = ArrayBuffer.empty[TermShape]
      h.resolver.listenInstanceViews(h.resolver.instanceShape(tpe)(using context))(values += _)(using context)
      values.toList
    List(input, leftInput, localInput).foreach: tpe =>
      assert(observe(tpe, consumer) == (bound :: Nil))
      List(h.state, left, right, sibling).foreach(context => assert(observe(tpe, context).isEmpty))
    assert(observe(rightInput, consumer).isEmpty)
    def bindings(context: ResolutionContext) = context.typeParameter(a).arguments
    assert(bindings(h.state).shapes.size == 1)
    assert(bindings(left).shapes.size == 2)
    assert(bindings(right).shapes.size == 2)
    assert(bindings(sibling).shapes.size == 2)
    assert(bindings(consumer).shapes.size == 3)
    val listeners = bindings(consumer).listeners.size
    (1 to 1000).foreach: _ =>
      h.supply(a, TypeArgument(localInput, output), Nil)(using consumer)
      h.resolver.constrainTypes(lower, ContextualType(at, Nil), N)(using consumer)
    assert(bindings(consumer).shapes.size == 3)
    assert(bindings(consumer).listeners.size == listeners)
    List(h.state, left, right, consumer, sibling).foreach: context =>
      assert(values.inferenceHost(using context).listeners.size == 1)
    // Both consumers must deliver the same new output independently, even when
    // another input binding already delivered it in their sibling's graph.
    val laterOutput = h.tpe(TypeShape.Abstract)
    List(consumer, sibling).foreach: context =>
      h.supply(a, TypeArgument(localInput, laterOutput), Nil)(using context)
      h.supply(a, TypeArgument(rightInput, laterOutput), Nil)(using context)
      assert(values.inferenceHost(using context).listeners.size == 2)
      assert(values.currentShapes(using context).size == 2)
    List(h.state, left, right).foreach: context =>
      assert(values.inferenceHost(using context).listeners.size == 1)
      assert(values.currentShapes(using context).size == 1)

  test("importers extend a cyclic relation without mutating the exporter or one another"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val ar = ContextualType(at, Nil)
    val br = ContextualType(bt, Nil)
    h.resolver.constrainTypes(ar, br, N)
    h.resolver.constrainTypes(br, ar, N)
    val output = new TermShapeHost
    h.resolver.listenInstanceViews(h.resolver.instanceShape(bt))(output.publish)
    val exporter = ArrayBuffer.empty[TermShape]
    val detach = output.inferenceHost.observe(exporter += _)
    val left = new Elaborator.State().newResolverState.context.inGraph(h.state)
    val right = new Elaborator.State().newResolverState.context.inGraph(h.state)
    val leftValues = ArrayBuffer.empty[TermShape]
    val rightValues = ArrayBuffer.empty[TermShape]
    h.resolver.listenInstanceViews(h.resolver.instanceShape(bt)(using left))(leftValues += _)(using left)
    h.resolver.listenInstanceViews(h.resolver.instanceShape(bt)(using right))(rightValues += _)(using right)
    val first = IntroShape(Term.UnitVal(), N)
    val second = DynShape()
    h.resolver.publishParameter(a, first)(using left)
    h.resolver.publishParameter(a, second)(using right)
    assert(leftValues.toList == List(first))
    assert(rightValues.toList == List(second))
    assert(exporter.isEmpty)
    assert(output.currentShapes.isEmpty)
    detach()

  test("recursive record intersections reuse type views and stop adding graph edges"):
    // Diff tests check member behavior; this measures graph growth and object
    // reuse after saturation, which their golden output cannot observe.
    val h = new Harness
    import h.given
    val left = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val right = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    def recursive(resolution: TypeResolution): Unit =
      val next = RcdField.signature(Term.Lit(Tree.StrLit("next")), Term.UnitVal())
      val source: Term.Rcd = Term.Rcd(false, List(next))
      resolution.publish(TypeShape.Record(source, List(next -> resolution)))
    recursive(left)
    recursive(right)
    val intersection = h.tpe(TypeShape.Intersection(left, right))
    def record(tpe: DeclaredType): RecordTypeShape = h.observe(ContextualType(tpe, Nil)).toList match
      case (value: RecordTypeShape) :: Nil => value
      case _ => fail("Expected one merged record")
    val first = record(intersection)
    val next = first.fields("next")
    val saturated = record(next)
    val counts = (left.inferenceHost.listeners.size, right.inferenceHost.listeners.size)
    (1 to 1000).foreach: _ =>
      assert(record(saturated.fields("next")) eq saturated)
    assert((left.inferenceHost.listeners.size, right.inferenceHost.listeners.size) == counts)
    assert(h.state.allocatedTypeInstanceCount == 0)
