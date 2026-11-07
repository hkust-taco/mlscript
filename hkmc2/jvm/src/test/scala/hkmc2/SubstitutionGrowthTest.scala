package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable.ArrayBuffer

import hkmc2.syntax.Tree
import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


/** Binder substitutions stay bounded by what a value can observe (see
  * NewResolver.instantiateShape). These tests cover what diff tests cannot
  * observe: the number of views and activation contexts that resolution
  * allocates while compiling generated units of growing size, and the
  * algebraic laws of substitution on individual shapes.
  */
class SubstitutionGrowthTest extends AnyFunSuite:

  private enum Variant:
    case Plain, UnusedParameter, Annotated, Dependent, Branching

  /** A chain of private identity functions `f1` ... `fk`, each passing its argument
    * to the next, called once with a value produced outside every generic scope.
    * The branching variant forwards the value through one of two generic
    * identities at each level, so the value returns to `f1` along 2^k call paths.
    */
  private def chain(k: Int, variant: Variant): Str =
    val definitions = (1 to k).map: i =>
      val next = if i == k then "value" else s"f${i + 1}(value)"
      variant match
        case Variant.Plain => s"private fun f$i(value) = $next"
        case Variant.UnusedParameter => s"private fun f$i[T$i](value) = $next"
        case Variant.Annotated => s"private fun f$i[T$i](value: Item): Item = $next"
        case Variant.Dependent => s"private fun f$i[T$i](value: T$i): T$i = $next"
        case Variant.Branching =>
          s"""private fun g$i[G$i](x) = x
             |private fun h$i[H$i](x) = x
             |private fun f$i(value) = if value.value > 0 then g$i($next) else h$i($next)""".stripMargin
    s"""#lang(0.3.x)
       |
       |class Item(val value: Int)
       |${definitions.mkString("\n")}
       |fun use() = f1(Item(1)).value
       |""".stripMargin

  private final case class Measurement(views: Int, largestSubstitution: Int, activations: Int, typeInstances: Int)

  private val cctx = TestFolders.compilerCtx(os.pwd)
  private given DebugPrinter = new DebugPrinter()
  private val tl = TraceLogger.silent

  private def allocationCounter: com.sun.management.ThreadMXBean =
    val allocation = java.lang.management.ManagementFactory.getThreadMXBean match
      case bean: com.sun.management.ThreadMXBean if bean.isThreadAllocatedMemorySupported => bean
      case _ => cancel("This JVM does not expose thread allocation counters")
    allocation.setThreadAllocatedMemoryEnabled(true)
    allocation

  /** Resolves a generated unit through ordinary elaboration, in a fresh state. */
  private def measure(name: Str, source: Str): Measurement =
    val dir = os.temp.dir(prefix = "substitution-growth-")
    val file = dir / s"$name.mls"
    os.write(file, source)
    measure(file)

  private def measure(file: os.Path): Measurement =
    val diagnostics = ArrayBuffer.empty[Diagnostic]
    given Raise = diagnostics += _
    val prelude = cctx.getPrelude(cctx.paths.preludeFile)(using tl, summon[Raise]).ctx
    val artifact = cctx.getElaboratedBlock(file, prelude)(using tl, summon[Raise])
    val errors = diagnostics.collect { case error: ErrorReport => error }
    assert(errors.isEmpty, s"Unexpected errors in ${file.baseName}:\n${errors.map(_.theMsg).mkString("\n")}")
    val state = artifact.state.newResolverState.context
    Measurement(state.allocatedShapeViewCount, state.largestRetainedSubstitution,
      state.activationContextCount, state.allocatedTypeInstanceCount)

  // The value passed along each chain is produced outside every generic scope,
  // so no view of it should retain more than the one binding of the scope
  // reading it, and the number of views and activation contexts should grow
  // with the number of definitions, not with the number of call paths.
  // Before substitutions were projected onto their support, the unused-parameter
  // chain retained a substitution of size k, and the branching chain allocated
  // 2^(k+2) views and 2^k activation contexts (65534 and 16412 at k = 14).
  test("substitutions through irrelevant generic scopes stay bounded"):
    for variant <- Variant.values; k <- List(2, 6, 10, 14) do
      val m = measure(s"${variant}_$k", chain(k, variant))
      withClue(s"$variant chain of length $k: $m"):
        assert(m.typeInstances == (if variant == Variant.Plain then 0 else if variant == Variant.Branching then 2 * k else k))
        assert(m.largestSubstitution <= 2)
        assert(m.views <= 2 * k + 4)
        assert(m.activations <= 2 * k + 4)

  // Constructor patterns synthesize omitted type arguments in the pattern's
  // lexical scope. Missing that scope made recursive FingerTreeList patterns
  // retain unrelated callers' binders, allocating over 15000 views. The generic
  // IterableBase signatures add views at the tree's constructor-pattern sites;
  // skipping wildcard field reads keeps the current fixture near 3200 views.
  // Check allocations independently of machine-dependent timeouts; the .mls
  // tests cover observable behavior.
  test("FingerTreeList constructor-pattern inference stays bounded"):
    val m = measure(TestFolders.compileTestDir(os.pwd) / "FingerTreeList.mls")
    withClue(s"FingerTreeList inference: $m"):
      assert(m.largestSubstitution <= 4)
      assert(m.views < 3500)

  // A constructor test still refines the input when every field is a wildcard,
  // but it needs none of those fields' values. Reading each ignored field used
  // to allocate a view per field and construction site. Keep the cost bounded
  // by the number of constructions as the number of ignored fields grows.
  test("wildcard constructor fields do not allocate substitution views"):
    val callSites = 10
    for width <- List(2, 6, 10, 14) do
      val fields = (1 to width).map(i => s"val field$i: A").mkString(", ")
      val wildcards = List.fill(width)("_").mkString(", ")
      val arguments = List.fill(width)("Item(42)").mkString(", ")
      val calls = List.fill(callSites)(s"discard(new Box[Item]($arguments))").mkString(", ")
      val m = measure(s"IgnoredFields_$width",
        s"""#lang(0.3.x)
           |
           |class Item(val value: Int)
           |class Box[A]($fields)
           |private fun discard(box) = if box is Box($wildcards) then 1 else 0
           |fun use() = [$calls]
           |""".stripMargin)
      withClue(s"$width ignored fields at $callSites construction sites: $m"):
        assert(m.largestSubstitution <= 1)
        assert(m.views <= 2 * callSites)

  // The branching chain above, passing a promise produced outside every generic
  // scope. Its views are projected onto the support of its payload, which is
  // recorded on the payload host and on the synthesized Awaited reference
  // wrapping it. The async body is a parameter reference, a term that records no
  // lexical scope of its own. When either scope was unknown, every view of the
  // promise retained its callers' bindings, allocating 3 * 2^k - 1 views
  // (3071 at k = 10) instead of one.
  test("promises through irrelevant generic scopes stay bounded"):
    for k <- List(2, 6, 10, 14) do
      val definitions = (1 to k).map: i =>
        val next = if i == k then "value" else s"f${i + 1}(value, flag)"
        s"""private fun g$i[G$i](x) = x
           |private fun h$i[H$i](x) = x
           |private fun f$i(value, flag) = if flag then g$i($next) else h$i($next)""".stripMargin
      val m = measure(s"Promise_$k",
        s"""#lang(0.3.x)
           |
           |class Item(val value: Int)
           |@annotations.async
           |private fun produce(item) = item
           |${definitions.mkString("\n")}
           |fun use(flag) = f1(produce(Item(1)), flag).then(item => item.value)
           |""".stripMargin)
      withClue(s"promise chain of length $k: $m"):
        assert(m.largestSubstitution <= 2)
        assert(m.views <= 2 * k + 4)
        assert(m.activations <= 2 * k + 4)

  // Each spread observes both branches of a recursive iterable producer. The
  // element hosts must join those flows instead of enumerating their product.
  // Diff tests check the resulting members; only this test observes graph size.
  test("recursive iterable spreads keep inference growth bounded"):
    for k <- List(2, 6, 10, 14) do
      val spreads = List.fill(k)("...xs").mkString(", ")
      val m = measure(s"Iterable_$k",
        s"""#lang(0.3.x)
           |
           |class Item(val value: Int)
           |private fun forward[A](xs: Iterable[A] | Array[A], n: Int): Iterable[A] | Array[A] =
           |  if n == 0 then xs else forward([$spreads], n - 1)
           |fun use(xs: Iterable[Item]) = [...forward(xs, 2)].map(x => x.value)
           |""".stripMargin)
      withClue(s"recursive iterable with $k spreads: $m"):
        assert(m.largestSubstitution <= 4)
        assert(m.views <= 80 * k + 300)
        assert(m.activations <= 20 * k + 100)
        assert(m.typeInstances <= 8 * k + 20)

  /** Shapes and instances for the substitution laws below. */
  private class Harness:
    given owner: Elaborator.State = new Elaborator.State
    given state: ResolutionContext = owner.newResolverState.context
    given Raise = diagnostic => fail(diagnostic.theMsg)
    given trace: TraceLogger = TraceLogger.silent
    given Config = Config.default(TestFolders.mainTestDir(os.pwd))
    given CompilerCtx = CompilerCtx.fresh(io.FileSystem.default, TestFolders.compilerPaths(os.pwd), summon[Config])
    val resolver = Elaborator(trace, TestFolders.mainTestDir(os.pwd), Elaborator.Ctx.empty)
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    def binder(name: Str): VarSymbol =
      val symbol = VarSymbol(Tree.Ident(name), mut = false)
      symbol.decl = S(TyParam(FldFlags.empty, N, symbol)(N))
      symbol
    def instance(binder: VarSymbol): TypeParameterInstance = instanceAt(binder, Set.empty)
    /** An instance of `binder` at a site where `site` are the binders in scope. */
    def instanceAt(binder: VarSymbol, site: Set[VarSymbol]): TypeParameterInstance =
      state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(binder), S(site))(binder)
    /** The type denoted by a binder or instance reference. */
    def typeOf(symbol: VarSymbol): DeclaredType =
      val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      resolution.publish(rctx.typeParameter(symbol))
      DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    def instanceOf(tpe: DeclaredType): InstanceShape = resolver.instanceShape(tpe)
    def instancesOf(shape: TermShape): Map[VarSymbol, TypeParameterInstance] = shape match
      case instance: InstanceShape => instance.tpe.instances.iterator.toMap
      case other => fail(s"Expected an instance, got ${other.describe}")
    /** A tuple holding `value`, written where no binder is in scope. */
    def holding(value: TermShape): TupleShape =
      val source = Term.Tup(Fld(FldFlags.empty, Term.UnitVal(), N) :: Nil)(Tree.DummyTup)
      state.recordLexicalBinders(source, Set.empty)
      TupleShape(source, TupleShape.ValueField(value, Nil) :: Nil)(resolver)
    /** A tuple literal `[()]` written where `binders` are in scope. */
    def tuple(binders: Set[VarSymbol]): TupleShape =
      val source = Term.Tup(Fld(FldFlags.empty, Term.UnitVal(), N) :: Nil)(Tree.DummyTup)
      state.recordLexicalBinders(source, binders)
      TupleShape(source, TupleShape.Field(Fld(FldFlags.empty, Term.UnitVal(), N), Nil) :: Nil)(resolver)

  // Diff tests cannot distinguish a shared dependency DAG from a traversal of
  // all its paths. Each combination below has two views of the same child, while
  // its captured instance requires B even before a bound mentioning B arrives.
  test("synthesized dependency queries do not expand shared interpretation paths"):
    val allocation = allocationCounter
    val h = new Harness
    import h.given
    val (a, b, unused) = (h.binder("A"), h.binder("B"), h.binder("Unused"))
    val a1 = h.instanceAt(a, Set.single(b))
    val b1 = h.instance(b)
    val extra = h.instance(unused)
    val leaf = h.typeOf(a).instantiate(TypeSubstitution(a1 :: Nil))
    for depth <- 8 :: 16 :: Nil do
      val root = (1 to depth).foldLeft(leaf): (child, _) =>
        val shape = TypeShape.Combined(TypeFormula.atom(child).union(TypeFormula.atom(child.withPolarity(false))))
        DeclaredType.synthesized(child.resolution, shape)
      val input = root.instantiate(TypeSubstitution(b1 :: extra :: Nil))
      val expected = root.instantiate(TypeSubstitution(b1 :: Nil))
      val repetitions = 100
      def project(): Unit =
        var index = 0
        while index < repetitions do
          assert(h.resolver.projectType(input) == expected)
          index += 1
      project()
      val before = allocation.getCurrentThreadAllocatedBytes
      project()
      val bytes = allocation.getCurrentThreadAllocatedBytes - before
      assert(bytes <= repetitions * 2048L, s"Depth $depth dependency queries allocated $bytes bytes")

  // The view count can stay linear while dependency queries traverse every path
  // through shared argument endpoints. Measure allocations for ordinary programs,
  // including first-time source analysis, independently of that view counter.
  test("nested type arguments allocate by graph size rather than binding paths"):
    val allocation = allocationCounter
    for nominal <- false :: true :: Nil; bounded <- false :: true :: Nil do
      val declaration = if nominal then "class Wrap[A](val value: A)" else "type Wrap[A] = [A]"
      val selection = if nominal then ".value" else ".0"
      def source(depth: Int): Str =
        val aliases = if bounded then (1 to depth).map: index =>
          val child = if index == 1 then "A" else s"Layer${index - 1}[A]"
          s"type Layer$index[A] = Wrap[in $child out $child]"
        else Nil
        val nested = if bounded then s"Layer$depth[A]"
          else (1 to depth).foldLeft("A")((child, _) => s"Wrap[$child]")
        s"""#lang(0.3.x)
          |$declaration
          |${aliases.mkString("\n")}
          |private fun nest[A](value: $nested): $nested = value
          |fun read[A](value: $nested): A = nest[A](value)${selection * depth}
          |""".stripMargin
      // Load the prelude and warm up the elaborator outside the measurements.
      measure("NestedArgumentsWarmup", source(4))
      for depth <- (if bounded then 8 :: 12 :: 16 :: Nil else 8 :: 16 :: 24 :: Nil) do
        val before = allocation.getCurrentThreadAllocatedBytes
        measure(s"NestedArguments$depth", source(depth))
        val bytes = allocation.getCurrentThreadAllocatedBytes - before
        // Named alias chains also repeat regularity and normalization work for
        // their shorter suffixes. Allow that polynomial cost here; the graph
        // tests below enforce linear allocation for each dependency query.
        val budget = if bounded then (depth + 1L) * (depth + 1L) * (depth + 1L) * 16384L
          else depth * 1024L * 1024L
        assert(bytes <= budget,
          s"nominal=$nominal, bounded=$bounded, depth=$depth allocated $bytes bytes")

  // Both endpoints can be identical, or distinct references to shared bindings.
  // Cold queries also traverse source dependencies; warm queries still need the
  // support of the retained binding DAG. Neither traversal may expand its paths.
  test("binding support shares cold and warm traversal work"):
    val allocation = allocationCounter
    for distinct <- false :: true :: Nil; depth <- 8 :: 16 :: 32 :: Nil do
      val h = new Harness
      import h.given
      val (a, b, unused) = (h.binder("A"), h.binder("B"), h.binder("Unused"))
      val a1 = h.instanceAt(a, Set.single(b))
      val b1 = h.instance(b)
      val extra = h.instance(unused)
      val leaf = h.typeOf(a).instantiate(TypeSubstitution(a1 :: Nil))
      val tuple = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      tuple.publish(TypeShape.Tuple(TypeShape.TupleField(h.typeOf(a).resolution, spread = false) :: Nil))
      val root = (1 to depth).foldLeft(leaf): (child, _) =>
        val output = if distinct then child.withPolarity(false) else child
        DeclaredType(tuple, Map(a -> TypeArgument(child, output)), TypeSubstitution.empty, true)(N)
      val wrapped = DeclaredType.synthesized(tuple, TypeShape.Contextual(ContextualType(root, Nil)))
      for tpe <- wrapped :: root :: Nil do
        val input = tpe.instantiate(TypeSubstitution(b1 :: extra :: Nil))
        val expected = tpe.instantiate(TypeSubstitution(b1 :: Nil))
        // Check the cold query before repeating it with source summaries cached.
        for repetitions <- 1 :: 10 :: Nil do
          val before = allocation.getCurrentThreadAllocatedBytes
          (1 to repetitions).foreach(_ => assert(h.resolver.projectType(input) == expected))
          val bytes = allocation.getCurrentThreadAllocatedBytes - before
          assert(bytes <= repetitions * (depth + 1) * 16384L,
            s"distinct=$distinct, depth=$depth, repetitions=$repetitions allocated $bytes bytes")

  test("binding support retains distinct endpoint captures and discovers late bounds"):
    val h = new Harness
    import h.given
    val (a, b, c, unused) = (h.binder("A"), h.binder("B"), h.binder("C"), h.binder("Unused"))
    val first = h.instanceAt(a, Set.single(b))
    val second = h.instanceAt(a, Set.single(c))
    val (b1, c1, extra) = (h.instance(b), h.instance(c), h.instance(unused))
    val source = h.typeOf(a)
    val input = source.instantiate(TypeSubstitution(first :: Nil))
    val output = source.instantiate(TypeSubstitution(second :: Nil))
    val pending = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val late = DeclaredType(pending, Map(a -> TypeArgument(input, output)), TypeSubstitution.empty, true)(N)
    val instances = TypeSubstitution(b1 :: c1 :: extra :: Nil)
    val original = late.instantiate(instances)
    assert(h.resolver.projectType(original) == original)
    pending.publish(TypeShape.Tuple(TypeShape.TupleField(source.resolution, spread = false) :: Nil))
    val expected = late.instantiate(TypeSubstitution(b1 :: c1 :: Nil))
    assert(h.resolver.projectType(original) == expected)
    val wrapped = DeclaredType.synthesized(pending, TypeShape.Contextual(ContextualType(late, Nil)))
    assert(h.resolver.projectType(wrapped.instantiate(instances)) == wrapped.instantiate(TypeSubstitution(b1 :: c1 :: Nil)))

  test("a substitution that a value cannot observe allocates no view"):
    val h = new Harness
    import h.given
    val (a, b) = (h.binder("A"), h.binder("B"))
    val irrelevant = TypeSubstitution(List(h.instance(b)))
    val literal = IntroShape(Term.UnitVal(), N)
    val rigid = RigidTypeShape(a, Term.UnitVal())
    val tuple = h.tuple(Set(a))
    val marked = MarkedShape(tuple, ExitMark(ResolutionBoundary(TermSymbol(syntax.Fun, N, Tree.Ident("f"))), N, NoMarks))
    val before = h.state.allocatedShapeViewCount
    (1 to 100).foreach: _ =>
      assert(h.resolver.instantiateShape(literal, irrelevant) eq literal)
      assert(h.resolver.instantiateShape(rigid, irrelevant) eq rigid)
      assert(h.resolver.instantiateShape(tuple, irrelevant) eq tuple)
      assert(h.resolver.instantiateShape(marked, irrelevant) eq marked)
    assert(h.state.allocatedShapeViewCount == before)

  // Erasing diagnostic evidence is an algebraic property of candidate keys:
  // each observation retains its witness without extending the inference graph.
  test("diagnostic witnesses do not multiply inferred values"):
    val h = new Harness
    import h.given
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    resolution.publish(TypeShape.Bottom)
    val tpe = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    val host = new TermShapeHost
    (1 to 1000).foreach: _ =>
      val reason = TypeInterfaceReason.Unavailable(Term.UnitVal())
      val view = h.resolver.instanceShape(tpe.withOrigin(S(reason)))
      assert(view.tpe.origin.contains(reason))
      host.publish(view)
    assert(host.currentShapes.size == 1)

  test("repeated substitution stabilizes on one canonical view"):
    val h = new Harness
    import h.given
    val (a, b) = (h.binder("A"), h.binder("B"))
    val substitution = TypeSubstitution(List(h.instance(a), h.instance(b)))
    val tuple = h.tuple(Set(a))
    val view = h.resolver.instantiateShape(tuple, substitution)
    val expected = TupleShape.view(tuple, TypeSubstitution(List(substitution(a))))(h.resolver)
    assert(view eq expected)
    val before = h.state.allocatedShapeViewCount
    (1 to 100).foreach: _ =>
      assert(h.resolver.instantiateShape(view, substitution) eq view)
      assert(h.resolver.instantiateShape(tuple, substitution) eq view)
      assert(h.resolver.instantiateShape(tuple, TypeSubstitution(List(substitution(a)))) eq view)
    assert(h.state.allocatedShapeViewCount == before)

  test("composed substitutions keep captured bindings and compare by effective view"):
    val h = new Harness
    import h.given
    val (a, b) = (h.binder("A"), h.binder("B"))
    val (first, second) = (h.instance(a), h.instance(a))
    val other = h.instance(b)
    val tuple = h.tuple(Set(a, b))
    val captured = h.resolver.instantiateShape(tuple, TypeSubstitution(List(first)))
    // A later binding for a captured binder is ignored; a new binder is composed.
    assert(h.resolver.instantiateShape(captured, TypeSubstitution(List(second))) eq captured)
    val composed = h.resolver.instantiateShape(captured, TypeSubstitution(List(second, other)))
    assert(composed eq h.resolver.instantiateShape(tuple, TypeSubstitution(List(first, other))))
    assert(composed eq TupleShape.view(tuple, TypeSubstitution(List(first, other)))(h.resolver))
    // The route to a view does not change its identity.
    assert(h.resolver.instantiateShape(h.resolver.instantiateShape(tuple, TypeSubstitution(List(other))), TypeSubstitution(List(first))) eq composed)

  // The bounds of an instance are templates written at its site (see
  // NewResolver.closure): selecting an instance requires the binders in scope
  // there, and their instances' sites in turn.
  test("selecting an instance requires the binders of its site, transitively"):
    val h = new Harness
    import h.given
    val (a, b, c, d) = (h.binder("A"), h.binder("B"), h.binder("C"), h.binder("D"))
    val c1 = h.instanceAt(c, Set.empty)
    val b1 = h.instanceAt(b, Set(c))
    val a1 = h.instanceAt(a, Set(b))
    val d1 = h.instanceAt(d, Set.empty)
    val tuple = h.tuple(Set(a))
    val substitution = TypeSubstitution(List(a1, b1, c1, d1))
    assert(h.resolver.instantiateShape(tuple, substitution) eq TupleShape.view(tuple, substitution.without(List(d)))(h.resolver))
    // A site of unknown scope retains everything.
    val opaque = h.state.instantiateTypeParameters(h.scheme, FlowSymbol.app(), List(a), N)(a)
    assert(h.resolver.instantiateShape(tuple, substitution.withOverrides(TypeSubstitution(List(opaque)))) eq
      TupleShape.view(tuple, substitution.withOverrides(TypeSubstitution(List(opaque))))(h.resolver))

  test("a nested value's retained instance requires its site from the enclosing value"):
    val h = new Harness
    import h.given
    val (a, b, d) = (h.binder("A"), h.binder("B"), h.binder("D"))
    val a1 = h.instanceAt(a, Set(b))
    val (a2, b1, d1) = (h.instance(a), h.instance(b), h.instance(d))
    // The field already selected a1 for A: the outer value needs B, not A.
    val field = h.instanceOf(DeclaredType(h.typeOf(a).resolution, Map.empty, TypeSubstitution(List(a1)), true)(N))
    assert(h.instancesOf(field) == Map(a -> a1))
    val tuple = h.holding(field)
    val view = h.resolver.instantiateShape(tuple, TypeSubstitution(List(a2, b1, d1)))
    assert(view eq TupleShape.view(tuple, TypeSubstitution(List(b1)))(h.resolver))
    // A captured substitution composes the same way.
    val written = h.tuple(Set(a))
    val captured = h.resolver.instantiateShape(written, TypeSubstitution(List(a1)))
    assert(h.resolver.instantiateShape(captured, TypeSubstitution(List(a2, b1, d1))) eq
      TupleShape.view(written, TypeSubstitution(List(a1, b1)))(h.resolver))

  test("a direct reference to an instance requires its site"):
    val h = new Harness
    import h.given
    val (a, b, d) = (h.binder("A"), h.binder("B"), h.binder("D"))
    val a1 = h.instanceAt(a, Set(b))
    val (b1, d1) = (h.instance(b), h.instance(d))
    val direct = h.instanceOf(h.typeOf(a1))
    assert(h.instancesOf(h.resolver.instantiateShape(direct, TypeSubstitution(List(b1, d1)))) == Map(b -> b1))
    val nested = h.holding(direct)
    assert(h.resolver.instantiateShape(nested, TypeSubstitution(List(b1, d1))) eq
      TupleShape.view(nested, TypeSubstitution(List(b1)))(h.resolver))

  test("bounds published after a view was built still resolve through its retained sites"):
    val h = new Harness
    import h.given
    val (a, b) = (h.binder("A"), h.binder("B"))
    val a1 = h.instanceAt(a, Set(b))
    val b1 = h.instance(b)
    val view = h.resolver.instantiateShape(h.instanceOf(DeclaredType(h.typeOf(a).resolution, Map.empty, TypeSubstitution(List(a1)), true)(N)), TypeSubstitution(List(b1)))
    assert(h.instancesOf(view) == Map(a -> a1, b -> b1))
    val seen = ArrayBuffer.empty[TermShape]
    h.resolver.listenInstanceViews(view)(seen += _)
    assert(seen.isEmpty)
    // A template mentioning B reaches a1 only now; B is bound later still.
    h.resolver.publishParameter(a1, h.instanceOf(h.typeOf(b)))
    assert(seen.isEmpty)
    val value = DynShape()
    h.resolver.publishParameter(b1, value)
    assert(seen.toList == List(value))

  // Applying variance must not traverse the selected endpoint, even when it
  // lies behind nested contextual references. This checks
  // allocation independently of depth; diff tests cover namespaces and witnesses.
  test("applying variance allocates independently of contextual argument depth"):
    val allocation = allocationCounter
    for depth <- 8 :: 32 :: Nil do
      val h = new Harness
      import h.given
      val leaf = h.typeOf(h.binder("A"))
      val root = (1 to depth).foldLeft(leaf): (child, _) =>
        DeclaredType.synthesized(child.resolution, TypeShape.Contextual(ContextualType(child, Nil)))
      val inputs = Vector.tabulate(4)(_ => TypeArgument.invariant(root.withPolarity(false).withPolarity(true)))
      for positive <- false :: true :: Nil do
        val parameter = TyParam(FldFlags.empty, S(positive), h.binder("T"))(N)
        val expected = h.resolver.argumentType(TypeArgument.invariant(root), parameter, root.resolution.source)
        inputs.foreach(input => assert(h.resolver.argumentType(input, parameter, root.resolution.source) == expected))
        val repetitions = 1000
        val before = allocation.getCurrentThreadAllocatedBytes
        var result = expected
        var index = 0
        while index < repetitions do
          result = h.resolver.argumentType(inputs(index % inputs.size), parameter, root.resolution.source)
          index += 1
        val bytes = allocation.getCurrentThreadAllocatedBytes - before
        assert(result == expected)
        assert(bytes <= repetitions * 512L, s"Variance at depth $depth allocated $bytes bytes")

  // Retain every returned view, so semantic key equality alone cannot hide a
  // fresh per-use wrapper or scope path on each hit of the transport cache.
  test("transported observations share views and scope paths across cache hits"):
    val h = new Harness
    import h.given
    val source = h.typeOf(h.binder("A")).resolution
    val boundary = ResolutionBoundary(TermSymbol(syntax.Fun, N, Tree.Ident("scope")))
    val site = S(FlowSymbol.app())
    val views = scala.collection.mutable.Set.empty[Identity[DeclaredType]]
    val paths = scala.collection.mutable.Set.empty[Identity[Ls[Marks]]]
    for index <- 0 until 1000 do
      val plain = DeclaredType(source, Map.empty, TypeSubstitution.empty, true)(N)
      val path = EntryMark(boundary, site, NoMarks) :: Nil
      views += new Identity(h.resolver.transportType(plain, path))
      val witnessed = plain.withOrigin(S(TypeInterfaceReason.Unrestricted(Term.UnitVal())))
      h.resolver.transportType(witnessed, path).shapes.foreach:
        case TypeShape.Contextual(reference) => paths += new Identity(reference.marks)
        case _ => fail("Expected a transported type")
    assert(views.size == 1)
    assert(paths.size == 1)

  test("transport interning projects irrelevant instances while retaining late dependencies"):
    val h = new Harness
    import h.given
    val (a, b, c, unused) = (h.binder("A"), h.binder("B"), h.binder("C"), h.binder("Unused"))
    val a1 = h.instanceAt(a, Set.single(b))
    val b1 = h.instanceAt(b, Set.single(c))
    val c1 = h.instance(c)
    val captured = h.typeOf(a).instantiate(TypeSubstitution(a1 :: Nil))
    val relevant = TypeSubstitution(List(b1, c1))
    val boundary = ResolutionBoundary(TermSymbol(syntax.Fun, N, Tree.Ident("scope")))
    val path = EntryMark(boundary, S(FlowSymbol.app()), NoMarks)
    // Interning must also project the retained source graph: the first caller's
    // irrelevant instances must not survive behind the shared transport node.
    val irrelevant = (1 to 100).iterator.map(i => h.instance(h.binder(s"Unused$i"))).toList
    val initial = relevant.withOverrides(TypeSubstitution(irrelevant))
    val canonical = h.resolver.transportType(captured.instantiate(initial), path :: Nil)
    val retainedSizes = canonical.resolution.currentShapes.collect:
      case TypeShape.Contextual(reference) => reference.tpe.instances.size
    assert(retainedSizes.nonEmpty && retainedSizes.forall(_ <= 3))
    // Only Unused varies. Keeping it in the transport key would allocate one
    // contextual reference per ambient activation before instanceShape projects it.
    (1 to 100).foreach: _ =>
      val incoming = relevant.withOverrides(TypeSubstitution(List(h.instance(a), h.instance(unused))))
      val moved = h.resolver.transportType(captured.instantiate(incoming), path :: Nil)
      assert(moved.resolution eq canonical.resolution)
    val seen = ArrayBuffer.empty[TermShape]
    h.resolver.listenInstanceViews(h.instanceOf(canonical))(seen += _)
    assert(seen.isEmpty)
    h.resolver.publishParameter(a1, h.instanceOf(h.typeOf(b)))
    h.resolver.publishParameter(b1, h.instanceOf(h.typeOf(c)))
    val value = DynShape()
    h.resolver.publishParameter(c1, value)
    assert(seen.toList.map(ShapeIdentity.key(_)) == List(ShapeIdentity.key(Marked(value, path))))

    // A forward source has no fixed support yet. Its two environments must
    // remain distinct and both must receive the target when it becomes known.
    val forward = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val pending = DeclaredType(forward, Map.empty, TypeSubstitution.empty, true)(N)
    val instances = List(h.instance(a), h.instance(a))
    val observations = instances.map: instance =>
      val moved = h.resolver.transportType(pending.instantiate(TypeSubstitution(instance :: Nil)), path :: Nil)
      val seen = ArrayBuffer.empty[TermShape]
      h.resolver.listenInstanceViews(h.instanceOf(moved))(seen += _)
      seen
    assert(observations.forall(_.isEmpty))
    forward.publish(rctx.typeParameter(a))
    instances.lazyZip(observations).foreach: (instance, seen) =>
      val late = DynShape()
      h.resolver.publishParameter(instance, late)
      assert(seen.toList.map(ShapeIdentity.key(_)) == List(ShapeIdentity.key(Marked(late, path))))
    assert(observations.forall(_.size == 1))

  test("an independent union arm shares its view cache across ambient substitutions"):
    val h = new Harness
    import h.given
    val a = h.binder("A")
    val unit = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    unit.publish(TypeShape.Unit)
    val union = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    union.publish(TypeShape.Union(h.typeOf(a).resolution, unit))
    val tpe = h.resolver.declaredType(union, Map.empty)
    def observe(): Unit =
      val seen = ArrayBuffer.empty[TermShape]
      h.resolver.listenInstanceViews(h.instanceOf(tpe.instantiate(TypeSubstitution(h.instance(a) :: Nil))))(seen += _)
      assert(seen.size == 1)
    observe()
    val listeners = unit.inferenceHost.listeners.size
    assert(listeners > 0)
    (1 to 100).foreach(_ => observe())
    assert(unit.inferenceHost.listeners.size == listeners)

  // A generic type use that omits arguments reads holes whose bounds are
  // written at the use, so its scope counts. Whether a use applies arguments is
  // recorded when the application is interpreted, not discovered by the
  // traversal that first analyzes the node (see NewResolver.dependencies).
  test("the support of a shared generic use does not depend on observation order"):
    def alias(h: Harness, suppliedAtSource: Bool): (DeclaredType, DeclaredType, VarSymbol) =
      import h.given
      val (b, formal) = (h.binder("B"), h.binder("X"))
      val symbol = TypeAliasSymbol(Tree.Ident("Identity"))
      val member = BlockMemberSymbol("Identity", Nil)
      val body = h.typeOf(formal)
      symbol.defn = S(TypeDef(N, symbol, member, List(TyParam(FldFlags.empty, N, formal)(N)), S(body.resolution.source), N, Nil)(N, N))
      // The use is written where B is in scope.
      val use = Term.UnitVal()
      h.state.recordLexicalBinders(use, Set(b))
      if suppliedAtSource then h.state.recordAppliedTypeArguments(use, 1)
      val reference = new TypeResolution(use, _ => fail("Unexpected type error"))
      reference.publish(TypeShape.Alias(symbol, S(body.resolution)))
      val application = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      application.publish(TypeShape.Applied(reference, List(TypeArgumentResolution.Type(h.typeOf(h.binder("C")).resolution))))
      (DeclaredType(reference, Map.empty, TypeSubstitution.empty, true)(N), DeclaredType(application, Map.empty, TypeSubstitution.empty, true)(N), b)
    def observe(h: Harness, tpe: DeclaredType, b: VarSymbol): Map[VarSymbol, TypeParameterInstance] =
      import h.given
      val d = h.binder("D")
      h.instancesOf(h.resolver.instantiateShape(h.instanceOf(tpe), TypeSubstitution(List(h.instance(b), h.instance(d)))))
    // Source metadata and observation order are independent. Merely reaching a
    // reference through a synthesized Applied node must not change its cached
    // support: an omitted argument still needs B, even when the application is
    // observed first. A source use recorded as fully applied needs no B in either
    // order, including when its reference is observed directly before the wrapper.
    for suppliedAtSource <- List(false, true); applicationFirst <- List(false, true) do
      val h = new Harness
      val (reference, application, b) = alias(h, suppliedAtSource)
      val observations = if applicationFirst then List(application, reference) else List(reference, application)
      val expected = if suppliedAtSource then Set.empty[VarSymbol] else Set(b)
      withClue(s"suppliedAtSource=$suppliedAtSource, applicationFirst=$applicationFirst: "):
        observations.foreach(tpe => assert(observe(h, tpe, b).keySet == expected))
