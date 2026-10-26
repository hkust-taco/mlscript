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
  // retain unrelated callers' binders, allocating over 15000 views instead of
  // about 1400. Allow headroom while checking graph size independently of the
  // machine-dependent timeout; the .mls tests cover observable behavior.
  test("FingerTreeList constructor-pattern inference stays bounded"):
    val m = measure(TestFolders.compileTestDir(os.pwd) / "FingerTreeList.mls")
    withClue(s"FingerTreeList inference: $m"):
      assert(m.largestSubstitution <= 4)
      assert(m.views < 3000)

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
      val symbol = VarSymbol(Tree.Ident(name))
      symbol.decl = S(TyParam(FldFlags.empty, N, symbol)(N))
      symbol
    def instance(binder: VarSymbol): TypeParameterInstance = instanceAt(binder, Set.empty)
    /** An instance of `binder` at a site where `site` are the binders in scope. */
    def instanceAt(binder: VarSymbol, site: Set[VarSymbol]): TypeParameterInstance =
      state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(binder), S(site))(binder)
    /** The type denoted by a binder or instance reference. */
    def typeOf(symbol: VarSymbol): DeclaredType =
      val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      resolution.publish(TypeShape.Parameter(symbol, symbol.inferenceHost))
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
      symbol.defn = S(TypeDef(symbol, member, List(TyParam(FldFlags.empty, N, formal)(N)), S(body.resolution.source), N, Nil)(N, N))
      // The use is written where B is in scope.
      val use = Term.UnitVal()
      h.state.recordLexicalBinders(use, Set(b))
      if suppliedAtSource then h.state.recordAppliedTypeArguments(use, 1)
      val reference = new TypeResolution(use, _ => fail("Unexpected type error"))
      reference.publish(TypeShape.Alias(symbol, S(body.resolution)))
      val application = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
      application.publish(TypeShape.Applied(reference, List(h.typeOf(h.binder("C")).resolution)))
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
