package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.utils.*
import hkmc2.semantics.*


class TypeInstantiationTest extends AnyFunSuite:
  private def allocatedInstances(source: String): Int =
    import io.PlatformPath.given
    val directory = os.temp.dir(prefix = "call-site-instances-")
    val file: io.Path = directory / "Library.mls"
    os.write(directory / "Library.mls", "#lang(0.3.x, strictResolution: true)\n" + source)
    try
      val paths = TestFolders.compilerPaths(os.pwd)
      val compiler = CompilerCtx.fresh(io.FileSystem.default, paths,
        Config.default(TestFolders.mainTestDir(os.pwd)))
      given DebugPrinter = new DebugPrinter
      given TL = new TraceLogger:
        override def doTrace: Boolean = false
      given Raise = diagnostic => fail(diagnostic.theMsg)
      val prelude = compiler.getPrelude(paths.preludeFile)
      val artifact = compiler.getElaboratedBlock(file, prelude.ctx)
      assert(prelude.state.newResolverState.allocatedTypeInstanceCount == 0)
      artifact.state.newResolverState.allocatedTypeInstanceCount
    finally os.remove.all(directory)

  test("polymorphic declaration calls allocate by application rather than shared reference"):
    assert(allocatedInstances(
      """|module Library with
         |  fun identity[A](x: A): A = x
         |  val shared = identity
         |  val first = shared(1)
         |  val second = shared("two")
         |""".stripMargin) == 2)

  test("constructor instances belong to the first term application, including stored new recipes"):
    val cases = List(
      """|class Box[T](val item: T)
         |private val specialized = Box[Int]
         |private val deferred = new Box[Int]
         |""".stripMargin -> 0,
      """|class Box[T](val item: T)
         |private val shared = Box
         |private val specialized = shared[Int]
         |private val direct = specialized(1)
         |private val explicit = new specialized(2)
         |""".stripMargin -> 2,
      """|class Box[T](val item: T)
         |private val deferred = new Box[Int]
         |private val first = deferred(1)
         |private val second = deferred(2)
         |""".stripMargin -> 2,
      """|class Box[T](val item: T)(val other: Int)
         |private val partial = new Box[Int](1)
         |private val first = partial(2)
         |private val second = partial(3)
         |""".stripMargin -> 1,
      """|class Box[T] with
         |  fun identity(x: T): T = x
         |private val first = new Box[Int]
         |private val second = new Box[Str]
         |""".stripMargin -> 2)
    cases.foreach: (source, count) =>
      withClue(source):
        assert(allocatedInstances(source) == count)

  test("a definition and static site allocate their binder group once"):
    given owner: Elaborator.State = new Elaborator.State
    val state = owner.newResolverState
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val otherScheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(new syntax.Tree.Ident("A"))
    val b = new VarSymbol(new syntax.Tree.Ident("B"))
    val firstSite = FlowSymbol.app()
    val secondSite = FlowSymbol.app()
    val first = state.instantiateTypeParameters(scheme, firstSite, List(a, b))
    (1 to 1000).foreach: _ =>
      val repeated = state.instantiateTypeParameters(scheme, firstSite, List(a, b))
      assert(repeated(a) eq first(a))
      assert(repeated(b) eq first(b))
    assert(state.allocatedTypeInstanceCount == 2)
    val second = state.instantiateTypeParameters(scheme, secondSite, List(a, b))
    val other = state.instantiateTypeParameters(otherScheme, firstSite, List(a, b))
    assert(!(second(a) eq first(a)))
    assert(!(other(a) eq first(a)))
    assert(first(a).origin eq a)
    assert(first(b).origin eq b)
    assert(state.allocatedTypeInstanceCount == 6)
    intercept[AssertionError]:
      state.instantiateTypeParameters(scheme, firstSite, List(a))

  test("instances do not copy checking candidates or listeners and cannot be reinstantiated"):
    given owner: Elaborator.State = new Elaborator.State
    given state: NewResolverState = owner.newResolverState
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    parameter.inferenceHost.publish(DynShape())
    parameter.subscribeToShapes(_ => ())
    val instance = state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter))(parameter)
    assert(instance.currentShapes.isEmpty)
    assert(instance.shapeListeners.isEmpty)
    assert(parameter.currentShapes.nonEmpty)
    assert(parameter.shapeListeners.nonEmpty)
    intercept[IllegalArgumentException]:
      state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(instance))

  test("consumer instantiation leaves another consumer and the source untouched"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState
    val first = new Elaborator.State().newResolverState
    val second = new Elaborator.State().newResolverState
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val site = FlowSymbol.app()
    val left = first.instantiateTypeParameters(scheme, site, List(parameter))(parameter)
    val right = second.instantiateTypeParameters(scheme, site, List(parameter))(parameter)
    left.inferenceHost(using first).publish(DynShape())(using first)
    assert(left.currentShapes(using first).nonEmpty)
    assert(right.currentShapes(using second).isEmpty)
    assert(parameter.currentShapes(using source).isEmpty)
    assert(source.allocatedTypeInstanceCount == 0)

  test("activation views compose flatly and share their consumer's hosts"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val local = new VarSymbol(new syntax.Tree.Ident("value"))
    val first = source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter))
    val second = source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter))
    val left = source.withInstances(first)
    val right = source.withInstances(second)
    (1 to 1000).foreach: _ =>
      assert(left.withInstances(second) eq right)
      assert(right.withInstances(first) eq left)
      assert(left.withInstances(Map.empty) eq source)
      assert(left.inGraph(right) eq left)
    assert(local.inferenceHost(using left) eq local.inferenceHost(using right))
    assert(source.allocatedTypeInstanceCount == 2)

  test("imported activation views retain consumer substitutions without mutating exporter hosts"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState
    val consumer = new Elaborator.State().newResolverState
    val other = new Elaborator.State().newResolverState
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val local = new VarSymbol(new syntax.Tree.Ident("value"))
    val sourceSubstitution = source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter))
    val substitution = consumer.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter))
    local.inferenceHost(using source).publish(UnknownValueShape.at(Term.UnitVal()))(using source)
    val contextual = consumer.withInstances(substitution)
    val imported = contextual.inGraph(source.withInstances(sourceSubstitution))
    assert(imported.instances == substitution)
    assert(imported.withInstances(Map.empty) eq consumer.inGraph(source))
    (1 to 1000).foreach: _ =>
      assert(contextual.inGraph(source) eq imported)
      assert(imported.inGraph(source) eq imported)
    local.inferenceHost(using imported).publish(DynShape())(using imported)
    assert(local.currentShapes(using imported).size == 2)
    assert(local.currentShapes(using source).size == 1)
    assert(local.currentShapes(using other.inGraph(source)).size == 1)
    assert(consumer.allocatedTypeInstanceCount == 1)
