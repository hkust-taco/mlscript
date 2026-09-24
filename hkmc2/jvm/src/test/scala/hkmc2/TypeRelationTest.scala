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
      DeclaredType(resolution, Map.empty, Map.empty)
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

  test("each concrete upper target receives later bounds and a union stays whole"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val one = h.tpe(TypeShape.Unit)
    val two = h.tpe(TypeShape.Abstract)
    val union = h.tpe(TypeShape.Union(one.resolution, two.resolution))
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

  test("reverse relations retain each endpoint's activation and exclude another caller"):
    val h = new Harness
    import h.given
    val (a, at) = h.parameter("A")
    val (b, bt) = h.parameter("B")
    val source = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("source")))
    val target = ResolutionBoundary(TermSymbol(Fun, N, Tree.Ident("target")))
    val site = FlowSymbol.app()
    val other = FlowSymbol.app()
    val sourceMarks = ExitMark(source, S(site), NoMarks) :: Nil
    val targetMarks = ExitMark(target, S(site), NoMarks) :: Nil
    val ar = ContextualType(at, sourceMarks)
    val br = ContextualType(bt, targetMarks)
    h.resolver.constrainTypes(ar, br)
    h.resolver.constrainTypes(br, ar)
    val seen = h.observe(ar)
    val accepted = IntroShape(Term.UnitVal(), N)
    h.resolver.publishParameter(b, accepted.enter(targetMarks))
    h.resolver.publishParameter(b, MarkedShape.enter(DynShape(), target, S(other)))
    assert(seen.toList == List(accepted))

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
