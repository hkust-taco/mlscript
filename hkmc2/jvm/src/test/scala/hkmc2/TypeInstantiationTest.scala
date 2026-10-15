package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.utils.*
import hkmc2.semantics.*


class TypeInstantiationTest extends AnyFunSuite:
  test("a definition and static site allocate their binder group once"):
    given owner: Elaborator.State = new Elaborator.State
    val state = owner.newResolverState.context
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val otherScheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(new syntax.Tree.Ident("A"))
    val b = new VarSymbol(new syntax.Tree.Ident("B"))
    val firstSite = FlowSymbol.app()
    val secondSite = FlowSymbol.app()
    val first = state.instantiateTypeParameters(scheme, firstSite, List(a, b), None)
    (1 to 1000).foreach: _ =>
      val repeated = state.instantiateTypeParameters(scheme, firstSite, List(a, b), None)
      assert(repeated(a) eq first(a))
      assert(repeated(b) eq first(b))
    assert(state.allocatedTypeInstanceCount == 2)
    val second = state.instantiateTypeParameters(scheme, secondSite, List(a, b), None)
    val other = state.instantiateTypeParameters(otherScheme, firstSite, List(a, b), None)
    assert(!(second(a) eq first(a)))
    assert(!(other(a) eq first(a)))
    assert(first(a).origin eq a)
    assert(first(b).origin eq b)
    assert(state.allocatedTypeInstanceCount == 6)
    intercept[AssertionError]:
      state.instantiateTypeParameters(scheme, firstSite, List(a), None)

  test("instances do not copy checking candidates or listeners and cannot be reinstantiated"):
    given owner: Elaborator.State = new Elaborator.State
    given state: ResolutionContext = owner.newResolverState.context
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    parameter.inferenceHost.publish(DynShape())
    parameter.subscribeToShapes(_ => ())
    val instance = state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None)(parameter)
    assert(instance.currentShapes.isEmpty)
    assert(instance.shapeListeners.isEmpty)
    assert(parameter.currentShapes.nonEmpty)
    assert(parameter.shapeListeners.nonEmpty)
    intercept[IllegalArgumentException]:
      state.instantiateTypeParameters(scheme, FlowSymbol.app(), List(instance), None)

  test("structural projections bound allocation across activation and importer views"):
    // Diff tests check recursive getter behavior; this checks that repeated
    // projections and imported activations allocate only one binder group.
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val field = BlockMemberSymbol("next", Nil)
    val site = source.fieldProjectionSite(field)
    assert(consumer.inGraph(source).fieldProjectionSite(field) eq site)
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val instances = consumer.instantiateTypeParameters(scheme, site, List(parameter), None)
    val views = List(consumer, consumer.withInstances(instances), consumer.inGraph(source),
      consumer.withInstances(instances).inGraph(source))
    (1 to 1000).foreach: _ =>
      views.foreach: view =>
        assert(view.fieldProjectionSite(field) eq site)
        assert(view.instantiateTypeParameters(scheme, view.fieldProjectionSite(field), List(parameter), None) == instances)
    assert(consumer.allocatedTypeInstanceCount == 1)
    assert(source.allocatedTypeInstanceCount == 0)

  test("consumer instantiation leaves another consumer and the source untouched"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val first = new Elaborator.State().newResolverState.context
    val second = new Elaborator.State().newResolverState.context
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val site = FlowSymbol.app()
    val left = first.instantiateTypeParameters(scheme, site, List(parameter), None)(parameter)
    val right = second.instantiateTypeParameters(scheme, site, List(parameter), None)(parameter)
    left.inferenceHost(using first).publish(DynShape())(using first)
    assert(left.currentShapes(using first).nonEmpty)
    assert(right.currentShapes(using second).isEmpty)
    assert(parameter.currentShapes(using source).isEmpty)
    assert(source.allocatedTypeInstanceCount == 0)

  test("activation views compose flatly and share their consumer's hosts"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val local = new VarSymbol(new syntax.Tree.Ident("value"))
    val first = source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None)
    val second = source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None)
    val left = source.withInstances(first)
    val right = source.withInstances(second)
    assert(left.state eq source.state)
    assert(right.state eq source.state)
    (1 to 1000).foreach: _ =>
      assert(left.withInstances(second) eq right)
      assert(right.withInstances(first) eq left)
      assert(left.withInstances(TypeSubstitution.empty) eq source)
      assert(left.inGraph(right) eq left)
    assert(local.inferenceHost(using left) eq local.inferenceHost(using right))
    assert(source.allocatedTypeInstanceCount == 2)

  test("shared resolver tables isolate mutable bookkeeping between activations and importers"):
    // Diff tests observe compiler results; they cannot detect an activation or
    // importer accidentally extending another context's mutable cache value.
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val first = source.withInstances(source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None))
    val second = source.withInstances(source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None))
    val key = new Object
    source.state.reportedArities.update(key, scala.collection.mutable.Set(0))(using source)
    first.state.reportedArities.get(key)(using first).get += 1
    assert(second.state.reportedArities.get(key)(using second).get.toSet == Set(0))
    val consumer = new Elaborator.State().newResolverState.context.inGraph(source)
    consumer.state.reportedArities.get(key)(using consumer).get += 2
    assert(source.state.reportedArities.get(key)(using source).get.toSet == Set(0))
    assert(first.state.reportedArities.get(key)(using first).get.toSet == Set(0, 1))
    assert(consumer.state.reportedArities.get(key)(using consumer).get.toSet == Set(0, 2))

  test("imported activation views retain consumer substitutions without mutating exporter hosts"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val other = new Elaborator.State().newResolverState.context
    val scheme = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val parameter = new VarSymbol(new syntax.Tree.Ident("A"))
    val local = new VarSymbol(new syntax.Tree.Ident("value"))
    val sourceSubstitution = source.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None)
    val substitution = consumer.instantiateTypeParameters(scheme, FlowSymbol.app(), List(parameter), None)
    local.inferenceHost(using source).publish(UnknownValueShape.at(Term.UnitVal()))(using source)
    val contextual = consumer.withInstances(substitution)
    val imported = contextual.inGraph(source.withInstances(sourceSubstitution))
    assert(imported.instances == substitution)
    assert(imported.withInstances(TypeSubstitution.empty) eq consumer.inGraph(source))
    (1 to 1000).foreach: _ =>
      assert(contextual.inGraph(source) eq imported)
      assert(imported.inGraph(source) eq imported)
    local.inferenceHost(using imported).publish(DynShape())(using imported)
    assert(local.currentShapes(using imported).size == 2)
    assert(local.currentShapes(using source).size == 1)
    assert(local.currentShapes(using other.inGraph(source)).size == 1)
    assert(consumer.allocatedTypeInstanceCount == 1)

  test("imported callbacks return to the consumer without growing graph-view chains"):
    val exporter = new Elaborator.State().newResolverState.context
    val middle = new Elaborator.State().newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val imported = consumer.inGraph(middle.inGraph(exporter))
    // A worksheet can observe successful values without detecting an extra
    // import-view layer per callback. Check the graph's boundedness directly.
    (1 to 1000).foreach: _ =>
      assert(imported.inGraph(consumer) eq consumer)
      assert(imported.inGraph(imported) eq imported)
