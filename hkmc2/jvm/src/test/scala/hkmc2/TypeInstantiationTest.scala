package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.utils.*
import hkmc2.semantics.*


class TypeInstantiationTest extends AnyFunSuite:
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
