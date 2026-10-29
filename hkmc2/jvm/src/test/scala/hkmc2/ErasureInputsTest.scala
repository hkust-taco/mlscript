package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*

/** Diff tests exercise representations. This checks the separate ownership property:
  * consumers and later worksheet blocks cannot mutate completed observation snapshots.
  */
class ErasureInputsTest extends AnyFunSuite:
  test("completed observations are isolated from worksheet and import consumers"):
    given owner: Elaborator.State = new Elaborator.State
    given defining: ResolutionContext = owner.newResolverState.context
    val inputs = owner.newResolverState.erasureInputs
    val symbol = VarSymbol(new syntax.Tree.Ident("value"), mut = true)
    val source = new TermShapeHost
    inputs.register(symbol)(source.subscribeToShapes)
    val initial = DynShape()
    source.publish(initial)
    defining.completeBlock(Term.UnitVal())
    val snapshot = inputs.shapes(symbol)
    val first = new Elaborator.State().newResolverState.context
    val second = new Elaborator.State().newResolverState.context
    val later = UnknownValueShape.at(Term.UnitVal())
    val other = UnknownValueShape.at(Term.Lit(syntax.Tree.IntLit(1)))
    source.publish(later)(using first)
    source.publish(other)(using second)
    source.publish(other)(using defining)
    assert(source.currentShapes(using first).toSet == Set(initial, later))
    assert(source.currentShapes(using second).toSet == Set(initial, other))
    assert(source.currentShapes(using defining).toSet == Set(initial, other))
    assert(snapshot == List(initial))
    assert(inputs.shapes(symbol) == snapshot)
