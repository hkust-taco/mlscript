package hkmc2
package codegen

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.utils.*, shorthands.*


/** Unit tests for the resource-ness dimension of [[ErasedType]].
  *
  * These pure functions are tested directly rather than through diff-tests because no `.mls` source can produce
  * a resource type yet: there is no syntax for one, so every `rsc` reaching the IR is still `S(false)` or `N`.
  */
class ErasedTypeRscTests extends AnyFunSuite:

  private val `rsc`: Opt[Bool] = S(true)
  private val `non-rsc`: Opt[Bool] = S(false)
  private val `rsc?`: Opt[Bool] = N

  test("lubRsc keeps a resource-ness both sides agree on"):
    assert(ErasedType.lubRsc(`rsc`, `rsc`) == `rsc`)
    assert(ErasedType.lubRsc(`non-rsc`, `non-rsc`) == `non-rsc`)
    assert(ErasedType.lubRsc(`rsc?`, `rsc?`) == `rsc?`)

  test("lubRsc joins a disagreement to the undetermined top"):
    assert(ErasedType.lubRsc(`rsc`, `non-rsc`) == `rsc?`)
    assert(ErasedType.lubRsc(`non-rsc`, `rsc`) == `rsc?`)

  test("lubRsc is absorbed by the undetermined top"):
    assert(ErasedType.lubRsc(`rsc?`, `rsc`) == `rsc?`)
    assert(ErasedType.lubRsc(`rsc`, `rsc?`) == `rsc?`)
    assert(ErasedType.lubRsc(`rsc?`, `non-rsc`) == `rsc?`)
    assert(ErasedType.lubRsc(`non-rsc`, `rsc?`) == `rsc?`)

  test("needsRscCast: no cast when the layouts already agree"):
    assert(ErasedType.needsRscCast(`rsc`, `rsc`) == S(false))
    assert(ErasedType.needsRscCast(`non-rsc`, `non-rsc`) == S(false))
    assert(ErasedType.needsRscCast(`rsc?`, `rsc?`) == S(false))

  test("needsRscCast widens a known layout into the undetermined one for free"):
    assert(ErasedType.needsRscCast(`rsc`, `rsc?`) == S(false))
    assert(ErasedType.needsRscCast(`non-rsc`, `rsc?`) == S(false))

  test("needsRscCast narrows out of the undetermined layout with a runtime test"):
    assert(ErasedType.needsRscCast(`rsc?`, `rsc`) == S(true))
    assert(ErasedType.needsRscCast(`rsc?`, `non-rsc`) == S(true))

  test("needsRscCast rejects a coercion between the two layouts"):
    assert(ErasedType.needsRscCast(`rsc`, `non-rsc`) == N)
    assert(ErasedType.needsRscCast(`non-rsc`, `rsc`) == N)

end ErasedTypeRscTests
