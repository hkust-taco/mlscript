package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*, shorthands.*
import syntax.Tree


/** Diff tests cannot observe whether equal literals reuse a symbol owned by another
  * compilation, or whether interning changes the source span of a flow occurrence.
  */
class LiteralSymbolCacheTest extends AnyFunSuite:
  test("literal interning preserves identity within each compilation and isolates owners and spans"):
    val firstState = new Elaborator.State
    val secondState = new Elaborator.State
    val firstOrigin = Origin(io.Path("/First.mls"), 0, new FastParseHelpers("42 42"))
    val secondOrigin = Origin(io.Path("/Second.mls"), 0, new FastParseHelpers("42"))
    val firstLiteral = new Tree.IntLit(42).withLoc(0, 2, firstOrigin)
    val repeatedLiteral = new Tree.IntLit(42).withLoc(3, 5, firstOrigin)
    val secondLiteral = new Tree.IntLit(42).withLoc(0, 2, secondOrigin)

    val first = LitSymbol(firstLiteral)(using firstState)
    val second = LitSymbol(secondLiteral)(using secondState)
    val repeated = LitSymbol(repeatedLiteral)(using firstState)
    assert(first eq repeated)
    assert(first ne second)
    assert(first.getState eq firstState)
    assert(second.getState eq secondState)
    assert(LitSymbol(firstLiteral)(using secondState) eq second)
    assert(first.toLoc == firstLiteral.toLoc)
    assert(second.toLoc == secondLiteral.toLoc)

    // The interned symbol has one representative span; each producer must still
    // identify its own occurrence, including repeated literals in the same file.
    val firstOccurrence = flow.Producer.Ctor(first, Nil)(Term.Lit(firstLiteral))
    val repeatedOccurrence = flow.Producer.Ctor(repeated, Nil)(Term.Lit(repeatedLiteral))
    assert(firstOccurrence.toLoc == firstLiteral.toLoc)
    assert(repeatedOccurrence.toLoc == repeatedLiteral.toLoc)
