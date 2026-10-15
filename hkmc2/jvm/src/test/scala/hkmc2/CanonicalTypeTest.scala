package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*, shorthands.*


/** Diff tests cannot distinguish a shared type DAG from exponentially repeated
  * equality work, or observe whether importing it extends the exporter's tables.
  */
class CanonicalTypeTest extends AnyFunSuite:
  test("independent constructions share a bounded canonical type DAG"):
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(syntax.Tree.Ident("A"))
    val b = new VarSymbol(syntax.Tree.Ident("B"))
    def tree(): DeclaredType =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      (1 to 64).foldLeft(leaf): (child, _) =>
        DeclaredType(resolution, Map(a -> child, b -> child), TypeSubstitution.empty, true)(N)
    val first = tree()
    (1 to 20).foreach: _ =>
      val repeated = tree()
      assert(first == repeated && first.hashCode == repeated.hashCode)
    assert(context.state.typeReferences.size == 65)

  test("cross-unit equality and import traverse shared children without expanding paths"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val other = new Elaborator.State().newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(syntax.Tree.Ident("A"))
    val b = new VarSymbol(syntax.Tree.Ident("B"))
    def tree()(using ResolutionContext): DeclaredType =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      (1 to 64).foldLeft(leaf): (child, _) =>
        DeclaredType(resolution, Map(a -> child, b -> child), TypeSubstitution.empty, true)(N)
    val original = tree()(using source)
    val independent = tree()(using other)
    assert(original == independent && independent == original)
    assert(original.hashCode == independent.hashCode)
    (1 to 20).foreach: _ =>
      val imported = DeclaredType(resolution, Map(a -> original, b -> independent), TypeSubstitution.empty, true)(N)(using consumer)
      val repeated = DeclaredType(resolution, Map(b -> original, a -> independent), TypeSubstitution.empty, true)(N)(using consumer)
      assert(imported == repeated)
    assert(consumer.state.typeReferences.size == 66)
    assert(consumer.state.typeReferences.importedCount == 130)
    assert(source.state.typeReferences.size == 65)
    assert(source.state.typeReferences.importedCount == 0)
    assert(other.state.typeReferences.size == 65)
    assert(other.state.typeReferences.importedCount == 0)
