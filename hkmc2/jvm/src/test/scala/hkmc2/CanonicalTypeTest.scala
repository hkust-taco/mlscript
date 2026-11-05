package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*, shorthands.*


/** Diff tests cannot distinguish a shared type DAG from exponentially repeated
  * equality work, measure comparison allocation, or observe whether importing it
  * extends the exporter's tables.
  */
class CanonicalTypeTest extends AnyFunSuite:
  private def allocationCounter: com.sun.management.ThreadMXBean =
    val allocation = java.lang.management.ManagementFactory.getThreadMXBean match
      case bean: com.sun.management.ThreadMXBean if bean.isThreadAllocatedMemorySupported => bean
      case _ => cancel("This JVM does not expose thread allocation counters")
    allocation.setThreadAllocatedMemoryEnabled(true)
    allocation

  test("leaf observation comparisons keep scratch allocation bounded"):
    val allocation = allocationCounter
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val alias = TypeAliasSymbol(syntax.Tree.Ident("Alias"))
    val witness = NamespaceWitness.Written(Term.UnitVal())
    val plans = Vector(N, S(TypeNamespaces.empty), S(TypeNamespaces.empty.through(S(alias), witness)))
    def leaf(plan: Opt[TypeNamespaces]): DeclaredType.Observation =
      val tpe = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      plan.fold(tpe)(tpe.withNamespaces).observation
    val left = plans.map(leaf)
    val right = plans.map(leaf)
    val repetitions = 10000
    def compare(): Int =
      var equal = 0
      var index = 0
      while index < repetitions do
        val position = index % left.size
        if left(position) == right(position) then equal += 1
        index += 1
      equal
    assert(compare() == repetitions)
    val before = allocation.getCurrentThreadAllocatedBytes
    val equal = compare()
    val bytes = allocation.getCurrentThreadAllocatedBytes - before
    assert(equal == repetitions)
    // Allow small closures and collection iterators, without requiring JIT escape
    // analysis. Two default-sized traversal maps per leaf exceed this allowance.
    assert(bytes <= repetitions * 256L, s"Leaf comparisons allocated $bytes bytes")

  test("shared observation comparisons keep allocation proportional to distinct pairs"):
    val allocation = allocationCounter
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(syntax.Tree.Ident("A"), mut = false)
    val b = new VarSymbol(syntax.Tree.Ident("B"), mut = false)
    def tree(depth: Int): DeclaredType.Observation =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      (1 to depth).foldLeft(leaf): (child, _) =>
        DeclaredType(resolution, Map(a -> child, b -> child), TypeSubstitution.empty, true)(N)
      .observation
    for depth <- 16 :: 64 :: Nil do
      val left = tree(depth)
      val right = tree(depth)
      val repetitions = 100
      def compare(): Int =
        var equal = 0
        var index = 0
        while index < repetitions do
          if left == right then equal += 1
          index += 1
        equal
      assert(compare() == repetitions)
      val before = allocation.getCurrentThreadAllocatedBytes
      val equal = compare()
      val bytes = allocation.getCurrentThreadAllocatedBytes - before
      assert(equal == repetitions)
      // A pair needs a small memo entry and traversal bookkeeping. Allow a generous
      // fixed cost per node, while rejecting a default-sized hash table for every pair.
      assert(bytes <= repetitions * (depth + 1) * 512L, s"Depth $depth comparisons allocated $bytes bytes")

  test("independent constructions share a bounded canonical type DAG"):
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(syntax.Tree.Ident("A"), mut = false)
    val b = new VarSymbol(syntax.Tree.Ident("B"), mut = false)
    def tree(): DeclaredType =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      (1 to 64).foldLeft(leaf): (child, _) =>
        DeclaredType(resolution, Map(a -> child, b -> child), TypeSubstitution.empty, true)(N)
    val first = tree()
    (1 to 20).foreach: _ =>
      val repeated = tree()
      assert(first == repeated && first.hashCode == repeated.hashCode)
      assert(first.observation == repeated.observation)
    assert(context.state.typeReferences.size == 65)

  test("cross-unit equality and import traverse shared children without expanding paths"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val other = new Elaborator.State().newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(syntax.Tree.Ident("A"), mut = false)
    val b = new VarSymbol(syntax.Tree.Ident("B"), mut = false)
    def tree()(using ResolutionContext): DeclaredType =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      (1 to 64).foldLeft(leaf): (child, _) =>
        DeclaredType(resolution, Map(a -> child, b -> child), TypeSubstitution.empty, true)(N)
    val original = tree()(using source)
    val independent = tree()(using other)
    assert(original == independent && independent == original)
    assert(original.hashCode == independent.hashCode)
    assert(original.observation == independent.observation)
    (1 to 20).foreach: _ =>
      val imported = DeclaredType(resolution, Map(a -> original, b -> independent), TypeSubstitution.empty, true)(N)(using consumer)
      val repeated = DeclaredType(resolution, Map(b -> original, a -> independent), TypeSubstitution.empty, true)(N)(using consumer)
      assert(imported == repeated)
      assert(imported.observation == repeated.observation)
    assert(consumer.state.typeReferences.size == 66)
    assert(consumer.state.typeReferences.importedCount == 130)
    assert(source.state.typeReferences.size == 65)
    assert(source.state.typeReferences.importedCount == 0)
    assert(other.state.typeReferences.size == 65)
    assert(other.state.typeReferences.importedCount == 0)

  test("shared namespace targets compare across units without expanding paths"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val aliases = Vector("Left", "Right", "Leaf", "Other").map(name => TypeAliasSymbol(syntax.Tree.Ident(name)))
    val witness = NamespaceWitness.Written(Term.UnitVal())
    def tree(leaf: TypeAliasSymbol, reverse: Bool)(using ResolutionContext): DeclaredType =
      def tpe = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      val initial = tpe.withNamespaces(TypeNamespaces.empty.through(S(leaf), witness))
      (1 to 64).foldLeft(initial): (child, _) =>
        val target = TypeNamespaces.target(TypeNamespaces.Target.Type(child.observation), witness)
        val left = target.through(S(aliases(0)), witness)
        val right = target.through(S(aliases(1)), witness)
        tpe.withNamespaces(if reverse then right.union(left) else left.union(right))
    val original = tree(aliases(2), false)(using source).observation
    val different = tree(aliases(3), false)(using consumer).observation
    // There are only 65 observations per construction, but two namespace paths
    // point to every child. Restarting equality at each target expands 2^64 paths.
    for _ <- 0 until 20 do
      val independent = tree(aliases(2), true)(using consumer).observation
      assert(original == independent && independent == original)
      assert(original.hashCode == independent.hashCode)
      assert(original != different)
    assert(source.state.typeReferences.size == 1)
    assert(consumer.state.typeReferences.size == 1)
