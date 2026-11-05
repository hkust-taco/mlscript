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

  test("canonical leaf comparisons allocate no traversal state"):
    val allocation = allocationCounter
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val alias = TypeAliasSymbol(syntax.Tree.Ident("Alias"))
    val witness = NamespaceWitness.Written(Term.UnitVal())
    val plans = Vector(N, S(TypeNamespaces.single(alias, witness)))
    def leaf(plan: Opt[TypeNamespaces]): DeclaredType =
      val tpe = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      plan.fold(tpe)(tpe.withNamespaces)
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
    // Equality uses the canonical reference directly, even for annotated types.
    // The fixed allowance covers counter/JIT bookkeeping, not per-comparison data.
    assert(bytes <= 4096L, s"Leaf comparisons allocated $bytes bytes")

  test("canonical DAG comparisons allocate independently of graph depth"):
    val allocation = allocationCounter
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val a = new VarSymbol(syntax.Tree.Ident("A"), mut = false)
    val b = new VarSymbol(syntax.Tree.Ident("B"), mut = false)
    def tree(depth: Int): DeclaredType =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
      (1 to depth).foldLeft(leaf): (child, _) =>
        DeclaredType(resolution, Map(a -> child, b -> child), TypeSubstitution.empty, true)(N)
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
      assert(bytes <= 4096L, s"Depth $depth comparisons allocated $bytes bytes")

  test("callable comparisons do not copy their parameter types"):
    val allocation = allocationCounter
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val tpe = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    for arity <- 1 :: 64 :: Nil do
      val parameters = List.fill(arity)(DeclaredParam(S(tpe), FldFlags.empty))
      val callable = CallableTypeShape(Term.UnitVal(), new ::(DeclaredParams(parameters, N), Nil), S(tpe), N, N, N, N)
      val left = callable.comparison
      val right = callable.copy().comparison
      val repetitions = 1000
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
      // Allow fixed comparison bookkeeping, but no list proportional to arity.
      assert(bytes <= repetitions * 64L, s"Arity $arity comparisons allocated $bytes bytes")

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

  test("annotated arguments stay local and importing their shared DAG is bounded"):
    given owner: Elaborator.State = new Elaborator.State
    val source = owner.newResolverState.context
    val consumer = new Elaborator.State().newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val alias = TypeAliasSymbol(syntax.Tree.Ident("Alias"))
    val other = TypeAliasSymbol(syntax.Tree.Ident("Other"))
    val argument = VarSymbol(syntax.Tree.Ident("A"), mut = false)
    val second = VarSymbol(syntax.Tree.Ident("B"), mut = false)
    val witness = NamespaceWitness.Written(Term.UnitVal())
    def tree(alias: TypeAliasSymbol)(using ResolutionContext): DeclaredType =
      val leaf = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
        .withNamespaces(TypeNamespaces.single(alias, witness))
      (1 to 64).foldLeft(leaf): (child, _) =>
        val parent = DeclaredType(resolution, Map(argument -> child, second -> child), TypeSubstitution.empty, true)(N)
        assert(parent.namespaces.isEmpty)
        parent
    val original = tree(alias)(using source)
    val different = tree(other)(using consumer)
    for _ <- 0 until 20 do
      val independent = tree(alias)(using consumer)
      assert(original == independent && independent == original)
      assert(original.hashCode == independent.hashCode)
      assert(original != different)
      val imported = DeclaredType(resolution, Map(argument -> original), TypeSubstitution.empty, true)(N)(using consumer)
      assert(imported.bindings(argument) == independent)
    assert(source.state.typeReferences.size == 66)
    assert(source.state.typeReferences.importedCount == 0)
    assert(consumer.state.typeReferences.size == 132)
    assert(consumer.state.typeReferences.importedCount == 65)

  test("repeated alias annotations and diagnostic views reuse canonical references"):
    given owner: Elaborator.State = new Elaborator.State
    given context: ResolutionContext = owner.newResolverState.context
    val resolution = new TypeResolution(Term.UnitVal(), _ => fail("Unexpected type error"))
    val alias = TypeAliasSymbol(syntax.Tree.Ident("Alias"))
    val witness = NamespaceWitness.Written(Term.UnitVal())
    val plain = DeclaredType(resolution, Map.empty, TypeSubstitution.empty, true)(N)
    val annotated = plain.withNamespaces(TypeNamespaces.single(alias, witness))
    var current = annotated
    for _ <- 0 until 1000 do
      current = current.withNamespaces(current.namespaces.get.through(alias, witness))
        .withOrigin(S(TypeInterfaceReason.Unrestricted(Term.UnitVal())))
      assert(current.reference eq annotated.reference)
      assert(current.withoutNamespaces.reference eq plain.reference)
    assert(context.state.typeReferences.size == 2)
