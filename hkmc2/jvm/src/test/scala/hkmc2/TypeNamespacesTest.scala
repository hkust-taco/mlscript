package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.syntax.Tree
import hkmc2.utils.*, shorthands.*

/** Diff tests cover resolution results. These tests check the policy algebra for
  * every provider assignment, including names absent or inaccessible in a namespace.
  */
class TypeNamespacesTest extends AnyFunSuite:
  test("normalizing priority paths preserves lookup and bounds repeated forwarding"):
    given Elaborator.State = new Elaborator.State
    val aliases = List("A", "B", "C").map(name => TypeAliasSymbol(Tree.Ident(name)))
    val witness = NamespaceWitness.Written(Term.UnitVal())
    def words(length: Int): List[List[TypeAliasSymbol]] =
      if length == 0 then List(Nil) else words(length - 1).flatMap(tail => aliases.map(_ :: tail))
    def plan(path: List[TypeAliasSymbol]): TypeNamespaces =
      path.foldRight(TypeNamespaces.empty)((alias, body) => body.through(S(alias), witness))
    def selected(plan: TypeNamespaces, available: Set[TypeAliasSymbol]): Set[TypeAliasSymbol] =
      plan.paths.flatMap((path, _) => path.aliases.find(available)).toSet
    val providers = (0 until 8).map(mask => aliases.zipWithIndex.collect:
      case (alias, index) if (mask & (1 << index)) != 0 => alias
    .toSet)
    for length <- 0 to 6; path <- words(length) do
      val normalized = plan(path)
      assert(normalized.paths.forall((p, _) => p.aliases.size <= aliases.size))
      for available <- providers do
        assert(selected(normalized, available) == path.find(available).toSet)
      assert(normalized.union(normalized).key == normalized.key)
      for alias <- aliases do
        assert(normalized.through(S(alias), witness).through(S(alias), witness).key ==
          normalized.through(S(alias), witness).key)
    // Each component chooses independently; an outer alias takes priority over both.
    for left <- words(3); right <- words(3); available <- providers do
      val combined = plan(left).union(plan(right))
      assert(selected(combined, available) == (left.find(available).toSet ++ right.find(available).toSet))
      val preferred = combined.through(S(aliases.head), witness)
      val expected = if available(aliases.head) then Set(aliases.head) else selected(combined, available)
      assert(selected(preferred, available) == expected)
