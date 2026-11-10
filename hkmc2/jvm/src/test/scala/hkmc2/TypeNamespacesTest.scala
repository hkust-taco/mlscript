package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.syntax.Tree
import hkmc2.utils.*, shorthands.*

/** Diff tests cover resolution results. This checks priority and idempotence
  * for every provider assignment, including absent or inaccessible names.
  */
class TypeNamespacesTest extends AnyFunSuite:
  test("local alias annotations preserve priority and bound repeated forwarding"):
    given Elaborator.State = new Elaborator.State
    val aliases = List("A", "B", "C").map(name => TypeAliasSymbol(Tree.Ident(name)))
    val witness = NamespaceWitness.Written(Term.UnitVal())
    def words(length: Int): List[List[TypeAliasSymbol]] =
      if length == 0 then List(Nil) else words(length - 1).flatMap(tail => aliases.map(_ :: tail))
    def plan(path: List[TypeAliasSymbol]): Opt[TypeNamespaces] =
      path.foldRight[Opt[TypeNamespaces]](N): (alias, body) =>
        S(body.fold(TypeNamespaces.single(alias, witness))(_.through(alias, witness)))
    val providers = (0 until 8).map(mask => aliases.zipWithIndex.collect:
      case (alias, index) if (mask & (1 << index)) != 0 => alias
    .toSet)
    for length <- 0 to 6; path <- words(length) do
      val normalized = plan(path).fold(Nil)(_.aliases)
      assert(normalized.size <= aliases.size)
      for available <- providers do
        assert(normalized.find(available) == path.find(available))
      for alias <- aliases do
        assert(plan(alias :: alias :: path).get.aliases == plan(alias :: path).get.aliases)
    for outer <- words(3); inner <- words(3) do
      assert(plan(inner).get.precededBy(plan(outer).get).aliases == plan(outer ::: inner).get.aliases)
