package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite


class TypeFormulaTest extends AnyFunSuite:
  test("lattice normalization preserves Boolean meanings and identifies equal formulas"):
    val a = TypeFormula.atom(0)
    val b = TypeFormula.atom(1)
    val c = TypeFormula.atom(2)
    val atoms = List(a, b, c, TypeFormula.top[Int], TypeFormula.bottom[Int])
    val formulas = (atoms ++ (for left <- atoms; right <- atoms; union <- List(false, true)
      yield if union then left.union(right) else left.intersection(right))).distinct
    def truthTable(formula: TypeFormula[Int]): List[Boolean] = (0 until 8).toList.map: assignment =>
      formula.clauses.exists(_.forall(atom => (assignment & (1 << atom)) != 0))
    val results = for left <- formulas; right <- formulas yield
      val union = left.union(right)
      val intersection = left.intersection(right)
      assert(truthTable(union) == truthTable(left).zip(truthTable(right)).map(_ || _))
      assert(truthTable(intersection) == truthTable(left).zip(truthTable(right)).map(_ && _))
      List(union, intersection)
    results.flatten.groupBy(truthTable).values.foreach(equal => assert(equal.distinct.size == 1))
    assert(a.union(a.intersection(b)) == a)
    assert(a.intersection(b.union(c)) == a.intersection(b).union(a.intersection(c)))
    assert(a.union(b) == b.union(a))
    assert(a.union(b).hashCode == b.union(a).hashCode)
    assert(a.union(b).orderedAtoms == Vector(0, 1))
    assert(b.union(a).orderedAtoms == Vector(1, 0))
    assert(a.union(a.intersection(b)).orderedAtoms == Vector(0))

  test("alternating recursive substitutions saturate without accumulating syntax"):
    val a = TypeFormula.atom("A")
    val b = TypeFormula.atom("B")
    val c = TypeFormula.atom("C")
    var value = a
    val expected = a.union(b).intersection(c)
    (1 to 1000).foreach: _ =>
      value = value.union(b).intersection(c)
      assert(value == expected)
