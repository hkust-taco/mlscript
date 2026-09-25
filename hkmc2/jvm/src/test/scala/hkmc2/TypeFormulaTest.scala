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

  test("all three-atom formulas retain their meaning when substitution identifies atoms"):
    // Enumerate every DNF over three atoms, including the empty clause (top)
    // and no clauses (bottom). This checks absorption after a non-injective map,
    // which recursive substitutions can cause even if the source was reduced.
    val clauses = (0 until 8).map: bits =>
      (0 until 3).filter(atom => (bits & (1 << atom)) != 0).foldLeft(TypeFormula.top[Int]): (clause, atom) =>
        clause.intersection(TypeFormula.atom(atom))
    val formulas = (0 until 256).map: bits =>
      clauses.zipWithIndex.filter((_, index) => (bits & (1 << index)) != 0).foldLeft(TypeFormula.bottom[Int]):
        case (formula, (clause, _)) => formula.union(clause)
    .distinct
    assert(formulas.size == 20)
    for formula <- formulas; a <- 0 until 3; b <- 0 until 3; c <- 0 until 3 do
      val substitution = Vector(a, b, c)
      val mapped = formula.map(substitution)
      assert(mapped.orderedAtoms.toSet == mapped.atoms)
      assert(mapped.orderedAtoms.distinct == mapped.orderedAtoms)
      val second = Vector(1, 1, 0)
      assert(mapped.map(second) == formula.map(atom => second(substitution(atom))))
      for assignment <- 0 until 8 do
        val expected = formula.clauses.exists(_.forall(atom => (assignment & (1 << substitution(atom))) != 0))
        val actual = mapped.clauses.exists(_.forall(atom => (assignment & (1 << atom)) != 0))
        assert(actual == expected)
