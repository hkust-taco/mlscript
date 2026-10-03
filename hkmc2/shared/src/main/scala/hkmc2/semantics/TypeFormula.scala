package hkmc2
package semantics

/** A union of intersections, with absorption. This is the free distributive
  * lattice over A: no nominal subtyping, disjointness, or inference bounds are
  * consulted. In particular, an atom can be a still-live inference reference.
  * For a finite set of atoms there are finitely many formulas, even when recursive
  * substitutions alternate union and intersection arbitrarily often.
  */
final case class TypeFormula[A] private (clauses: Set[Set[A]])(val orderedAtoms: Vector[A]):
  // The second parameter list is not part of case-class equality. Preserve the
  // first source order for observation and diagnostics without distinguishing
  // equal formulas merely because their operands were written in another order.
  def union(that: TypeFormula[A]): TypeFormula[A] = TypeFormula.normalized(clauses ++ that.clauses, orderedAtoms ++ that.orderedAtoms)
  def intersection(that: TypeFormula[A]): TypeFormula[A] =
    TypeFormula.normalized(for left <- clauses; right <- that.clauses yield left ++ right, orderedAtoms ++ that.orderedAtoms)
  def map[B](f: A => B): TypeFormula[B] =
    val mapped = orderedAtoms.map(atom => atom -> f(atom)).toMap
    TypeFormula.normalized(clauses.map(_.map(mapped)), orderedAtoms.map(mapped))
  def atoms: Set[A] = clauses.flatten

object TypeFormula:
  def atom[A](value: A): TypeFormula[A] = TypeFormula(Set(Set(value)))(Vector(value))
  def top[A]: TypeFormula[A] = TypeFormula(Set(Set.empty))(Vector.empty)
  def bottom[A]: TypeFormula[A] = TypeFormula(Set.empty)(Vector.empty)
  private def normalized[A](clauses: Set[Set[A]], order: Vector[A]): TypeFormula[A] =
    val result = clauses.filterNot(clause => clauses.exists(other => other != clause && other.subsetOf(clause)))
    val atoms = result.flatten
    TypeFormula(result)(order.distinct.filter(atoms))
