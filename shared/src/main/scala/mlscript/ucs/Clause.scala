package mlscript.ucs

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.mutable.Buffer

/**
  * A `Clause` represents a minimal unit of logical predicate in the UCS.
  * There are three kinds of clauses: boolean test, class match, and tuple match.
  */
abstract class Clause {
  /**
    * Local interleaved let bindings declared before this condition.
    */
  var bindings: Ls[(Bool, Var, Term)] = Nil

  /**
    * Locations of terms that build this `Clause`.
    *
    * @return
    */
  val locations: Ls[Loc]
}

object Clause {
  final case class MatchClass(
    scrutinee: Scrutinee,
    className: Var,
    fields: Ls[Str -> Var]
  )(override val locations: Ls[Loc]) extends Clause

  final case class MatchTuple(
    scrutinee: Scrutinee,
    arity: Int,
    fields: Ls[Str -> Var]
  )(override val locations: Ls[Loc]) extends Clause

  final case class BooleanTest(test: Term)(override val locations: Ls[Loc]) extends Clause

  def showBindings(bindings: Ls[(Bool, Var, Term)]): Str =
    bindings match {
      case Nil => ""
      case bindings => bindings.map {
        case (_, Var(name), _) => name
      }.mkString("(", ", ", ")")
    }


  def showClauses(clauses: Iterable[Clause]): Str = {
    clauses.iterator.map { clause =>
      (clause match {
        case Clause.BooleanTest(test) => s"«$test»"
        case Clause.MatchClass(scrutinee, Var(className), fields) =>
          s"«$scrutinee is $className»"
        case Clause.MatchTuple(scrutinee, arity, fields) =>
          s"«$scrutinee is Tuple#$arity»"
      }) + (if (clause.bindings.isEmpty) "" else " with " + showBindings(clause.bindings))
    }.mkString("", " and ", "")
  }

  def print(println: (=> Any) => Unit, conjunctions: Iterable[Conjunction -> Term]): Unit = {
    println("Flattened conjunctions")
    conjunctions.foreach { case Conjunction(clauses, trailingBindings) -> term =>
      println("+ " + showClauses(clauses) + {
        (if (trailingBindings.isEmpty) "" else " ") +
          showBindings(trailingBindings) +
          s" => $term"
      })
    }
  }
}
