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
  var locations: Ls[Loc] = Nil
}

object Clause {
  final case class MatchClass(
    scrutinee: Scrutinee,
    className: Var,
    fields: Ls[Str -> Var]
  ) extends Clause

  final case class MatchTuple(
    scrutinee: Scrutinee,
    arity: Int,
    fields: Ls[Str -> Var]
  ) extends Clause

  final case class BooleanTest(test: Term) extends Clause

  // Make it a class, and then include methods in `Conjunction`?
  type Conjunction = (Ls[Clause], Ls[(Bool, Var, Term)])

  def print(println: (=> Any) => Unit, cnf: Ls[Conjunction -> Term]): Unit = {
    def showBindings(bindings: Ls[(Bool, Var, Term)]): Str =
      bindings match {
        case Nil => ""
        case bindings => bindings.map {
          case (_, Var(name), _) => name
        }.mkString("(", ", ", ")")
      }

    println("Flattened conjunctions")
    cnf.foreach { case ((conditions, tailBindings), term) =>
      println("+ " + conditions.iterator.map { condition =>
        (condition match {
          case Clause.BooleanTest(test) => s"«$test»"
          case Clause.MatchClass(scrutinee, Var(className), fields) =>
            s"«$scrutinee is $className»"
          case Clause.MatchTuple(scrutinee, arity, fields) =>
            s"«$scrutinee is Tuple#$arity»"
        }) + (if (condition.bindings.isEmpty) "" else " with " + showBindings(condition.bindings))
      }.mkString("", " and ", {
        (if (tailBindings.isEmpty) "" else " ") +
          showBindings(tailBindings) +
          s" => $term"
      }))
    }
  }

  /**
    * Attach bindings to the first condition of a CNF.
    *
    * @param conditions the conditions
    * @param interleavedLets the interleaved let buffer
    * @return idential to `conditions`
    */
  def withBindings
    (conditions: Conjunction)
    (implicit interleavedLets: Buffer[(Bool, Var, Term)])
  : Conjunction = {
    conditions._1 match {
      case Nil => (Nil, interleavedLets.toList ::: conditions._2)
      case head :: _ =>
        head.bindings = interleavedLets.toList
        conditions
    }
  }
}