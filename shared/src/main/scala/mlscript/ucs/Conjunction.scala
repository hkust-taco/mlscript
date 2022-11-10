package mlscript.ucs

import mlscript._, utils._, shorthands._
import Clause._, helpers._

/**
  * A `Conjunction` represents a list of `Clause`s.
  */
object Conjunction {
  /**
    * Concatenate two `Conjunction` together.
    * 
    * The trailing bindings of the first `Conjunction` will be added to the
    * first `Clause` of the second `Conjunction`
    *
    * @param lhs the left hand side value
    * @param rhs the right hand side value
    * @return the sititched `Conjunction`
    */
  def concat(lhs: Conjunction, rhs: Conjunction): Conjunction = {
    val (lhsConditions, lhsTailBindings) = lhs
    val (rhsConditions, rhsTailBindings) = rhs
    rhsConditions match {
      case Nil => (lhsConditions, lhsTailBindings ::: rhsTailBindings)
      case head :: _ =>
        head.bindings = lhsTailBindings ::: head.bindings
        (lhsConditions ::: rhsConditions, rhsTailBindings)
    }
  }

  def separate(conditions: Conjunction, expectedScrutinee: Scrutinee): Opt[(MatchClass, Conjunction)] = {
    def rec(past: Ls[Clause], upcoming: Ls[Clause])
        : Opt[(Ls[Clause], MatchClass, Ls[Clause])] = {
      upcoming match {
        case Nil => N
        case (head @ MatchClass(scrutinee, _, _)) :: tail =>
          if (scrutinee === expectedScrutinee) {
            S((past, head, tail))
          } else {
            rec(past :+ head, tail)
          }
        // TODO: Support tuples after merging `MatchClass` and `MatchTuple`.
        case head :: tail =>
          rec(past :+ head, tail)
      }
    }

    // println(s"Searching $expectedScrutinee in $conditions")
    rec(Nil, conditions._1).map { case (past, wanted, remaining) =>
      // println("Found!")
      (wanted, (past ::: remaining, conditions._2))
    }
  }
}