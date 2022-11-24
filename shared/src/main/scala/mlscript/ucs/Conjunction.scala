package mlscript.ucs

import mlscript._, utils._, shorthands._
import Clause._, helpers._
import scala.collection.mutable.Buffer

/**
  * A `Conjunction` represents a list of `Clause`s.
  */
final case class Conjunction(clauses: Ls[Clause], trailingBindings: Ls[(Bool, Var, Term)]) {
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
  def +(rhs: Conjunction): Conjunction = {
    val Conjunction(lhsClauses, lhsTailBindings) = this
    val Conjunction(rhsClauses, rhsTailBindings) = rhs
    rhsClauses match {
      case Nil => Conjunction(lhsClauses, lhsTailBindings ::: rhsTailBindings)
      case head :: _ =>
        head.bindings = lhsTailBindings ::: head.bindings
        Conjunction(lhsClauses ::: rhsClauses, rhsTailBindings)
    }
  }

  /**
    * This is a shorthand if you only have clauses.
    *
    * @param suffix the list of clauses to append to this conjunction
    * @return a new conjunction with clauses from `this` and `suffix`
    */
  def +(suffix: Ls[Clause]): Conjunction = {
    suffix match {
      case Nil => this
      case head :: _ =>
        head.bindings = trailingBindings ::: head.bindings
        Conjunction(clauses ::: suffix, Nil)
    }
  }

  /**
    * This is a shorthand if you only have the last binding.
    *
    * @param suffix the list of clauses to append to this conjunction
    * @return a new conjunction with clauses from `this` and `suffix`
    */
  def +(lastBinding: (Bool, Var, Term)): Conjunction =
    Conjunction(clauses, trailingBindings :+ lastBinding)

  def separate(expectedScrutinee: Scrutinee): Opt[(MatchClass, Conjunction)] = {
    def rec(past: Ls[Clause], upcoming: Ls[Clause]): Opt[(Ls[Clause], MatchClass, Ls[Clause])] = {
      upcoming match {
        case Nil => N
        case (head @ MatchClass(scrutinee, _, _)) :: tail =>
          if (scrutinee === expectedScrutinee) {
            S((past, head, tail))
          } else {
            rec(past :+ head, tail)
          }
        case head :: tail =>
          rec(past :+ head, tail)
      }
    }

    rec(Nil, clauses).map { case (past, wanted, remaining) =>
      (wanted, Conjunction(past ::: remaining, trailingBindings))
    }
  }

  /**
    * Prepend bindings to the first condition of this conjunction.
    *
    * @param interleavedLets the buffer of let bindings in the current context
    * @return idential to `conditions`
    */
  def withBindings(implicit interleavedLets: Buffer[(Bool, Var, Term)]): Conjunction = {
    clauses match {
      case Nil => Conjunction(Nil, interleavedLets.toList ::: trailingBindings)
      case head :: _ =>
        head.bindings = head.bindings ::: interleavedLets.toList
        this
    }
  }
}

object Conjunction {
  def empty: Conjunction = Conjunction(Nil, Nil)
}
