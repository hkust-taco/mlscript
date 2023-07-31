package mlscript.ucs

import scala.collection.mutable.{Set => MutSet}

import mlscript._
import mlscript.utils.shorthands._

object helpers {
  /**
    * Make a tuple with only one element. For example,
    * 
    * ```scala
    * mkMonuple(t) = Tup(N -> Fld(false, false, t) :: Nil)
    * ```
    *
    * @param t the sole element
    * @return a tuple term with the only element
    */
  def mkMonuple(t: Term): Tup = Tup(N -> Fld(false, false, false, t) :: Nil)

  /**
    * Make a binary operation.
    *
    * @param lhs the left-hand side term
    * @param op the operator
    * @param rhs the right-hand side term
    * @return something like `App(App(op, lhs), rhs)`
    */
  def mkBinOp(lhs: Term, op: Var, rhs: Term): Term =
    App(App(op, mkMonuple(lhs)), mkMonuple(rhs))

  /**
    * Split a term joined by `and` into a list of terms.
    * E.g. `x and y and z` will be split into `x`, `y`, and `z`.
    *
    * @return a list of sub-terms of `t`
    */
  def splitAnd(t: Term): Ls[Term] =
    t match {
      case App(
        App(Var("and"),
            Tup((_ -> Fld(_, _, _, lhs)) :: Nil)),
        Tup((_ -> Fld(_, _, _, rhs)) :: Nil)
      ) =>
        splitAnd(lhs) :+ rhs
      case _ => t :: Nil
    }

  /**
    * Split a term into two parts: the pattern and the extra test.
    * This is used to extract patterns from UCS conjunctions. For example,
    * the second line results in `IfThen(Some(xv) and xv == 0, ...)`
    * in the following case.
    * 
    * ```
    * if x is
    *   Some(xv) and xv == 0 then ...
    * ```
    * 
    * We must separate `Some(xv)` from the term to complete the pattern
    * `x is Some(xv)`.
    *
    * @param term a term which might contains a pattern and an extra test
    * @return a tuple, whose the first element is the pattern and the second
    *   element is the extra test
    */
  def separatePattern(term: Term): (Term, Opt[Term]) =
    term match {
      case App(
        App(and @ Var("and"),
            Tup((_ -> Fld(_, _, _, lhs)) :: Nil)),
        Tup((_ -> Fld(_, _, _, rhs)) :: Nil)
      ) =>
        separatePattern(lhs) match {
          case (pattern, N) => (pattern, S(rhs))
          case (pattern, S(lshRhs)) => (pattern, S(mkBinOp(lshRhs, and, rhs)))
        }
      case _ => (term, N)
    }

  /**
    * Generate a chain of `Let` from a list of bindings.
    *
    * @param bindings a list of bindings, 
    * @param body the final body
    */
  def mkBindings(bindings: Ls[LetBinding], body: Term, defs: Set[Var]): Term = {
    def rec(bindings: Ls[LetBinding], defs: Set[Var]): Term =
      bindings match {
        case Nil => body
        case LetBinding(_, isRec, nameVar, value) :: tail =>
          if (defs.contains(nameVar)) {
            rec(tail, defs)
          } else {
            Let(isRec, nameVar, value, rec(tail, defs + nameVar))
          }
      }
    rec(bindings, defs)
  }
}
