package mlscript.ucs

import scala.collection.mutable.{Set => MutSet}

import mlscript._
import mlscript.utils.shorthands._

object helpers {
  import stages.mkBinOp

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
  def separatePattern(term: Term, newDefs: Bool): (Term, Opt[Term]) =
    term match {
      case App(
        App(and @ Var("and"),
            Tup((_ -> Fld(_, lhs)) :: Nil)),
        Tup((_ -> Fld(_, rhs)) :: Nil)
      ) => // * Old-style operators
        separatePattern(lhs, newDefs) match {
          case (pattern, N) => (pattern, S(rhs))
          case (pattern, S(lshRhs)) => (pattern, S(mkBinOp(lshRhs, and, rhs, newDefs)))
        }
      case App(and @ Var("and"), PlainTup(lhs, rhs)) =>
        separatePattern(lhs, newDefs) match {
          case (pattern, N) => (pattern, S(rhs))
          case (pattern, S(lshRhs)) => (pattern, S(mkBinOp(lshRhs, and, rhs, newDefs)))
        }
      case _ => (term, N)
    }
}
