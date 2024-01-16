package mlscript.ucs

import mlscript.{App, Fld, FldFlags, Lit, PlainTup, Term, Tup, Var}
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._

package object stages {
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
  def mkMonuple(t: Term): Tup = Tup(N -> Fld(FldFlags.empty, t) :: Nil)

  /**
    * Make a binary operation.
    *
    * @param lhs the left-hand side term
    * @param op the operator
    * @param rhs the right-hand side term
    * @return something like `App(App(op, lhs), rhs)`
    */
  def mkBinOp(lhs: Term, op: Var, rhs: Term, newDefs: Bool): Term =
    if (newDefs) App(op, PlainTup(lhs, rhs))
    else App(App(op, mkMonuple(lhs)), mkMonuple(rhs))
}
