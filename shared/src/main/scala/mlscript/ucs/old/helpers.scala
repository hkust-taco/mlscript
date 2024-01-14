package mlscript.ucs.old

import scala.collection.mutable.{Set => MutSet}

import mlscript._
import mlscript.utils.shorthands._

object helpers {
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
            Tup((_ -> Fld(_, lhs)) :: Nil)),
        Tup((_ -> Fld(_, rhs)) :: Nil)
      ) => // * Old-style operators
        splitAnd(lhs) :+ rhs
      case App(Var("and"), PlainTup(lhs, rhs)) =>
        splitAnd(lhs) :+ rhs
      case _ => t :: Nil
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
