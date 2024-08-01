package mlscript
package ucs.stages

import utils._, shorthands._

/**
  * A `PartialTerm` represents a possibly incomplete term.
  * We'd better precisely track detailed locations of each parts.
  */
sealed abstract class PartialTerm {
  /** Individual terms that used to build this `PartialTerm`. */
  def terms: Iterator[Term]

  override def toString(): String = this match {
    case PartialTerm.Empty => "<empty>"
    case PartialTerm.Total(term, _) => s"<total> ${term.showDbg}"
    case PartialTerm.Half(lhs, op, _) => s"<half> ${lhs.showDbg} ${op.name}"
  }
}

object PartialTerm {
  sealed abstract class Incomplete extends PartialTerm {
    def addTerm(term: Term): PartialTerm.Total
  }

  final case object Empty extends Incomplete {
    override def terms: Iterator[Term] = Iterator.empty
    def addTerm(term: Term): Total = Total(term, term :: Nil)
  }

  final case class Total(term: Term, parts: Ls[Term]) extends PartialTerm {
    override def terms: Iterator[Term] = parts.reverseIterator
    def addOp(op: Var): Half = Half(term, op, op :: parts)
    def get: Term = term
  }

  final case class Half(lhs: Term, op: Var, parts: Ls[Term]) extends Incomplete {
    override def terms: Iterator[Term] = parts.reverseIterator
    def addTerm(rhs: Term): Total = {
      val (realRhs, extraExprOpt) = separatePattern(rhs)
      val leftmost = App(op, PlainTup(lhs, realRhs))
      extraExprOpt match {
        case N            => Total(leftmost, parts)
        case S(extraExpr) => Total(App(Var("and"), PlainTup(leftmost, extraExpr)), extraExpr :: parts)
      }
    }
  }
}
