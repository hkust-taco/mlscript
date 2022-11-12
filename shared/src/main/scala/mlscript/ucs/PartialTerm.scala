package mlscript.ucs

import mlscript._
import mlscript.utils.shorthands._

import helpers._

class PartialTermError(term: PartialTerm, message: Str) extends Error(message)

/**
  * A `PartialTerm` represents a possibly incomplete term.
  * We'd better precisely track detailed locations of each parts.
  * 
  * @param fragments fragment terms that used to build this `PartialTerm`.
  */
sealed abstract class PartialTerm(val fragments: Ls[Term]) {
  def addTerm(term: Term): PartialTerm.Total
  def addOp(op: Var): PartialTerm.Half
  def addTermOp(term: Term, op: Var): PartialTerm.Half =
    this.addTerm(term).addOp(op)
}

object PartialTerm {
  final case object Empty extends PartialTerm(Nil) {
    override def addTerm(term: Term): Total = Total(term, term :: Nil)
    override def addOp(op: Var): Half =
      throw new PartialTermError(this, s"expect a term but operator $op was given")
  }

  final case class Total(val term: Term, override val fragments: Ls[Term]) extends PartialTerm(fragments) {
    override def addTerm(term: Term): Total =
      throw new PartialTermError(this, s"expect an operator but term $term was given")
    override def addOp(op: Var): Half = Half(term, op, op :: fragments)
  }

  final case class Half(lhs: Term, op: Var, override val fragments: Ls[Term]) extends PartialTerm(fragments) {
    override def addTerm(rhs: Term): Total = op match {
      // TODO: Why are they look the same? How did the code here evolve?
      case isVar @ Var("is") =>
        // Special treatment for pattern matching.
        val (pattern, extraTestOpt) = separatePattern(rhs)
        val assertion = mkBinOp(lhs, isVar, pattern)
        extraTestOpt match {
          case N            => Total(assertion, fragments)
          case S(extraTest) => Total(mkBinOp(assertion, Var("and"), extraTest), extraTest :: fragments)
        }
      case _ =>
        val (realRhs, extraExprOpt) = separatePattern(rhs)
        val leftmost = mkBinOp(lhs, op, realRhs)
        extraExprOpt match {
          case N            => Total(leftmost, fragments)
          case S(extraExpr) => Total(mkBinOp(leftmost, Var("and"), extraExpr), extraExpr :: fragments)
        }
    }
    override def addOp(op: Var): Half =
      throw new PartialTermError(this, s"expect a term but operator $op was given")
  }
}