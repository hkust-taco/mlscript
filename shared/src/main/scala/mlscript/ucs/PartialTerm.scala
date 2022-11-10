package mlscript.ucs

import mlscript._
import mlscript.utils.shorthands._

import helpers._

// FIXME: It seems the `locations` here does not really work.
// It's not used right now.
// Becuase we will split the term by `and`.
// We'd better precisely track detailed locations of each parts.
sealed abstract class PartialTerm(val locations: Ls[Loc]) {
  def addTerm(term: Term): PartialTerm.Total
  def addOp(op: Var): PartialTerm.Half
  def addTermOp(term: Term, op: Var): PartialTerm.Half =
    this.addTerm(term).addOp(op)

  protected final def prependLocation(loc: Opt[Loc]): Ls[Loc] =
    loc.fold(locations)(_ :: locations)
  protected final def prependLocations(locs: Opt[Loc]*): Ls[Loc] =
    locs.iterator.flatten.toList ::: locations
}

class PartialTermError(term: PartialTerm, message: Str) extends Error(message)

object PartialTerm {
  final case object Empty extends PartialTerm(Nil) {
    override def addTerm(term: Term): Total = Total(term, prependLocation(term.toLoc))
    override def addOp(op: Var): Half =
      throw new PartialTermError(this, s"expect a term but operator $op was given")
  }

  final case class Total(val term: Term, override val locations: Ls[Loc]) extends PartialTerm(locations) {
    override def addTerm(term: Term): Total =
      throw new PartialTermError(this, s"expect an operator but term $term was given")
    override def addOp(op: Var): Half = Half(term, op, prependLocation(op.toLoc))
  }

  final case class Half(lhs: Term, op: Var, override val locations: Ls[Loc]) extends PartialTerm(locations) {
    override def addTerm(rhs: Term): Total = op match {
      case isVar @ Var("is") =>
        // Special treatment for pattern matching.
        val (pattern, extraTestOpt) = separatePattern(rhs)
        val assertion = mkBinOp(lhs, isVar, pattern)
        extraTestOpt match {
          case N => Total(assertion, prependLocation(pattern.toLoc))
          case S(extraTest) => Total(
            mkBinOp(assertion, Var("and"), extraTest),
            prependLocation(extraTest.toLoc)
          )
        }
      case _ =>
        val (realRhs, extraExprOpt) = separatePattern(rhs)
        val leftmost = mkBinOp(lhs, op, realRhs)
        Total(
          extraExprOpt.fold(leftmost){ mkBinOp(leftmost, Var("and"), _) },
          prependLocations(realRhs.toLoc, extraExprOpt.flatMap(_.toLoc))
        )
    }
    override def addOp(op: Var): Half =
      throw new PartialTermError(this, s"expect a term but operator $op was given")
  }
}