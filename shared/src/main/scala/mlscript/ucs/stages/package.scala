package mlscript.ucs

import mlscript.{Lit, Term, Var}
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._

package object stages {
  object Scrutinee {
    def unapply(term: Term): Opt[(Var, ScrutineeSymbol)] = term match {
      case v @ Var(_) => v.symbol match {
        case symbol: ScrutineeSymbol => S(v, symbol)
        case _ => N
      }
      case _ => N
    }
  }

  private[stages] sealed abstract class MatchOrNot {
    override def toString(): String = this match {
      case Yes => "+"
      case No => "-"
    }
  }
  private[stages] final case object Yes extends MatchOrNot
  private[stages] final case object No extends MatchOrNot

  sealed abstract class CasePattern {
    override def toString(): String = this match {
      case CasePattern.Class(symbol) => symbol.name
      case CasePattern.Boolean(value) => value.toString
      case CasePattern.Literal(value) => value.toString
    }
  }

  object CasePattern {
    final case class Class(symbol: TypeSymbol) extends CasePattern
    final case class Boolean(value: Boolean) extends CasePattern
    final case class Literal(value: Lit) extends CasePattern
  }
}
