package mlscript.ucs

import mlscript.{Term, Var}
import mlscript.pretyper.ScrutineeSymbol
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
}
