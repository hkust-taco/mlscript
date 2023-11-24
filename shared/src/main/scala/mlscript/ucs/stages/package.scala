package mlscript.ucs

import mlscript.{Term, Var}
import mlscript.pretyper.Symbol
import mlscript.utils._, shorthands._

package object stages {
  private[stages] sealed abstract class MatchOrNot {
    override def toString(): String = this match {
      case Yes => "+"
      case No => "-"
    }
  }
  private[stages] final case object Yes extends MatchOrNot
  private[stages] final case object No extends MatchOrNot
}
