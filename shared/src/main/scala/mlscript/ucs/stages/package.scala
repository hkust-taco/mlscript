package mlscript.ucs

import mlscript.{Lit, Term, Var}
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._

package object stages {
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
