package mlscript

import mlscript.utils._, shorthands._


sealed abstract class Token

final case class SPACE() extends Token
final case class NEWLINE() extends Token // TODO rm
final case class INDENT() extends Token // TODO rm
final case class DEINDENT() extends Token // TODO rm
// final case class INDENTED(block: Ls[Token]) extends Token
final case class ERROR() extends Token
final case class LITVAL(value: Lit) extends Token
final case class IDENT(name: String, symbolic: Bool) extends Token
final case class OPEN_BRACKET(k: BracketKind) extends Token // TODO rm
final case class CLOSE_BRACKET(k: BracketKind) extends Token // TODO rm
// final case class BRACKETS(k: BracketKind) extends Token
final case class COMMENT(text: String) extends Token


sealed abstract class BracketKind {
  import BracketKind._
  lazy val (beg, end) = this match {
    case Round => '(' -> ')'
    case Curly => '{' -> '}'
    case Square => '[' -> ']'
  }
  def name = this match {
    case Round => "parenthesis"
    case Curly => "curly brace"
    case Square => "square bracket"
  }
}

object BracketKind {
  case object Round extends BracketKind
  case object Curly extends BracketKind
  case object Square extends BracketKind
  def unapply(c: Char): Opt[Either[BracketKind, BracketKind]] = c |>? {
    case '(' => Left(Round)
    case ')' => Right(Round)
    case '{' => Left(Curly)
    case '}' => Right(Curly)
    case '[' => Left(Square)
    case ']' => Right(Square)
  }
}

