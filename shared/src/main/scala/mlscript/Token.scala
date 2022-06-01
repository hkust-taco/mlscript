package mlscript

import mlscript.utils._, shorthands._


sealed abstract class Token {
  def describe: Str = this match {
    case SPACE => "space"
    case COMMA => "comma"
    case NEWLINE => "newline"
    case INDENT => "indentation"
    case DEINDENT => "deindentation"
    case ERROR => "error"
    case LITVAL(value) => "literal"
    case KEYWORD(name) => s"'$name' keyword"
    case IDENT(name, symbolic) => if (symbolic) "operator" else "identifier"
    case OPEN_BRACKET(k) => s"opening ${k.name}"
    case CLOSE_BRACKET(k) => s"closing ${k.name}"
    case COMMENT(text) => "comment"
  }
}

case object SPACE extends Token
case object COMMA extends Token
case object NEWLINE extends Token // TODO rm
case object INDENT extends Token // TODO rm
case object DEINDENT extends Token // TODO rm
// final case class INDENTED(block: Ls[Token]) extends Token
case object ERROR extends Token
final case class LITVAL(value: Lit) extends Token
final case class KEYWORD(name: String) extends Token
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
  def name: Str = this match {
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

