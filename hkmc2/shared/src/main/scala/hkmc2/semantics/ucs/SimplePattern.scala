package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*

enum SimplePattern:
  case Wildcard
  case Literal(value: syntax.Literal)
  case ClassLike(symbol: MatchableSymbol)
  
  val arity: Int = this match
    case Wildcard => 0
    case Literal(_) => 0
    case ClassLike(symbol) => symbol match
      case StringJoin => 2
      case _: TermSymbol => 0
      case symbol: ClassSymbol => symbol.arity
      case _: ModuleSymbol => 0
  
  def display: Str = s"$showDbg ($arity)"
  
  def showDbg: Str = this match
    case Literal(value) => value.idStr
    case ClassLike(symbol) => symbol match
      case StringJoin => "~"
      case (size, true) => s"tuple:$size+"
      case (size, false) => s"tuple:$size"
      case symbol: ClassSymbol => symbol.toString // TODO: display arity
      case symbol: ModuleSymbol => symbol.toString
      case symbol: PatternSymbol => symbol.toString
    case Wildcard => "_"
