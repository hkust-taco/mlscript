package hkmc2
package semantics
package ucs

import collection.immutable.NumericRange
import mlscript.utils.*, shorthands.*

/** "Virtual" constructor for string joining operator `~`. */
case object StringJoin

case class LocalPattern(id: Int, arity: Int)

case class Expansion(symbol: PatternSymbol)

/** Describe the size of tuples. If `infinite` is `false`, it represents
 *  fixed-size tuples. Otherwise, it represents tuples with at least `size`.
 */
type TupleCapacity = (size: Int, infinite: Bool)

type MatchableSymbol = ClassSymbol | ModuleSymbol | PatternSymbol |
  TupleCapacity | StringJoin.type | LocalPattern | Expansion | DeBrujinSplit

/** `PatternStub` is a simplified representation of `semantics.Pattern`. It
 *  excludes terms and symbols which can break the uniqueness of the pattern.
 */
enum PatternStub:  
  /** Match the current scrutinee with a literal. */
  case Literal(value: syntax.Literal)
  
  /** Match the current scrutinee with a range of characters. */
  case CharClass(range: NumericRange[Char])
  
  /** Match the current scrutinee with a class-like symbol. If the class-like
   *  symbol has extractions, each extraction has to match the corresponding
   *  `PartialSplit` stored in `subSplits`.
   */
  case ClassLike(symbol: MatchableSymbol)
  
  /** Match the current scrutinee unconditionally. */
  case Wildcard
  
  lazy val arity: Int = this match
    case Literal(_) => 0
    case CharClass(_) => 0
    case ClassLike(symbol) => symbol match
      case StringJoin => 2
      case symbol: ClassSymbol => symbol.arity
      case symbol: ModuleSymbol => 0
      case symbol: PatternSymbol => symbol.arity
      case LocalPattern(_, arity) => arity
      case _: DeBrujinSplit => 1 // The arity of embedded splits is always 1.
    case Wildcard => 0
    
  def display: Str = s"$showDbg ($arity)"
  
  def showDbg: Str = this match
    case Literal(value) => value.idStr
    case CharClass(range) => range.isInclusive match
      case true => s"'${range.start}' to '${range.end}'"
      case false => s"'${range.start}' until '${range.end}'"
    case ClassLike(symbol) => symbol match
      case StringJoin => "~"
      case (size, true) => s"tuple:$size+"
      case (size, false) => s"tuple:$size"
      case symbol: ClassSymbol => symbol.toString // TODO: display arity
      case symbol: ModuleSymbol => symbol.toString
      case symbol: PatternSymbol => symbol.toString
      case LocalPattern(id, _) => s"local:$id"
      case split: DeBrujinSplit => "<split>"
    case Wildcard => "_"

object PatternStub:
  object CharClass:
    def apply(start: Char, end: Char, inclusive: Bool): PatternStub =
      if inclusive then CharClass(start to end) else CharClass(start until end)
