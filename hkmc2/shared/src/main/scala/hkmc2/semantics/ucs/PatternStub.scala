package hkmc2
package semantics
package ucs

import collection.immutable.NumericRange
import mlscript.utils.*, shorthands.*

enum ConstructorLike:
  case Symbol(symbol: ClassSymbol | ModuleSymbol)
  /** "Virtual" constructor for string joining operator `~`. */
  case StringJoin
  /** Describe the size of tuples. If `infinite` is `false`, it represents
   *  fixed-size tuples. Otherwise, it represents tuples with at least `size`.
   */
  case TupleCapacity(size: Int, infinite: Bool)
  case Instantiation(symbol: PatternSymbol, arguments: List[DeBrujinSplit])
  case LocalPattern(id: Int)
  /** This case represents pattern parameters, which only make sense within the
    * body of the pattern declaration.
    */
  case Parameter(symbol: LocalSymbol & NamedSymbol)
  /**
    * This case represents a nested split, where the arity of the split must be 1
    * (there is exactly one `Binder` at the top level). The split must not have
    * free variables.
    */
  case Nested(split: DeBrujinSplit)
  
  lazy val arity: Int = this match
    case Symbol(symbol: ClassSymbol) => symbol.arity
    case Symbol(symbol: ModuleSymbol) => 0
    case StringJoin => 2
    case TupleCapacity(size, infinite) => ???
    case Instantiation(symbol, arguments) => 0 // TODO: fill in the arity
    case LocalPattern(id) => 0
    case Parameter(symbol) => 0 // TODO: fill in the arity
    case Nested(_) => 0
  
  def showDbg: Str = this match
    case Symbol(symbol: ClassSymbol) => symbol.toString // TODO: display arity
    case Symbol(symbol: ModuleSymbol) => symbol.toString
    case StringJoin => "~"
    case TupleCapacity(size, true) => s"tuple:$size+"
    case TupleCapacity(size, false) => s"tuple:$size"
    case Instantiation(symbol, arguments) => s"applied:${symbol.nme}(${arguments.iterator.map(_.showDbg.indent("  ")).mkString("\n", "\n", "\n")})"
    case LocalPattern(id) => s"local:$id"
    case Parameter(symbol) => s"parameter:${symbol.nme}"
    case Nested(split) => "<split>"

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
  case ClassLike(constructor: ConstructorLike)
  
  /** Match the current scrutinee unconditionally. */
  case Wildcard
  
  lazy val arity: Int = this match
    case Literal(_) => 0
    case CharClass(_) => 0
    case ClassLike(symbol) => symbol.arity
    case Wildcard => 0
    
  def display: Str = s"$showDbg ($arity)"
  
  def showDbg: Str = this match
    case Literal(value) => value.idStr
    case CharClass(range) => range.isInclusive match
      case true => s"'${range.start}' to '${range.end}'"
      case false => s"'${range.start}' until '${range.end}'"
    case ClassLike(symbol) => symbol.showDbg
    case Wildcard => "_"

object PatternStub:
  object CharClass:
    def apply(start: Char, end: Char, inclusive: Bool): PatternStub =
      if inclusive then CharClass(start to end) else CharClass(start until end)
