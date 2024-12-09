package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*

/** A partial-split is similar to `semantics.Split`, but we removed interleaved
 *  `let` and scrutinees. We also encode sub-matches inside `PatternStub`.
 * 
 *  A `PartialSplit` can be transformed to `Split` with a given scrutinee.
 */
enum PartialSplit extends ProductWithTail:
  /** Represent a conditional. If the current scrutinee matches `pattern`, and
   *  the sub-scrutinees matches the sub-partial-splits in `pattern`, then we go
   *  to `consequence`. Otherwise, we go to `alternative`.
   * 
   *  This corresponds to `Split.Cons(Branch(_, _, _), _)`.
   */
  case Branch(
      scrutinee: Int,
      pattern: PatternStub,
      consequence: PartialSplit,
      alternative: PartialSplit
  )
  /** Represent a successful match. This corresponds to `Split.Else(_)`. */
  case Accept
  /** Represent a failed match. This corresponds to `Split.End`. */
  case Reject
  
  def decrement: PartialSplit = this match
    case Branch(n, pattern, consequence, alternative) =>
      Branch(n - 1, pattern, consequence.decrement, alternative.decrement)
    case _ => this
    
  def increment: PartialSplit = this match
    case Branch(n, pattern, consequence, alternative) =>
      Branch(n + 1, pattern, consequence.increment, alternative.increment)
    case _ => this
    
  def parameterCount: Int = this match
    case Branch(_, pattern, consequence, _) =>
      consequence.parameterCount - pattern.arity
    case _ => 0
  
  // def ++(that: PartialSplit): PartialSplit = this match
  //   case Accept => this
  //   case Reject => that
  //   case Branch(pattern, consequence, alternative) =>
  //     Branch(pattern, consequence ++ that, alternative ++ that)
  
  def showDbg: Str = this match
    case Accept => "accept"
    case Reject => ""
    case Branch(n, pattern, consequence, alternative) =>
      val pat = pattern match
        case PatternStub.Literal(value) => value.idStr
        case PatternStub.CharClass(range) => range.isInclusive match
          case true => s"'${range.start}' to '${range.end}'"
          case false => s"'${range.start}' until '${range.end}'"
        case PatternStub.ClassLike(symbol) => symbol match
          case StringJoin => s"${n + 1} ~ ${n + 2}"
          case (size, true) => s"tuple:$size+"
          case (size, false) => s"tuple:$size"
          case symbol: ClassSymbol => symbol.toString // TODO: display arity
          case symbol: ModuleSymbol => symbol.toString
          case symbol: PatternSymbol => symbol.toString
          case symbol: TermSymbol => symbol.toString
        case PatternStub.Wildcard => "_"
      val con = consequence.showDbg
      val alt = alternative.showDbg
      s"$n is $pat ->" +
        (if con.contains('\n') then "\n" + con.indent("  ") else s" $con") +
        (if alt == "" then "" else s"\n$alt")
      
