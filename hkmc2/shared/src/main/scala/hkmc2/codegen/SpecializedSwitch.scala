package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.syntax.{Literal}
import scala.annotation.tailrec

/**
  * Represents a switch case.
  * @param l The case's literal value.
  * @param b The case body.
  */
enum SwitchCase(l: Literal, b: Block):
  /**
    * A switch case that requires an explicit `break` to be inserted by the codegen.
    * @param l The case's literal value.
    * @param b The case body.
    */
  case ExplicitBreak(l: Literal, b: Block) extends SwitchCase(l, b)
  /**
    * A switch case that already has a `break` or `continue` at the end.
    * @param l The case's literal value.
    * @param b The case body.
    */
  case ImplicitBreak(l: Literal, b: Block) extends SwitchCase(l, b)
  /**
    * A switch case that falls through to the subsequent case.
    * @param l The case's literal value.
    * @param b The case body.
    * @param next The literal value of the next case.
    */
  case Fallthrough(l: Literal, b: Block, next: Literal) extends SwitchCase(l, b)

private enum MatchType:
  case MFallthrough(value: Literal, body: Block, next: Literal)
  case MBreak(value: Literal, body: Block)
  case MCases(arms: List[Literal -> Block])

/*
 * We specialize chains of match statements of the following form:
 * 
 * M1 M2 ... Mn
 * 
 * where each Mi are match statements that match on a common scrutinee `x`, only have literal patterns,
 * and have an empty or no default case, except for Mn. We define three types of such match statements
 * (which are mostly unrelated to switch case types in the enum `SwitchCase`):
 * - MFallthrough(next): Has only one branch, and assigns the literal `next` to `x` at the end of that branch.
 * - MBreak: Has only one branch that ends with a `break` or a `continue` (and thus exits the
 *   scope that the match chain is defined in).
 * - MCases: Is not an MFallthrough or an MBreak (but still matches on `x` and only has literals patterns).
 * 
 * For this chain to be specialized, for each adjacent pair Mi and M(i+1), one of the following hold:
 * 
 * - Mi = MFallthrough(_, _, v), and the first case of M(i+1) matches v.
 * - Mi = MBreak.
 * 
 * Note that this means Mi = MCases only if i = n.
 * 
 * Furthermore, if M(n-1) is an MBreak, then the last statement may have a non-empty default case and it will be
 * compiled into `default: body`.
 * 
 * - MFallthrough is translated into SwitchCase.Fallthrough.
 * - MBreak is translated into SwitchCase.ImplicitBreak.
 * - MCases is translated into a list of SwitchCase.ExplicitBreak.
 */

// S(S(value)): Ends with assign
// S(N): Ends with break or continue
// N: None of the cases
@tailrec
private def caseLastBlk(b: Block, scrutSym: Local): Opt[Opt[Literal]] = b match
  case a @ Assign(`scrutSym`, l: Literal, End(_)) => S(S(l))
  case b: (Break | Continue) => S(N)
  case b: NonBlockTail => caseLastBlk(b.rest, scrutSym)
  case _: BlockTail => N

private object LitCases:
  def unapply(arms: List[Case -> Block]) = arms.foldLeft[Opt[List[Literal -> Block]]](S(Nil)):
    case (S(acc), Case.Lit(litVal) -> b) => S((litVal -> b) :: acc)
    case _ => N

@tailrec
private def findMatchChainRec(
  b: Block,
  scrutSym: Local,
  acc: List[MatchType]
): (cases: List[MatchType], dflt: Opt[Block], rest: Block) =
  
  object CaseLastBlk:
    def unapply(b: Block) = caseLastBlk(b, scrutSym)
  
  inline def join: (cases: List[MatchType], dflt: Opt[Block], rest: Block) = b match
    case m: Match =>
      // Classify the current match statement.
      val curMatch = b match
        // MFallthrough or MBreak
        case Match(
          Value.Ref(`scrutSym`, _),                               // * The scrutinee is a ref and is the same as the one before.
          Case.Lit(curVal) -> (b @ CaseLastBlk(nextVal)) :: Nil,  // * There is only one case matching an int literal
                                                                  //   and it ends with break, continue or a literal assignment.
          default, restBlk
        ) => nextVal match
          case S(nextVal) => S(MatchType.MFallthrough(curVal, b, nextVal))
          case N => S(MatchType.MBreak(curVal, b))
        // MCases
        case Match(Value.Ref(`scrutSym`, _), LitCases(arms), default, restBlk) =>
          S(MatchType.MCases(arms))
        case _ => N
      
      curMatch match
      case Some(value) =>
        // Only the last match may have a default case.
        if m.dflt.isDefined then (value :: acc, m.dflt, m.rest)
        else findMatchChainRec(m.rest, scrutSym, value :: acc)
      case None => (acc, N, m)
    case _ => (acc, N, b)
  
  
  val curVal = b match
    case m: Match => m.arms.headOption.collect:
      case Case.Lit(lit) -> _ => lit
    case _ => N
  
  acc.headOption match
    case Some(MatchType.MFallthrough(next = expectedVal))
      if curVal.map(_ == expectedVal).getOrElse(true) => join
    case Some(_: MatchType.MBreak) | None => join
    case _ => (acc, N, b)



object SpecializedSwitch:
  def unapply(b: Block) = ???
