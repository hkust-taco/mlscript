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
enum SwitchCase(val litValue: Literal, val body: Block):
  /**
    * A switch case that requires an explicit `break` to be inserted by the codegen.
    * @param l The case's literal value.
    * @param b The case body.
    */
  case ExplicitBreak(l: Literal, b: Block) extends SwitchCase(l, b)
  /**
    * A switch case that is abortive and does not explicitly require a `break`.
    * @param l The case's literal value.
    * @param b The case body.
    */
  case Abortive(l: Literal, b: Block) extends SwitchCase(l, b)
  /**
    * A switch case that falls through to the subsequent case.
    * @param l The case's literal value.
    * @param b The case body.
    * @param next The literal value of the next case.
    */
  case Fallthrough(l: Literal, b: Block, next: Literal) extends SwitchCase(l, b)

private enum MatchType:
  case MFallthrough(value: Literal, body: Block, next: Literal)
  case MAbortive(arms: List[Literal -> Block])
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
 * - MAbortive: All branches are abortive (and thus exits the scope that the match chain is defined in).
 * - MCases: Is not an MFallthrough or an MAbortive (but still matches on `x` and only has literals patterns).
 * 
 * For this chain to be specialized, for each adjacent pair Mi and M(i+1), one of the following hold:
 * 
 * - Mi = MFallthrough(_, _, v), and the first case of M(i+1) matches v.
 * - Mi = MAbortive.
 * 
 * Note that this means Mi = MCases only if i = n.
 * 
 * Furthermore, if M(n-1) is an MAbortive, then the last statement may have a non-empty default case and it will be
 * compiled into `default: body`.
 * 
 * - MFallthrough is translated into SwitchCase.Fallthrough.
 * - MAbortive is translated into SwitchCase.Abortive.
 * - MCases is translated into a list of SwitchCase.ExplicitBreak.
 */

// S(value): Ends with assign
// N: None of the cases
@tailrec
private def isTailAssign(b: Block, scrutSym: Local): Opt[Literal] = b match
  case a @ Assign(`scrutSym`, Value.Lit(l), End(_)) => S(l)
  case b: NonBlockTail => isTailAssign(b.rest, scrutSym)
  case _: BlockTail => N

// Matches List[Case.Lit -> Block]
private object LitCases:
  def unapply(arms: List[Case -> Block]) = arms.foldLeft[Opt[List[Literal -> Block]]](S(Nil)):
    case (S(acc), Case.Lit(litVal) -> b) => S((litVal -> b) :: acc)
    case _ => N

private case class MatchChain(scrut: Value.Ref, cases: List[MatchType], dflt: Opt[Block], rest: Block)

// Helper that determines whether a default branch is empty
private def isEmptyDflt(dflt: Opt[Block]) = dflt match
  case Some(End(_)) => true
  case None => true
  case _ => false

// Extracts a valid match chain beginning at a block.
@tailrec
private def findMatchChainRec(
  b: Block,
  scrutRef: Value.Ref,
  acc: List[MatchType]
): MatchChain =
  object TailAssign:
    def unapply(b: Block) = isTailAssign(b, scrutRef.l)
  
  // Whether the current match may have a non-empty default case.
  // It is allowed iff the previous case was a break, or if this is the only case.
  val isDfltCaseAllowed = acc.headOption match
    case Some(_: MatchType.MAbortive) => true
    case None => true
    case _ => false
  
  // This block does not include the match chain
  inline def fail = MatchChain(scrutRef, acc, N, b)
  
  inline def success(res: MatchType, m: Match, dflt: Opt[Block], dfltEmpty: Bool, rest: Block) =
    if !dfltEmpty then MatchChain(scrutRef, res :: acc, dflt, rest)
    else findMatchChainRec(rest, scrutRef, res :: acc)
  
  inline def join: MatchChain = b match
    case m: Match =>
      val dfltEmpty = isEmptyDflt(m.dflt)
      
      // Classify the current match statement.
      m match
        // MFallthrough
        case Match(
          `scrutRef`,                                                 // * The scrutinee is a ref and is the same as the one before.
          Case.Lit(curVal) -> (b @ TailAssign(nextVal)) :: Nil,       // * There is only one case matching a literal
                                                                      //   and it assigns the scrut to a literal.
          default, restBlk
        ) =>
          if !isDfltCaseAllowed && !dfltEmpty then fail               // Default branch not allowed
          else
            val res = MatchType.MFallthrough(curVal, b, nextVal)
            success(res, m, m.dflt, dfltEmpty, restBlk)
        // MAbortive or MCases
        case Match(`scrutRef`, LitCases(arms), default, restBlk) =>
          // MAbortive
          if arms.forall(_._2.isAbortive) then
            // If both default and restBlk are not End(), and default blocks are not allowed, then fail
            // Otherwise, take the non-end one as the next block
            val restEmpty = restBlk.isInstanceOf[End]
            val res = MatchType.MAbortive(arms)
            if !dfltEmpty && !restEmpty then
              if !isDfltCaseAllowed then fail
              else success(res, m, m.dflt, dfltEmpty, restBlk)
            else if restEmpty then
              success(res, m, N, true, m.dflt.get)
            else
              success(res, m, m.dflt, dfltEmpty, restBlk)
          // MCases
          else
            if !isDfltCaseAllowed && !dfltEmpty then fail                // Default branch not allowed
            else
              val res = MatchType.MCases(arms)
              success(res, m, m.dflt, dfltEmpty, restBlk)
        case _ => fail
    case _ => fail
  
  // Get the first case's value (in case the previous match is MFallthrough).
  val curVal = b match
    case m: Match => m.arms.headOption.collect:
      case Case.Lit(lit) -> _ => lit
    case _ => N
  
  // Check for the valid cases:
  // - The previous match is a fallthrough that sets the scrut to curVal.
  // - The previous match is abortive.
  acc.headOption match
    case S(MatchType.MFallthrough(next = expectedVal))
      if curVal.map(_ == expectedVal).getOrElse(true) =>
        join // OK
    case S(_: MatchType.MAbortive) | N => join // OK
    case S(_) => fail

private case class SwitchLike(scrut: Value.Ref, cases: List[SwitchCase], dflt: Opt[Block], rest: Block)

// Converts a match chain to a switch.
private def matchChainToSwitch(m: MatchChain): SwitchLike =
  def mpArms(arms: List[(Literal, Block)]) = arms.map:
    case (l, b) =>
      if b.isAbortive then SwitchCase.Abortive(l, b)
      else SwitchCase.ExplicitBreak(l, b)
  val cases = m.cases.flatMap:
    case MatchType.MFallthrough(value, body, next) =>
      SwitchCase.Fallthrough(value, body, next) :: Nil
    case MatchType.MAbortive(arms) => mpArms(arms)
    case MatchType.MCases(arms) => mpArms(arms)
  SwitchLike(m.scrut, cases, m.dflt, m.rest)

object SpecializedSwitch:
  def unapply(b: Block) = b match
    case m @ Match(scrut = r @ Value.Ref(l, _)) =>
      val chain = findMatchChainRec(m, r, Nil)
      val SwitchLike(scrut, cases, dflt, rest) = matchChainToSwitch(chain)
      if cases.size < 2 then N
      else
        S((scrut, cases.reverse, dflt, rest))
    case _ => N

