package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.ScopeData.*
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
 * - MCases: Is not an MFallthrough or an MBreak (but still matches on `x` and only has literals patterns.)
 * 
 * For this chain to be specialized, for each adjacent pair Mi and M(i+1), one of the following hold:
 * 
 * - Mi = MFallthrough(_, _, v) and Mi(i+1) matches v, and the first case of M(i+1) matches v.
 *   ==> Mi gets translated into SwitchCase.Fallthrough.
 * - Mi = MBreak.
 *   ==> Mi gets translated into ImplicitBreak.
 * 
 * Note that this means Mi = MCases only if i = n.
 * 
 * Furthermore, if M(n-1) is an MBreak, then the last statement may have a non-empty default case and it will be
 * compiled into `default: body`.
 */
@tailrec
private def lastBlk(b: Block): Opt[Assign | Break | Continue] = b match
  case a @ Assign(lhs, rhs, End(_)) => S(a)
  case b: (Break | Continue) => S(b)
  case b: NonBlockTail => lastBlk(b.rest)
  case _: BlockTail => N

// @tailrec
private def specializeIfRec(
  b: Block, 
  scrutSym: Local,
  prev: Opt[SwitchCase],
  acc: List[SwitchCase]
): (cases: List[SwitchCase], rest: Block) = b match
  case Match(
    Value.Ref(`scrutSym`, _),         // The scrutinee is a ref and is the same as the one before.
    Case.Lit(curVal) -> caseBod :: Nil,     // There is only one case matching an int literal.
    N | S(End(_)), rest               // Default case does nothing, or does not exist.
  ) => 
    def join =
      val last = lastBlk(caseBod)
      ???
    prev match
    case Some(SwitchCase.Fallthrough(l, b, expectedVal)) if expectedVal === curVal => join
    case Some(_: SwitchCase.ExplicitBreak) | Some(_: SwitchCase.ImplicitBreak) | None => join
    case _ => (acc, b)
  case _ => (acc, b)



object SpecializedSwitch:
  def unapply(b: Block) = ???
