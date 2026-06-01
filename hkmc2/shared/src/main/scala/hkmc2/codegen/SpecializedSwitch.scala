package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
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
 * - MFallthrough(next): Has only one branch, and if the branch executes to completion, then `next` is assigned
 *   to `x`.
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

private object PostCondRes:
  val empty = PostCondRes(false, false, Map.empty)

// isImpure: indicates whether the result was computed for a possibly impure expression. All analysis results
// that could possibly come before this result must be discarded.
// isAbortive: indicates whether the result was computed for an abortive block. When merging results from
// different branches, the results for this must be discarded.
private case class PostCondRes(isImpure: Bool, isAbortive: Bool, varsMap: Map[ValueSymbol, Literal]):
  def markImpure = copy(isImpure = true)

// Combines postconditions from different branches.
private def combinePostConds(p1: PostCondRes, p2: PostCondRes) =
  if p1.isAbortive && p2.isAbortive then
    PostCondRes(false, false, Map.empty)
  else if p1.isAbortive then
    PostCondRes(p2.isImpure, false, p2.varsMap) // We don't care about whether p1 is impure if it is abortive.
  else if p2.isAbortive then
    PostCondRes(p1.isImpure, false, p1.varsMap) // Same as above
  else
    // If a variable was set to a different value in either branch, or was only set in one branch, do not include
    // Otherwise, we can combine them
    val combined = p1.varsMap.collect:
      case k -> v1 if p2.varsMap.contains(k) && p2.varsMap(k) == v1 => k -> v1
    PostCondRes(p1.isImpure || p2.isImpure, false, combined)

extension (r: PostCondRes)
  // For combining postconditions derived in different branches
  def ++(r2: PostCondRes): PostCondRes = combinePostConds(r, r2)
  // For combining sequences of postconditions
  def >=>(r2: PostCondRes): PostCondRes =
    if r.isAbortive then r
    else if r2.isImpure then r2
    else PostCondRes(r.isImpure, r2.isAbortive, r.varsMap ++ r2.varsMap)
  def +(v: ValueSymbol -> Literal): PostCondRes = PostCondRes(r.isImpure, r.isAbortive, r.varsMap + v)

// Analyzes postconditions for a block. Namely, determines variables that are
// definitely set to a certain literal.
//
// Note that impure computations will lead to `isImpure` being set to true. This means
// all analysis *before* the impure computation will be discarded.
//
// The intended semantics of this are, assuming the block finishes execution, i.e.
// it does not break to a label that wraps the block or returns, then the 
// postconditions hold. Otherwise, the results are invalid, which does not matter,
// because they will be irrelevant in that case anyway.
private object PostCondAnalysisImpl extends CachedAnalysis[Block, PostCondRes]:
  
  private def res(lhs: Opt[ValueSymbol], rhs: Result, rest: Block) =
    if rhs.isPure then lhs match
      case Some(lhs) => rhs match
        case Value.Lit(lit) => PostCondRes(false, false, Map(lhs -> lit)) >=> analyze(rest)
        case _ => analyze(rest)
      case None => analyze(rest)
    else analyze(rest).markImpure
  
  override def analyzeUncached(b: Block): PostCondRes = b match
    case Label(label, loop, body, rest) =>
      /* We do not traverse into the label body.
       * If we do, then there are cases like this:
       * 
       * label l1:
       *   label l2:
       *     body
       *     set x = 1
       *   end
       * end
       * 
       * and it is very difficult to tell whether we should have the postcondition x = 2 in the outer loop,
       * because `body` could break out of `l1` or `l2`.
       * 
       * Not traversing into labels also makes `Block.isAbortive` more useful, as we always know that
       * if a block is abortive, then it aborts out of the "initial" block that `analyze` was called on.
       */
      val restRes = analyze(rest)
      restRes.copy(isImpure = restRes.isImpure || analyze(body).isImpure)
    case Match(scrut, arms, dflt, rest) =>
      arms.foldLeft(dflt.map(analyze).getOrElse(PostCondRes.empty)):
        case (acc, (_, blk)) => acc ++ analyze(blk)
      >=> analyze(rest)
    case Scoped(syms, body) => analyze(body)
    case Begin(sub, rest) => analyze(sub) >=> analyze(rest)
    case TryBlock(sub, finallyDo, rest) => analyze(sub) >=> analyze(finallyDo) >=> analyze(rest)
    case Assign(NoSymbol, rhs, rest) => res(N, rhs, rest)
    case Assign(lhs: ValueSymbol, rhs, rest) => res(S(lhs), rhs, rest)
    case AssignField(path, _, rhs, rest) => res(N, rhs, rest)
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => res(N, rhs, rest)
    case Define(defn, rest) => defn match
      case v: ValDefn => res(S(v.sym), v.rhs, rest)
      case c: ClsLikeDefn => analyze(rest).markImpure // TODO: refine for object and module ctors
      case f: FunDefn => analyze(rest)
    case b: BlockTail => PostCondRes.empty.copy(isAbortive = b.isAbortive)

private object PostCondAnalysis extends CachedAnalysis[Block, Map[ValueSymbol, Literal]]:
  override def analyzeUncached(b: Block): Map[ValueSymbol, Literal] = PostCondAnalysisImpl.analyze(b).varsMap

// Matches List[Case.Lit -> Block]
private object LitCases:
  def unapply(arms: List[Case -> Block]) = arms.foldLeft[Opt[List[Literal -> Block]]](S(Nil)):
    case (S(acc), Case.Lit(litVal) -> b) => S((litVal -> b) :: acc)
    case _ => N

private case class MatchChain(scrut: Value.SimpleRef, cases: List[MatchType], dflt: Opt[Block], rest: Block)

// Helper that determines whether a default branch is empty
private def isEmptyDflt(dflt: Opt[Block]) = dflt match
  case S(x) if x.isEmpty => true
  case N => true
  case _ => false

// Extracts a valid match chain beginning at a block.
@tailrec
private def findMatchChainRec(
  b: Block,
  scrutRef: Value.SimpleRef,
  acc: List[MatchType]
): MatchChain =
  object TailAssign:
    def unapply(b: Block) =
      if b.isAbortive then N
      else PostCondAnalysis.analyze(b).get(scrutRef.sym) match
        case S(value) => S(value)
        case N => N
  
  
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
            val restEmpty = restBlk.isEmpty
            val res = MatchType.MAbortive(arms)
            if !dfltEmpty && !restEmpty then
              if !isDfltCaseAllowed then fail
              else success(res, m, m.dflt, dfltEmpty, restBlk)
            else if restEmpty then
              success(res, m, N, true, m.dflt.getOrElse(End()))
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

private case class SwitchLike(scrut: Value.SimpleRef, cases: List[SwitchCase], dflt: Opt[Block], rest: Block)

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
    case m @ Match(scrut = r @ Value.SimpleRef(l)) =>
      val chain = findMatchChainRec(m, r, Nil)
      val SwitchLike(scrut, cases, dflt, rest) = matchChainToSwitch(chain)
      if cases.size < 2 then N
      else
        S((scrut, cases.reverse, dflt, rest))
    case _ => N
