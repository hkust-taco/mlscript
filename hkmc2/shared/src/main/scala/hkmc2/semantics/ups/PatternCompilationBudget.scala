package hkmc2
package semantics
package ups

import hkmc2.utils.*, shorthands.*
import Message.MessageContext, ucs.error

/** An internal abort, caught at the entry to a compilation stage. No partial
  * automaton or incomplete instantiation context may escape on exhaustion. */
private[ups] final case class PatternCompilationLimit(field: Str, limit: Int)
    extends RuntimeException with scala.util.control.NoStackTrace:
  def report(loc: Opt[Loc])(using Raise): Unit = error(
    msg"Pattern compilation exceeded `${field}` (${limit})." -> loc,
    msg"Simplify this pattern or increase the limit with `#config(${field}: ...)`." -> N,
    msg"This resource limit does not mean that the pattern's language is non-regular." -> N)

/** Deterministic work accounting for one instantiation or automaton build.
  * Charge graph visits, copied entries and table cells before allocating them.
  * Counts use Long so products of state and alphabet sizes cannot overflow.
  * The state cap also bounds individual NFA/DFA graphs independently of how
  * much work has already been spent. Each compiler invocation owns its budget.
  */
private[ups] final class PatternCompilationBudget(using Config):
  private var remaining = config.patternCompilationWorkLimit.toLong

  def spend(amount: Long): Unit =
    require(amount >= 0)
    if amount > remaining then
      throw PatternCompilationLimit("patternCompilationWorkLimit", config.patternCompilationWorkLimit)
    remaining -= amount

  def newState(existing: Int): Unit =
    if existing >= config.stringPatternStateLimit then
      throw PatternCompilationLimit("stringPatternStateLimit", config.stringPatternStateLimit)
    spend(1)

  def newSpecialization(existing: Int): Unit =
    if existing >= config.patternSpecializationLimit then
      throw PatternCompilationLimit("patternSpecializationLimit", config.patternSpecializationLimit)
    spend(1)
