package hkmc2
package semantics
package ups

import hkmc2.utils.*, shorthands.*
import Message.MessageContext, ucs.error

/** An internal abort, caught at the entry to a compilation stage. No partial
  * matcher, automaton or incomplete instantiation context may escape on exhaustion. */
private[ups] final case class PatternCompilationLimit(field: Str, limit: Int)
    extends RuntimeException with scala.util.control.NoStackTrace:
  def report(loc: Opt[Loc])(using Raise): Unit = error(
    msg"Pattern compilation exceeded `${field}` (${limit})." -> loc,
    msg"Simplify this pattern or increase the limit with `#config(${field}: ...)`." -> N,
    msg"This resource limit does not mean that the pattern's language is non-regular." -> N)

/** Deterministic work accounting, shared by the pattern compilation stages.
  * Charge graph visits, copied entries and table cells before allocating them.
  * Counts use Long so products of state and alphabet sizes cannot overflow.
  */
private[ups] class PatternCompilationWorkBudget(field: Str, limit: Int):
  private var remaining = limit.toLong

  def spend(amount: Long): Unit =
    require(amount >= 0)
    if amount > remaining then
      throw PatternCompilationLimit(field, limit)
    remaining -= amount

  /** Structural hashing and tree traversals revisit shared argument subtrees.
    * Compute their unfolded size using identity memoization, saturating above
    * the limit so measuring an exponentially shared DAG is itself bounded.
    * Synonym bodies are charged separately when an operation unfolds them.
    */
  def visit(pattern: Pat): Unit = spend(treeSize(pattern))

  private val treeSizes = collection.mutable.Map.empty[Identity[Pat], Long]

  private def treeSize(pattern: Pat): Long = treeSizes.getOrElseUpdate(Identity(pattern), {
    import Pattern.*
    val children: Iterable[Pat] = pattern match
      case Concat(ps) => ps
      case And(ps) => ps
      case Or(ps) => ps
      case Not(p) => p :: Nil
      case Rename(p, _) => p :: Nil
      case Extract(p, _, _) => p :: Nil
      case Synonym(inst) => inst.arguments
      case ClassLike(_, args) => args.toList.flatMap(_.values)
      case MatchedClassLike(_, fields) => fields.values
      case Record(fields) => fields.values
      case Tuple(leading, spread) => leading ::: spread.toList.flatMap:
        (_, middle, trailing) => middle :: trailing
      case _: (Literal | CharClass) => Nil
    children.foldLeft(1L): (size, child) =>
      (size + treeSize(child)) min (limit.toLong + 1)
  })

/** Instantiation and automata also bound the number of distinct graph nodes.
  * Each instantiation or string automaton build owns one of these budgets.
  */
private[ups] final class PatternCompilationBudget(using Config)
    extends PatternCompilationWorkBudget("patternCompilationWorkLimit", config.patternCompilationWorkLimit):

  def newState(existing: Int): Unit =
    if existing >= config.stringPatternStateLimit then
      throw PatternCompilationLimit("stringPatternStateLimit", config.stringPatternStateLimit)
    spend(1)

  def newSpecialization(existing: Int): Unit =
    if existing >= config.patternSpecializationLimit then
      throw PatternCompilationLimit("patternSpecializationLimit", config.patternSpecializationLimit)
    spend(1)
