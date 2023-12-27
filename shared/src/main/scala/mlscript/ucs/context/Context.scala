package mlscript.ucs.context

import collection.mutable.{Buffer, Map => MutMap, SortedMap => MutSortedMap}
import mlscript.{If, Loc, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.pretyper.Scope
import mlscript.ucs.VariableGenerator
import mlscript.utils._, shorthands._

class Context(originalTerm: If) {
  private val prefix = Context.freshPrefix()
  private val cachePrefix = prefix + "$cache$"
  private val scrutineePrefix = prefix + "$scrut$"
  private val testPrefix = prefix + "$test$"
  private val shadowPrefix = prefix + "$shadow$"
  val unappliedPrefix: Str = prefix + "$args_"

  def isCacheVar(nme: Var): Bool = nme.name.startsWith(cachePrefix)
  def isScrutineeVar(nme: Var): Bool = nme.name.startsWith(scrutineePrefix)
  def isTestVar(nme: Var): Bool = nme.name.startsWith(testPrefix)
  def isUnappliedVar(nme: Var): Bool = nme.name.startsWith(unappliedPrefix)
  def isGeneratedVar(nme: Var): Bool =
    isCacheVar(nme) || isScrutineeVar(nme) || isTestVar(nme) || isUnappliedVar(nme)

  // Call these objects to generate fresh variables for different purposes.
  // I plan to mix the unique identifiers of UCS expressions into the prefixes.
  // So that the generated variables will definitely not conflict with others.
  val freshCache: VariableGenerator = new VariableGenerator(cachePrefix)
  val freshScrutineeVar: VariableGenerator = new VariableGenerator(scrutineePrefix)
  val freshTest: VariableGenerator = new VariableGenerator(testPrefix)
  val freshShadowed: VariableGenerator = new VariableGenerator(shadowPrefix)

  /** The buffer contains all `ScrutineeData` created within this context. */
  private val scrutineeBuffer: Buffer[ScrutineeData] = Buffer.empty

  def freshScrutinee: ScrutineeData = {
    val scrutinee = new ScrutineeData(this, N)
    scrutineeBuffer += scrutinee
    scrutinee
  }

  private[context] def freshScrutinee(parent: ScrutineeData): ScrutineeData = {
    val scrutinee = new ScrutineeData(this, S(parent))
    scrutineeBuffer += scrutinee
    scrutinee
  }

  /**
    * Create a `MatchRegistry` from the current context.
    */
  def toMatchRegistry: MatchRegistry =
    scrutineeBuffer.iterator.flatMap { scrutinee =>
      val caseSet = scrutinee.toCaseSet
      scrutinee.aliasesIterator.map(alias => (alias -> scrutinee) -> caseSet)
    }.toMap
}

object Context {
  // TODO: Generate fresh prefix in a determinstic way. I tried to use a counter,
  // but the produced value is not stable across different runs.
  def freshPrefix(): Str = "ucs"
}
