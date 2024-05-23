package mlscript
package ucs
package context

import collection.mutable.{Buffer, Map => MutMap}
import utils._, shorthands._
import pretyper.symbol.{DummyClassSymbol, TypeSymbol}
import pretyper.Scope

class Context(originalTerm: If) {
  /** The prefix of all prefixes. */
  private val prefix = Context.freshPrefix
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

  // Symbol Management
  // =================

  private val dummyClassSymbols: MutMap[Var, DummyClassSymbol] = MutMap.empty
  def getOrCreateDummyClassSymbol(nme: Var): DummyClassSymbol =
    dummyClassSymbols.getOrElseUpdate(nme, new DummyClassSymbol(nme))

  // Scrutinee Management
  // ====================

  /** The buffer contains all `ScrutineeData` created within this context. */
  private val scrutineeBuffer: Buffer[Scrutinee] = Buffer.empty

  def freshScrutinee: Scrutinee = {
    val scrutinee = new Scrutinee(this, N)
    scrutineeBuffer += scrutinee
    scrutinee
  }

  private[context] def freshScrutinee(parent: Scrutinee): Scrutinee = {
    val scrutinee = new Scrutinee(this, S(parent))
    scrutineeBuffer += scrutinee
    scrutinee
  }

  def scrutinees: Iterator[Scrutinee] = scrutineeBuffer.iterator
}

object Context {
  private val freshPrefix: Str = "ucs"
}
