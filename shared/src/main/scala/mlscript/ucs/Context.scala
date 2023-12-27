package mlscript.ucs

import collection.mutable.{Buffer, Map => MutMap, SortedMap => MutSortedMap, Set => MutSet}
import mlscript.{If, Loc, NuFunDef, NuTypeDef, TypeName, Var}
import mlscript.{Cls, Trt, Mxn, Als, Mod}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.pretyper.Scope
import mlscript.utils._, shorthands._

class Context(originalTerm: If) {
  val prefix: Str = Context.freshPrefix().name

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
  val freshScrutinee: VariableGenerator = new VariableGenerator(scrutineePrefix)
  val freshTest: VariableGenerator = new VariableGenerator(testPrefix)
  val freshShadowed: VariableGenerator = new VariableGenerator("shadowed$")
}

object Context {
  private val freshPrefix = new VariableGenerator("ucs")
}
