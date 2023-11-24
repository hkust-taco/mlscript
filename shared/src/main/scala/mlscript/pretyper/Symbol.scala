package mlscript.pretyper

import collection.mutable.{Buffer, Map => MutMap, Set => MutSet}
import mlscript.{NuFunDef, NuTypeDef, TypeName, Var}
import mlscript.utils._, shorthands._

sealed abstract class Symbol(val name: String)

final class TypeSymbol(val nme: TypeName, val defn: NuTypeDef) extends Symbol(nme.name) {
  var containedScope: Opt[Scope] = N
  var containedContents: Opt[TypeContents] = N

  def scope: Scope = containedScope.getOrElse(throw new Exception("Scope not set"))
  def contents: TypeContents = containedContents.getOrElse(throw new Exception("TypeContents not set")) 

  def scope_=(s: Scope): Unit = containedScope = S(s)
  def contents_=(c: TypeContents): Unit = containedContents = S(c)
}

sealed abstract class TermSymbol(name: String) extends Symbol(name)

final class FunctionSymbol(val nme: Var, val defn: NuFunDef) extends TermSymbol(nme.name) {
  var containedScope: Opt[Scope] = N

  def scope: Scope = containedScope.getOrElse(throw new Exception("Scope not set"))

  def scope_=(s: Scope): Unit = containedScope = S(s)
}

sealed abstract class ScrutineeSymbol(name: Str) extends TermSymbol(name) {
  val matchedClasses: MutSet[Var] = MutSet.empty
  /**
    * This map contains the sub-scrutinee symbols when this scrutinee is matched
    * against class patterns.
    */
  val classParameterScrutineeMap: MutMap[Var -> Int, SubValueSymbol] = MutMap.empty
  val tupleElementScrutineeMap: MutMap[Int, SubValueSymbol] = MutMap.empty
  val recordValueScrutineeMap: MutMap[Var, SubValueSymbol] = MutMap.empty

  def addSubScrutinee(className: Var, index: Int, parameter: Var): SubValueSymbol = {
    classParameterScrutineeMap.getOrElseUpdate(className -> index, {
      new SubValueSymbol(this, S(className) -> S(index), parameter.name)
    })
  }

  def addSubScrutinee(fieldName: Var): SubValueSymbol =
    recordValueScrutineeMap.getOrElseUpdate(fieldName, {
      val synthesizedName = s"${name}$$record${fieldName}"
      new SubValueSymbol(this, S(fieldName) -> N, synthesizedName)
    })
  
  def addSubScrutinee(index: Int): SubValueSymbol =
    tupleElementScrutineeMap.getOrElseUpdate(index, {
      val synthesizedName = s"${name}$$tuple${index.toString}"
      new SubValueSymbol(this, N -> S(index), synthesizedName)
    })

  /**
    * This buffer contains alias variables which created by "let" bindings or
    * alias patterns.
    */
  val aliases: Buffer[Var] = Buffer.empty
}

final class ValueSymbol(val nme: Var, val hoisted: Bool) extends ScrutineeSymbol(nme.name)

final class SubValueSymbol(
  val parentSymbol: ScrutineeSymbol,
  /**
    * TODO: This becomes useless now.
    * Class patterns: (S(className), S(index))
    * Record patterns: (S(fieldName), N)
    * Tuple patterns: (N, S(index))
    */
  val accessor: (Opt[Var], Opt[Int]),
  override val name: Str
) extends ScrutineeSymbol(name) {
  lazy val toVar: Var = Var(name)
}
