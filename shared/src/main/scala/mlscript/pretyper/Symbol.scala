package mlscript.pretyper

import collection.mutable.{Buffer, Map => MutMap, Set => MutSet}
import mlscript.{Loc, NuFunDef, NuTypeDef, TypeName, Var}
import mlscript.{Cls, Trt, Mxn, Als, Mod}
import mlscript.utils._, shorthands._

package object symbol {
  sealed abstract class Symbol(val name: Str) {
    def typeSymbolOption: Opt[TypeSymbol] = this match {
      case symbol: TypeSymbol => S(symbol)
      case _ => N
    }
    def termSymbolOption: Opt[TermSymbol] = this match {
      case symbol: TermSymbol => S(symbol)
      case _ => N
    }
  }

  sealed abstract class TypeSymbol(val defn: NuTypeDef) extends Symbol(defn.name) {
    def scope: Scope = ???
    def contents: Map[Str, Symbol] = ???

    def complete(scope: Scope, contents: Map[Str, Symbol]): Unit = ???

    var baseTypes: Ls[TypeSymbol] = Nil
    var sealedDerivedTypes: Ls[TypeSymbol] = Nil

    @inline def hasSuperType(superType: TypeSymbol): Bool = baseTypes.exists(_ === superType)
  }

  final class ClassSymbol(/* enclosingScope: Scope, */ defn: NuTypeDef) extends TypeSymbol(defn) {
    require(defn.kind === Cls)
    // lazy val (scope, contents) = (enclosingScope.derive, Map.empty[Str, Symbol])
  }

  final class TraitSymbol(/* enclosingScope: Scope, */ defn: NuTypeDef) extends TypeSymbol(defn) {
    require(defn.kind === Trt)
    // lazy val (scope, contents) = (enclosingScope.derive, Map.empty[Str, Symbol])
  }

  final class MixinSymbol(/* enclosingScope: Scope, */ defn: NuTypeDef) extends TypeSymbol(defn) {
    require(defn.kind === Mxn)
    // lazy val (scope, contents) = (enclosingScope.derive, Map.empty[Str, Symbol])
  }

  final class TypeAliasSymbol(/* enclosingScope: Scope, */ defn: NuTypeDef) extends TypeSymbol(defn) {
    require(defn.kind === Als)
    // lazy val (scope, contents) = (enclosingScope.derive, Map.empty[Str, Symbol])
  }

  final class ModuleSymbol(/* enclosingScope: Scope, */ defn: NuTypeDef) extends TypeSymbol(defn) {
    require(defn.kind === Mod)
    // lazy val (scope, contents) = (enclosingScope.derive, Map.empty[Str, Symbol])
  }

  sealed abstract class TermSymbol(name: String) extends Symbol(name)

  final class FunctionSymbol(val defn: NuFunDef) extends TermSymbol(defn.nme.name) {
    require(defn.isLetRec.isEmpty)
    val nme: Var = defn.nme
    val operator: Opt[Var] = defn.symbolicNme
  }

  object FunctionSymbol {
    def unapply(symbol: TermSymbol): Opt[(Var, Opt[Var], NuFunDef)] =
      symbol match {
        case fs: FunctionSymbol => S(fs.nme, fs.operator, fs.defn)
        case _ => N
      }
  }

  sealed abstract class ScrutineeSymbol(name: Str) extends TermSymbol(name) {
    def toLoc: Opt[Loc]

    val matchedClasses: MutMap[TypeSymbol, Buffer[Loc]] = MutMap.empty
    val unappliedVarMap: MutMap[TypeSymbol, Var] = MutMap.empty
    // Hmm, maybe we can merge these two maps into one.

    def addMatchedClass(symbol: TypeSymbol, loc: Opt[Loc]): Unit = {
      matchedClasses.getOrElseUpdate(symbol, Buffer.empty) ++= loc
    }

    def addUnappliedVar(symbol: TypeSymbol, nme: Var): Unit = {
      unappliedVarMap += symbol -> nme
    }

    /**
      * This map contains the sub-scrutinee symbols when this scrutinee is matched
      * against class patterns.
      */
    val classParameterScrutineeMap: MutMap[Var -> Int, SubValueSymbol] = MutMap.empty
    val tupleElementScrutineeMap: MutMap[Int, SubValueSymbol] = MutMap.empty
    val recordValueScrutineeMap: MutMap[Var, SubValueSymbol] = MutMap.empty

    def addSubScrutinee(className: Var, index: Int, parameter: Var, loc: Opt[Loc]): SubValueSymbol = {
      classParameterScrutineeMap.getOrElseUpdate(className -> index, {
        new SubValueSymbol(this, S(className) -> S(index), parameter.name, loc)
      })
    }

    def addSubScrutinee(fieldName: Var, loc: Opt[Loc]): SubValueSymbol =
      recordValueScrutineeMap.getOrElseUpdate(fieldName, {
        val synthesizedName = s"${name}$$record${fieldName}"
        new SubValueSymbol(this, S(fieldName) -> N, synthesizedName, loc)
      })
    
    def addSubScrutinee(index: Int, loc: Opt[Loc]): SubValueSymbol =
      tupleElementScrutineeMap.getOrElseUpdate(index, {
        val synthesizedName = s"${name}$$tuple${index.toString}"
        new SubValueSymbol(this, N -> S(index), synthesizedName, loc)
      })

    /**
      * This buffer contains alias variables which created by "let" bindings or
      * alias patterns.
      */
    val aliases: Buffer[Var] = Buffer.empty
  }

  final class ValueSymbol(val nme: Var, val hoisted: Bool) extends ScrutineeSymbol(nme.name) {
    override def toLoc: Opt[Loc] = nme.toLoc
  }

  final class SubValueSymbol(
    val parentSymbol: ScrutineeSymbol,
    /**
      * TODO: This becomes useless now.
      * Class patterns: (S(className), S(index))
      * Record patterns: (S(fieldName), N)
      * Tuple patterns: (N, S(index))
      */
    val accessor: (Opt[Var], Opt[Int]),
    override val name: Str,
    override val toLoc: Opt[Loc]
  ) extends ScrutineeSymbol(name) {
    lazy val toVar: Var = Var(name)
  }
}