package mlscript.pretyper

import collection.mutable.{Buffer, Map => MutMap, Set => MutSet}
import mlscript.{Loc, NuFunDef, NuTypeDef, TypeName, Var}
import mlscript.{Cls, Trt, Mxn, Als, Mod}
import mlscript.utils._, shorthands._
import mlscript.ucs.{Context, ScrutineeData}

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

  sealed abstract class TermSymbol(name: String) extends Symbol(name) {
    private val scrutinees: MutMap[Context, ScrutineeData] = MutMap.empty
    
    def getOrCreateScrutinee(implicit context: Context): ScrutineeData =
      scrutinees.getOrElseUpdate(context, context.freshScrutinee)

    def getScrutinee(implicit context: Context): Opt[ScrutineeData] =
      scrutinees.get(context)

    def isScrutinee(implicit context: Context): Bool = scrutinees.contains(context)

    def addScrutinee(scrutinee: ScrutineeData)(implicit context: Context): Unit = {
      require(!isScrutinee)
      scrutinees += context -> scrutinee
    }
  }

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

  final class ValueSymbol(val nme: Var, val hoisted: Bool) extends TermSymbol(nme.name)
}