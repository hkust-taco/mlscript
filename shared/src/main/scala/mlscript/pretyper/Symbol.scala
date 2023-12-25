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

  // FIXME:
  // We should remove `ScrutineeSymbol` ASAP. There are too many reasons. The
  // most important one I can remember right now is that multiple variables
  // may share the same scrutinee symbol. But for now symbol must have a unique
  // name. We should use a dedicated symbol for tracking scrutinees.
  sealed abstract class ScrutineeSymbol(name: Str) extends TermSymbol(name) {
    def toLoc: Opt[Loc]

    val matchedClasses: MutMap[TypeSymbol, Buffer[Loc]] = MutMap.empty
    val unappliedVarMap: MutMap[TypeSymbol, Var] = MutMap.empty
    val subScrutineeMap: MutMap[TypeSymbol, MutMap[Int, MutMap[Var, ValueSymbol]]] = MutMap.empty
    // Hmm, maybe we can merge these three maps into one.
    // Urgh, let's do this in the next refactor.
    // I really should move these imperative and stateful functions to a
    // separate class!

    def getSubScrutineeSymbolOrElse(
        classLikeSymbol: TypeSymbol,
        index: Int,
        name: Var, // <-- Remove this parameter after we remove `ScrutineeSymbol`.
        default: => ValueSymbol
    ): ValueSymbol =
      subScrutineeMap.getOrElseUpdate(classLikeSymbol, MutMap.empty)
                     .getOrElseUpdate(index, MutMap.empty)
                     .getOrElseUpdate(name, default)

    def addMatchedClass(symbol: TypeSymbol, loc: Opt[Loc]): Unit = {
      matchedClasses.getOrElseUpdate(symbol, Buffer.empty) ++= loc
    }

    def getUnappliedVarOrElse(classLikeSymbol: TypeSymbol, default: => Var): Var =
      unappliedVarMap.getOrElseUpdate(classLikeSymbol, default)

    def addUnappliedVar(symbol: TypeSymbol, nme: Var): Unit = {
      unappliedVarMap += symbol -> nme
    }

    // Store the symbol of the parent scrutinee. I doubt if this is necessary.
    private var maybeParentSymbol: Opt[ScrutineeSymbol] = N
    def parentSymbol: Opt[ScrutineeSymbol] = maybeParentSymbol
    def withParentSymbol(parentSymbol: ScrutineeSymbol): this.type =
      maybeParentSymbol match {
        case N => maybeParentSymbol = S(parentSymbol); this
        case S(_) => throw new IllegalStateException("Parent symbol is already set.")
      }
  }

  final class ValueSymbol(val nme: Var, val hoisted: Bool) extends ScrutineeSymbol(nme.name) {
    override def toLoc: Opt[Loc] = nme.toLoc
  }
}