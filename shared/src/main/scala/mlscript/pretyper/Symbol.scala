package mlscript.pretyper

import collection.mutable.{Buffer, Map => MutMap, Set => MutSet}
import mlscript.{Loc, NuFunDef, NuTypeDef, Term, Type, TypeName, Var}
import mlscript.{Cls, Trt, Mxn, Als, Mod}
import mlscript.utils._, shorthands._
import mlscript.ucs.context.Matchable

package object symbol {
  sealed trait Symbol {
    def name: Str

    def typeSymbolOption: Opt[TypeSymbol] = this match {
      case symbol: TypeSymbol => S(symbol)
      case _ => N
    }
    def termSymbolOption: Opt[TermSymbol] = this match {
      case symbol: TermSymbol => S(symbol)
      case _ => N
    }
  }

  sealed trait TypeSymbol extends Symbol {
    def defn: NuTypeDef
    
    override def name: Str = defn.name

    var baseTypes: Ls[TypeSymbol] = Nil
    var sealedDerivedTypes: Ls[TypeSymbol] = Nil

    @inline def hasBaseClass(baseClassLikeSymbol: TypeSymbol): Bool =
      baseTypes.exists(_ === baseClassLikeSymbol)

    def showDbg: Str = s"${defn.kind.str} $name"
  }

  object TypeSymbol {
    def apply(defn: NuTypeDef): TypeSymbol =
      defn.kind match {
        case Cls => new ClassSymbol(defn)
        case Als => new TypeAliasSymbol(defn)
        case Mxn => new MixinSymbol(defn)
        case Trt => new TraitSymbol(defn)
        case Mod => new ModuleSymbol(defn)
      }
    def unapply(symbol: TypeSymbol): Opt[NuTypeDef] = S(symbol.defn)
  }

  /**
    * When a type symbol is not defined and we must need a symbol in some
    * scenarios, we use a dummy symbol to represent it.
    *
    * @param nme the name of the expect type symbol.
    */
  final class DummyClassSymbol(val nme: Var) extends TypeSymbol {
    override def defn: NuTypeDef = die

    override def name: Str = nme.name

    override def showDbg: Str = s"dummy class $name"
  }

  final class ClassSymbol(override val defn: NuTypeDef) extends TypeSymbol {
    require(defn.kind === Cls)
  }

  final class TraitSymbol(override val defn: NuTypeDef) extends TypeSymbol {
    require(defn.kind === Trt)
  }

  final class MixinSymbol(override val defn: NuTypeDef) extends TypeSymbol {
    require(defn.kind === Mxn)
  }

  final class TypeAliasSymbol(override val defn: NuTypeDef) extends TypeSymbol {
    require(defn.kind === Als)
  }

  final class ModuleSymbol(override val defn: NuTypeDef) extends TypeSymbol with TermSymbol {
    require(defn.kind === Mod)
  }

  sealed trait TermSymbol extends Symbol with Matchable

  class DefinedTermSymbol(val defn: NuFunDef) extends TermSymbol {
    override def name: Str = defn.name

    def body: Term \/ Type = defn.rhs

    def isFunction: Bool = defn.isLetRec.isEmpty

    def isRecursive: Bool = defn.isLetRec.getOrElse(true)

    def isDeclaration: Bool = defn.rhs.isRight

    def operatorAlias: Opt[Var] = defn.symbolicNme
  }

  class LocalTermSymbol(val nme: Var) extends TermSymbol {
    override def name: Str = nme.name
  }
}
