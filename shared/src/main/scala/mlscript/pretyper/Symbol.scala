package mlscript
package pretyper

import annotation.tailrec, collection.immutable.SortedSet
import utils._, shorthands._, ucs.context.Matchable

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

    def showDbg: Str = s"${defn.kind.str} $name"
  }

  object TypeSymbol {
    def apply(defn: NuTypeDef): TypeSymbol =
      defn.kind match {
        case Cls => new ClassSymbol(defn, extractSuperTypes(defn.parents))
        case Als => new TypeAliasSymbol(defn)
        case Mxn => new MixinSymbol(defn)
        case Trt => new TraitSymbol(defn, extractSuperTypes(defn.parents))
        case Mod => new ModuleSymbol(defn, extractSuperTypes(defn.parents))
      }
    def unapply(symbol: TypeSymbol): Opt[NuTypeDef] = S(symbol.defn)

    private def extractSuperTypes(parents: Ls[Term]): Ls[Var] = {
      @tailrec
      def rec(acc: Ls[Var], rest: Ls[Term]): Ls[Var] =
        rest match {
          case Nil => acc.reverse
          case (nme: Var) :: tail => rec(nme :: acc, tail)
          case (TyApp(ty, _)) :: tail => rec(acc, ty :: tail)
          case (App(term, Tup(_))) :: tail => rec(acc, term :: tail)
          case head :: _ =>
            lastWords(s"unknown type in parent types: ${head.showDbg}")
        }
      rec(Nil, parents)
    }
  }

  /**
    * When a type symbol is not defined and we must need a symbol in some
    * scenarios, we use a dummy symbol to represent it.
    *
    * @param nme the name of the expect type symbol.
    */
  final class DummyClassSymbol(val nme: Var) extends ClassLikeSymbol {
    override val parentTypeNames: Ls[Var] = Nil
    
    override def defn: NuTypeDef = die

    override def name: Str = nme.name

    override def showDbg: Str = s"dummy class $name"
  }

  trait ClassLikeSymbol extends TypeSymbol {
    val parentTypeNames: Ls[Var]

    private val _baseClassLikeSymbols: Lazy[SortedSet[ClassLikeSymbol]] = new mlscript.utils.Lazy({
      implicit val ord: Ordering[ClassLikeSymbol] = new Ordering[ClassLikeSymbol] {
        override def compare(x: ClassLikeSymbol, y: ClassLikeSymbol): Int =
          x.name.compareTo(y.name)
      }
      val parentClassLikeSymbols = parentTypeNames.iterator.map(_.symbol).collect {
        case s: ClassLikeSymbol => s
      }.toList
      SortedSet.from(
        parentClassLikeSymbols.iterator ++
        parentClassLikeSymbols.iterator.flatMap(_.baseClassLikeSymbols))
    })

    lazy val baseClassLikeSymbols: SortedSet[ClassLikeSymbol] = _baseClassLikeSymbols.get_!

    def <:<(that: ClassLikeSymbol): Bool =
      this === that || baseClassLikeSymbols.contains(that)
  }

  final class ClassSymbol(
    override val defn: NuTypeDef,
    override val parentTypeNames: Ls[Var]
  ) extends ClassLikeSymbol {
    require(defn.kind === Cls)
  }

  final class TraitSymbol(
    override val defn: NuTypeDef,
    override val parentTypeNames: Ls[Var]
  ) extends ClassLikeSymbol {
    require(defn.kind === Trt)
  }

  final class MixinSymbol(override val defn: NuTypeDef) extends TypeSymbol {
    require(defn.kind === Mxn)
  }

  final class TypeAliasSymbol(override val defn: NuTypeDef) extends TypeSymbol {
    require(defn.kind === Als)
  }

  final class ModuleSymbol(
    override val defn: NuTypeDef,
    override val parentTypeNames: Ls[Var]
  ) extends ClassLikeSymbol with TermSymbol {
    require(defn.kind === Mod)

    override def nameVar: Var = defn.nameVar
  }

  sealed trait TermSymbol extends Symbol with Matchable {
    def nameVar: Var
  }

  class DefinedTermSymbol(val defn: NuFunDef) extends TermSymbol {
    override def name: Str = defn.name

    override def nameVar: Var = defn.nme

    def body: Term \/ Type = defn.rhs

    def isFunction: Bool = defn.isLetRec.isEmpty

    def isRecursive: Bool = defn.isLetRec.getOrElse(true)

    def isDeclaration: Bool = defn.rhs.isRight

    def operatorAlias: Opt[Var] = defn.symbolicNme

    def declaredLoc: Opt[Loc] = defn.nme.toLoc
  }

  class LocalTermSymbol(val nme: Var) extends TermSymbol {
    override def name: Str = nme.name

    override def nameVar: Var = nme
  }

  trait Symbolic {
    val name: String

    private var _symbol: Opt[Symbol] = N

    def symbolOption: Opt[Symbol] = _symbol
    def symbol: Symbol = _symbol.getOrElse(lastWords(s"Symbol not set for $name"))
    def symbol_=(symbol: Symbol): Unit =
      _symbol match {
        case N => _symbol = S(symbol)
        case S(`symbol`) => ()
        case S(current) =>
          println(s"symbol: old ${current.name} vs new ${symbol.name}")
          lastWords(s"Symbol already set for $name")
      }
    def withSymbol(symbol: Symbol): this.type = { this.symbol = symbol; this }

    def getClassLikeSymbol: Opt[ClassLikeSymbol] = _symbol.collectFirst {
      case symbol: ClassLikeSymbol => symbol
    }
  }
}
