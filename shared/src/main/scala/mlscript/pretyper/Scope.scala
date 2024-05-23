package mlscript
package pretyper

import annotation.tailrec, collection.immutable.Map
import utils._, shorthands._, symbol._

final class Scope(val enclosing: Opt[Scope], val types: Map[Str, TypeSymbol], val terms: Map[Str, TermSymbol]) {
  import Scope._


  @tailrec
  final def getTypeSymbol(name: Str): Opt[TypeSymbol] =
    types.get(name) match {
      case entry @ S(_) => entry
      case N => enclosing match {
        case N => N
        case S(scope) => scope.getTypeSymbol(name)
      }
    }

  @tailrec
  final def getTermSymbol(name: Str): Opt[TermSymbol] =
    terms.get(name) match {
      case entry @ S(_) => entry
      case N => enclosing match {
        case N => N
        case S(scope) => scope.getTermSymbol(name)
      }
    }
  
  final def getSymbols(name: Str): Ls[Symbol] = Ls.concat(getTypeSymbol(name), getTermSymbol(name))

  @inline
  def +(sym: Symbol): Scope = sym match {
    case symbol: ModuleSymbol => new Scope(enclosing, types + (symbol.name -> symbol), terms + (symbol.name -> symbol))
    case symbol: TypeSymbol => new Scope(enclosing, types + (symbol.name -> symbol), terms)
    case symbol: DefinedTermSymbol =>
      val newTerms = terms + (symbol.name -> symbol)
      new Scope(enclosing, types, symbol.operatorAlias match {
        case N => newTerms
        case S(alias) => newTerms + (alias.name -> symbol)
      })
    case symbol: TermSymbol => new Scope(enclosing, types, terms + (symbol.name -> symbol))
  }

  @inline
  def ++(symbols: IterableOnce[Symbol]): Scope = {
    val (newTypes, newTerms) = partitionSymbols((types, terms), symbols)
    new Scope(enclosing, newTypes, newTerms)
  }

  def withEntries(syms: IterableOnce[Var -> Symbol]): Scope = {
    val (newTypes, newTerms) = syms.iterator.foldLeft((types, terms)) {
      case ((types, terms), (nme, symbol: ModuleSymbol)) => (types + (nme.name -> symbol), terms + (nme.name -> symbol))
      case ((types, terms), (nme, symbol: TypeSymbol)) => (types + (nme.name -> symbol), terms)
      case ((types, terms), (nme, symbol: TermSymbol)) => (types, terms + (nme.name -> symbol))
    }
    new Scope(enclosing, newTypes, newTerms)
  }

  @inline
  def symbols: Iterator[Symbol] = Iterator.concat[Symbol](types.values, terms.values)

  def derive: Scope = new Scope(S(this), Map.empty, Map.empty)

  def derive(symbols: IterableOnce[Symbol]): Scope = {
    val (newTypes, newTerms) = partitionSymbols((types, terms), symbols)
    new Scope(S(this), newTypes, newTerms)
  }

  def showLocalSymbols: Str = symbols.iterator.map(_.name).mkString(", ")
}

object Scope {
  def partitionSymbols(
      z: (Map[Str, TypeSymbol], Map[Str, TermSymbol]),
      symbols: IterableOnce[Symbol]
  ): (Map[Str, TypeSymbol], Map[Str, TermSymbol]) =
    symbols.iterator.foldLeft((z._1, z._2)) {
      case ((types, terms), symbol: ModuleSymbol) => (types + (symbol.name -> symbol), terms + (symbol.name -> symbol))
      case ((types, terms), symbol: TypeSymbol) => (types + (symbol.name -> symbol), terms)
      case ((types, terms), symbol: DefinedTermSymbol) =>
        (types, terms + (symbol.name -> symbol) ++ symbol.operatorAlias.map(_.name -> symbol))
      case ((types, terms), symbol: TermSymbol) => (types, terms + (symbol.name -> symbol))
    }

  def from(symbols: IterableOnce[Symbol]): Scope = {
    val (newTypes, newTerms) = partitionSymbols((Map.empty, Map.empty), symbols)
    new Scope(N, newTypes, newTerms)
  }

  val global: Scope = {
    def mod(name: Str) = NuTypeDef(Mod, TypeName(name), Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, N, Nil)
    // def cls(name: Str) = NuTypeDef(Trt, TypeName(name), Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, N)
    def als(name: Str) = NuTypeDef(Als, TypeName(name), Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, N, Nil)
    val builtinTypes = Ls(
      new ModuleSymbol(mod("true"), Nil),
      new ModuleSymbol(mod("false"), Nil),
      new TypeAliasSymbol(als("nothing")),
      new DummyClassSymbol(Var("Object")),
      new DummyClassSymbol(Var("Int")),
      new DummyClassSymbol(Var("Num")),
      new DummyClassSymbol(Var("Str")),
      new DummyClassSymbol(Var("Bool")),
    )
    val commaSymbol = new LocalTermSymbol(Var(","))
    Scope.from(
      """true,false,document,window,typeof,toString,not,succ,log,discard,negate,
        |round,add,sub,mul,div,sqrt,lt,le,gt,ge,slt,sle,sgt,sge,length,concat,
        |join,eq,ne,error,id,if,emptyArray,
        |+,-,*,%,/,**,<,>,<=,>=,==,===,<>,&&,||,and,
        |numAdd,numSub,numMul,NaN"""
        .stripMargin
        .split(",")
        .iterator
        .map(_.trim)
        .map(name => new LocalTermSymbol(Var(name)))
        .concat(commaSymbol :: builtinTypes)
    )
  }
}
