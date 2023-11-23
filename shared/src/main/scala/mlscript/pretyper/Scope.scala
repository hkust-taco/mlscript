package mlscript.pretyper

import collection.immutable.Map
import mlscript.utils._, shorthands._
import mlscript.Var

class Scope(val enclosing: Opt[Scope], val entries: Map[String, Symbol]) {
  @inline
  def get(name: String): Opt[Symbol] = entries.get(name) match {
    case Some(sym) => S(sym)
    case None => enclosing.fold(N: Opt[Symbol])(_.get(name))
  }

  @inline
  def +(sym: Symbol): Scope = new Scope(S(this), entries + (sym.name -> sym))

  @inline
  def ++(syms: IterableOnce[Symbol]): Scope =
    new Scope(S(this), entries ++ syms.iterator.map(sym => sym.name -> sym))

  def withEntries(syms: IterableOnce[Var -> Symbol]): Scope =
    new Scope(S(this), entries ++ syms.iterator.map {
      case (nme, sym) => nme.name -> sym
    })

  @inline
  def symbols: Iterable[Symbol] = entries.values

  def derive: Scope = new Scope(S(this), Map.empty)

  def showLocalSymbols: Str = entries.iterator.map(_._1).mkString(", ")
}

object Scope {
  def from(symbols: IterableOnce[Symbol]): Scope =
    new Scope(N, Map.from(symbols.iterator.map(sym => sym.name -> sym)))

  val global: Scope = Scope.from(
    """true,false,document,window,typeof,toString,not,succ,log,discard,negate,
      |round,add,sub,mul,div,sqrt,lt,le,gt,ge,slt,sle,sgt,sge,length,concat,eq,
      |ne,error,id,if,emptyArray,+,-,*,%,/,<,>,<=,>=,==,===,<>,&&,||"""
      .stripMargin
      .split(",")
      .iterator
      .map(name => new ValueSymbol(Var(name), false))
  )
}
