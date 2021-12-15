package mlscript.codegen

import mlscript.utils.shorthands._

class Scope(initialSymbols: Seq[Str], enclosing: Opt[Scope]) {
  private val symbols = scala.collection.mutable.HashSet[Str](initialSymbols: _*)

  def this() = this(Nil, None)

  def this(symbols: Seq[Str]) = this(symbols, None)

  def add(name: Str): Unit = {
    if (symbols.contains(name)) {
      throw new Exception(s"Symbol $name already defined in this scope")
    }
    symbols += name
  }

  def has(name: Str): Boolean = (symbols contains name) || (enclosing match {
    case Some(scope) => scope.has(name)
    case None        => false
  })

  /**
    * Allocate a alphabetic name for new symbol.
    * The name is guaranteed to be unique in this scope.
    */
  def allocate(): Str = {
    for (i <- 1 to Int.MaxValue; c <- Scope.nameAlphabet.combinations(i)) {
      val name = c.mkString
      if (!has(name)) {
        add(name)
        return name
      }
    }
    throw new Exception("Could not allocate a new symbol")
  }

  /**
    * Allocate a name with given prefix.
    */
  def allocate(prefix: Str): Str = {
    // Try just prefix.
    if (!has(prefix)) {
      add(prefix)
      return prefix
    }
    // Try prefix with an integer.
    for (i <- 1 to Int.MaxValue) {
      val name = s"$prefix$i"
      if (!has(name)) {
        add(name)
        return name
      }
    }
    throw new Exception("Could not allocate a new symbol")
  }
}

object Scope {
  def apply(symbols: Seq[Str]): Scope = new Scope(symbols)
  def apply(symbols: Seq[Str], enclosing: Scope): Scope = new Scope(symbols, Some(enclosing))

  private val nameAlphabet = Ls.from("abcdefghijklmnopqrstuvwxyz")
}
