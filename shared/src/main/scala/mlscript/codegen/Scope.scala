package mlscript.codegen

import mlscript.utils.shorthands._

class Scope(initialSymbols: Seq[Str], enclosing: Opt[Scope]) {
  def this() = this(Nil, None)

  def this(symbols: Seq[Str]) = this(symbols, None)

  // Declared JavaScript names in current scope.
  private val symbols = scala.collection.mutable.HashSet[Str](initialSymbols: _*)

  // If a symbol is re-declared, this map contains the actual JavaScript name.
  private val overrides =
    scala.collection.mutable.HashMap[Str, Str](symbols.toSeq.map(s => (s, s)): _*)

  private def declareJavaScriptName(name: Str): Unit = {
    if (symbols contains name) {
      throw new Exception(s"name \"$name\" already defined in this scope")
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
  def allocateJavaScriptName(): Str = {
    for (i <- 1 to Int.MaxValue; c <- Scope.nameAlphabet.combinations(i)) {
      val name = c.mkString
      if (!has(name)) {
        declareJavaScriptName(name)
        return name
      }
    }
    throw new Exception("Could not allocate a new symbol")
  }

  /**
    * Allocate a name with given prefix.
    */
  def allocateJavaScriptName(prefix: Str): Str = {
    // Try just prefix.
    if (!has(prefix)) {
      declareJavaScriptName(prefix)
      return prefix
    }
    // Try prefix with an integer.
    for (i <- 1 to Int.MaxValue) {
      val name = s"$prefix$i"
      if (!has(name)) {
        declareJavaScriptName(name)
        return name
      }
    }
    throw new Exception("Could not allocate a new symbol")
  }

  /**
    * Declare a name in current MLscript scope. The method returns corresponding
    * JavaScript name. 
    *
    * @param name the name to be declared in MLscript code
    * @return the actual name in JavaScript code
    */
  def declare(name: Str): Str = {
    if (symbols contains name) {
      val newName = allocateJavaScriptName(name)
      overrides += name -> newName
      newName
    } else {
      declareJavaScriptName(name)
      overrides += name -> name
      name
    }
  }

  /**
    * Resolve the JavaScript name for a given MLscript name.
    *
    * @param name the name to be declared in MLscript code
    * @return the actual name in JavaScript code
    */
  def resolve(name: Str): Str = (overrides get name) orElse {
    enclosing map { _ resolve name }
  } getOrElse name

  /**
    * Same as `resolve`, but returns the `Scope` where the name is defined.
    *
    * @param name
    * @return
    */
  def resolveWithScope(name: Str): (Str, Opt[Scope]) =
    overrides.get(name).map((_, S(this))) orElse {
      enclosing map { _.resolveWithScope(name) }
    } getOrElse (name, N)

  val isTopLevel: Bool = enclosing.isEmpty
}

object Scope {
  def apply(): Scope = new Scope()
  def apply(symbols: Seq[Str]): Scope = new Scope(symbols)
  def apply(symbols: Seq[Str], enclosing: Scope): Scope = new Scope(symbols, Some(enclosing))

  private val nameAlphabet = Ls.from("abcdefghijklmnopqrstuvwxyz")
}
