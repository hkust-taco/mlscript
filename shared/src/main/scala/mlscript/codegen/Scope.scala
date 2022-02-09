package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.{JSStmt, JSExpr, JSLetDecl}
import mlscript.Type
import scala.reflect.ClassTag
import mlscript.{TypeName, Top, Bot}

class Scope(name: Str, enclosing: Opt[Scope]) {
  private val lexicalTypeSymbols = scala.collection.mutable.HashMap[Str, TypeSymbol]()
  private val lexicalValueSymbols = scala.collection.mutable.HashMap[Str, ValueSymbol]()
  private val runtimeSymbols = scala.collection.mutable.HashMap[Str, RuntimeSymbol]()

  val tempVars: TemporaryVariableEmitter = TemporaryVariableEmitter()

  /**
    * Shorthands for creating top-level scopes.
    */
  def this(name: Str) = {
    this(name, N)
    // TODO: allow types and values to have the same name
    // TODO: read built-in symbols from `Typer`.
    Ls(
      "true",
      "false",
      "id",
      "succ",
      "error",
      "concat",
      "add",
      "sub",
      "mul",
      "div",
      "gt",
      "not",
      "toString",
      "negate"
    ) foreach { name =>
      register(BuiltinSymbol(name, name))
    }
    // TODO: add `true`, `false`, and `error` to this list
    register(TypeSymbol("anything", "anything", Nil, Top))
    register(TypeSymbol("nothing", "nothing", Nil, Bot))
    // TODO: register them in the same way as `Typer` does.
    Ls("int", "number", "bool", "string", "unit") foreach { name =>
      register(TypeSymbol(name, name, Nil, TypeName(name)))
    }
  }

  /**
    * Shorthands for creating function scopes.
    */
  def this(name: Str, params: Ls[Str], enclosing: Scope) = {
    this(name, Opt(enclosing))
    params foreach { param =>
      // TODO: avoid reserved keywords.
      val symbol = ParamSymbol(param, param)
      register(symbol)
    }
  }

  private val allocateRuntimeNameIter = for {
    i <- (1 to Int.MaxValue).iterator
    c <- Scope.nameAlphabet.combinations(i)
    name = c.mkString
    if !runtimeSymbols.contains(name)
  } yield {
    name
  }

  /**
    * Allocate a non-sense runtime name.
    */
  private def allocateRuntimeName(): Str = allocateRuntimeNameIter.next()

  /**
    * Allocate a runtime name starting with the given prefix.
    */
  private def allocateRuntimeName(prefix: Str): Str = {
    // Fallback case.
    if (prefix.isEmpty()) {
      return allocateRuntimeName()
    }
    // Try just prefix.
    if (!runtimeSymbols.contains(prefix)) {
      return prefix
    }
    // Try prefix with an integer.
    for (i <- 1 to Int.MaxValue) {
      val name = s"$prefix$i"
      if (!runtimeSymbols.contains(name)) {
        return name
      }
    }
    // Give up.
    throw new CodeGenError(
      if (prefix.isEmpty())
        "Cannot allocate a runtime name"
      else
        s"Cannot allocate a runtime name starting with '$prefix'"
    )
  }

  /**
    * Register a lexical symbol in both runtime name set and lexical name set.
    */
  private def register(symbol: TypeSymbol): Unit = {
    lexicalTypeSymbols.put(symbol.lexicalName, symbol)
    runtimeSymbols.put(symbol.runtimeName, symbol)
    ()
  }

  /**
    * Register a lexical symbol in both runtime name set and lexical name set.
    */
  private def register(symbol: ValueSymbol): Unit = {
    lexicalValueSymbols.put(symbol.lexicalName, symbol)
    runtimeSymbols.put(symbol.runtimeName, symbol)
    ()
  }

  private def unregister(symbol: ValueSymbol): Unit = {
    lexicalTypeSymbols.remove(symbol.lexicalName)
    runtimeSymbols.remove(symbol.runtimeName)
    ()
  }

  /**
   * Look up for a symbol locally. 
   */
  def get(name: Str): LexicalSymbol =
    lexicalValueSymbols
      .get(name)
      .getOrElse(lexicalTypeSymbols.get(name).getOrElse(FreeSymbol(name)))

  def getType(name: Str): Opt[TypeSymbol] = lexicalTypeSymbols.get(name)

  /**
   * Look up for a class symbol locally.
   */
  def expect[T <: TypeSymbol](name: Str)(implicit tag: ClassTag[T]): Opt[T] =
    lexicalTypeSymbols.get(name) flatMap {
      _ match {
        case c: T => S(c)
        case _    => N
      }
    }

  /**
   * Check whether a lexical name is used.
   */
  def declared(lexicalName: Str): Boolean =
    lexicalValueSymbols.contains(lexicalName) ||
      lexicalTypeSymbols.contains(lexicalName)

  /**
    * Look up for a symbol recursively.
    */
  def resolve(name: Str): LexicalSymbol =
    lexicalValueSymbols.get(name) match {
      case S(sym) => sym
      case N =>
        lexicalTypeSymbols.get(name) match {
          case S(sym) => sym
          case N =>
            enclosing match {
              case S(scope) => scope.resolve(name)
              case N        => FreeSymbol(name)
            }
        }
    }

  def declareClass(lexicalName: Str, params: Ls[Str], base: Type): ClassSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = ClassSymbol(lexicalName, runtimeName, params, base, this)
    register(symbol)
    symbol
  }

  def declareTrait(lexicalName: Str, params: Ls[Str], base: Type): TraitSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = TraitSymbol(lexicalName, runtimeName, params, base)
    register(symbol)
    symbol
  }

  def declareType(lexicalName: Str, params: Ls[Str], ty: Type): TypeSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = TypeSymbol(lexicalName, runtimeName, params, ty)
    register(symbol)
    symbol
  }

  def declareValue(lexicalName: Str): ValueSymbol = {
    val runtimeName = lexicalValueSymbols.get(name) match {
      case S(sym: StubValueSymbol) => sym.runtimeName
      case _                       => allocateRuntimeName(lexicalName)
    }
    val symbol = ValueSymbol(lexicalName, runtimeName)
    register(symbol)
    symbol
  }

  def declareStubValue(lexicalName: Str): StubValueSymbol =
    declareStubValue(lexicalName, N)

  def declareStubValue(lexicalName: Str, previous: StubValueSymbol): StubValueSymbol =
    declareStubValue(lexicalName, S(previous))

  private def declareStubValue(lexicalName: Str, previous: Opt[StubValueSymbol]): StubValueSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = StubValueSymbol(lexicalName, runtimeName, previous)
    register(symbol)
    symbol
  }

  def stubize(sym: ValueSymbol, previous: StubValueSymbol): StubValueSymbol = {
    unregister(sym)
    declareStubValue(sym.lexicalName, S(previous))
  }

  def declareRuntimeSymbol(): Str = {
    val name = allocateRuntimeName()
    runtimeSymbols.put(name, TemporarySymbol(name))
    name
  }

  def declareRuntimeSymbol(prefix: Str): Str = {
    val name = allocateRuntimeName(prefix)
    runtimeSymbols.put(name, TemporarySymbol(name))
    name
  }

  /**
    * Shorthands for deriving normal scopes.
    */
  def derive(name: Str): Scope = new Scope(name, S(this))

  /**
    * Shorthands for deriving function scopes.
    */
  def derive(name: Str, params: Ls[Str]): Scope = Scope(name, params, this)
}

object Scope {

  /**
  * Shorthands for creating top-level scopes.
  */
  def apply(name: Str): Scope = new Scope(name)

  /**
    * Shorthands for creating function scopes.
    */
  def apply(name: Str, params: Ls[Str], enclosing: Scope): Scope =
    new Scope(name, params, enclosing)

  private val nameAlphabet: Ls[Char] = Ls.from("abcdefghijklmnopqrstuvwxyz")
}

final case class TemporaryVariableEmitter() {
  private val names = scala.collection.mutable.HashSet[Str]()

  def +=(name: Str): Unit = names += name

  def emit(): Opt[JSLetDecl] = if (names.isEmpty) {
    N
  } else {
    val decl = JSLetDecl.from(names.toList)
    names.clear()
    S(decl)
  }

  def get(): Ls[Str] = {
    val vars = names.toList
    names.clear()
    vars
  }

  /**
    * Prepend temp variable declarations to given statements.
    */
  def `with`(stmts: Ls[JSStmt]): Ls[JSStmt] =
    emit() match {
      case S(decl) => decl :: stmts
      case N       => stmts
    }

  /**
    * Prepend temp variable declarations to given expression. If no temp variables,
    * return the expression as `Left`.
    */
  def `with`(expr: JSExpr): JSExpr \/ Ls[JSStmt] =
    emit() match {
      case S(decl) => R(decl :: expr.`return` :: Nil)
      case N       => L(expr)
    }
}
