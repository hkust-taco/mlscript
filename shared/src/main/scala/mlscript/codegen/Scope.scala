package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.{JSStmt, JSExpr, JSLetDecl}
import mlscript.Type
import scala.reflect.ClassTag
import mlscript.{TypeName, Top, Bot, TypeDef, Als, Trt, Cls}
import mlscript.MethodDef
import mlscript.Term

class Scope(name: Str, enclosing: Opt[Scope]) {
  private val lexicalTypeSymbols = scala.collection.mutable.HashMap[Str, TypeSymbol]()
  private val lexicalValueSymbols = scala.collection.mutable.HashMap[Str, RuntimeSymbol]()
  private val runtimeSymbols = scala.collection.mutable.HashSet[Str]()

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
    register(TypeAliasSymbol("anything", Nil, Top))
    register(TypeAliasSymbol("nothing", Nil, Bot))
    // TODO: register them in the same way as `Typer` does.
    Ls("int", "number", "bool", "string", "unit") foreach { name =>
      register(TypeAliasSymbol(name, Nil, TypeName(name)))
    }
  }

  /**
    * Shorthands for creating function scopes.
    */
  def this(name: Str, params: Ls[Str], enclosing: Scope) = {
    this(name, Opt(enclosing))
    params foreach { param =>
      // TODO: avoid reserved keywords.
      val symbol = ValueSymbol(param, param)
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
    if (!runtimeSymbols.contains(prefix) && !Symbol.isKeyword(prefix)) {
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
    throw CodeGenError(
      if (prefix.isEmpty())
        "Cannot allocate a runtime name"
      else
        s"Cannot allocate a runtime name starting with '$prefix'"
    )
  }

  private def register(symbol: TypeAliasSymbol): Unit = {
    lexicalTypeSymbols.put(symbol.lexicalName, symbol)
    ()
  }

  /**
    * Register a lexical symbol in both runtime name set and lexical name set.
    */
  private def register(symbol: TypeSymbol with RuntimeSymbol): Unit = {
    lexicalTypeSymbols.put(symbol.lexicalName, symbol)
    lexicalValueSymbols.put(symbol.lexicalName, symbol)
    runtimeSymbols += symbol.runtimeName
    ()
  }

  /**
    * Register a lexical symbol in both runtime name set and lexical name set.
    */
  private def register(symbol: RuntimeSymbol): Unit = {
    lexicalValueSymbols.put(symbol.lexicalName, symbol)
    runtimeSymbols += symbol.runtimeName
    ()
  }

  private def unregister(symbol: ValueSymbol): Unit = {
    lexicalTypeSymbols.remove(symbol.lexicalName)
    runtimeSymbols.remove(symbol.runtimeName)
    ()
  }

  def getType(name: Str): Opt[TypeSymbol] = lexicalTypeSymbols.get(name)

  /**
   * Look up for a class symbol locally.
   */
  def getClassSymbol(name: Str): Opt[ClassSymbol] =
    lexicalTypeSymbols.get(name) flatMap {
      _ match {
        case c: ClassSymbol => S(c)
        case _              => N
      }
    }

  /**
   * Look up for a type alias symbol locally.
   */
  def getTypeAliasSymbol(name: Str): Opt[TypeAliasSymbol] =
    lexicalTypeSymbols.get(name) flatMap {
      _ match {
        case c: TypeAliasSymbol => S(c)
        case _                  => N
      }
    }

  /**
   * Look up for a type symbol locally.
   */
  def getTypeSymbol(name: Str): Opt[TypeSymbol] = lexicalTypeSymbols.get(name)

  def resolveValue(name: Str): Opt[RuntimeSymbol] =
    lexicalValueSymbols.get(name).orElse(enclosing.flatMap(_.resolveValue(name)))

  /**
    * Find the base class for a specific class.
    */
  def resolveBaseClass(ty: Type): Opt[ClassSymbol] = {
    val baseClasses = ty.collectTypeNames.flatMap { name =>
      this.getType(name) match {
        case S(sym: ClassSymbol) => S(sym)
        case S(sym: TraitSymbol) => N
        case S(sym: TypeAliasSymbol) =>
          throw new CodeGenError(s"cannot inherit from type alias $name" )
        case N =>
          throw new CodeGenError(s"undeclared type name $name when resolving base classes")
      }
    }
    if (baseClasses.length > 1)
      throw CodeGenError(
        s"cannot have ${baseClasses.length} base classes: " +
        baseClasses.map { _.lexicalName }.mkString(", ")
      )
    else
      baseClasses.headOption
  }

  def declareTypeSymbol(typeDef: TypeDef): TypeSymbol = typeDef match {
    case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
      declareTypeAlias(name, tparams map { _.name }, body)
    case TypeDef(Trt, TypeName(name), tparams, body, _, _) =>
      declareTrait(name, tparams map { _.name }, body)
    case TypeDef(Cls, TypeName(name), tparams, baseType, _, members) =>
      declareClass(name, tparams map { _.name }, baseType, members)
  }

  def declareClass(
      lexicalName: Str,
      params: Ls[Str],
      base: Type,
      methods: Ls[MethodDef[Left[Term, Type]]]
  ): ClassSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = ClassSymbol(lexicalName, runtimeName, params.sorted, base, methods)
    register(symbol)
    symbol
  }

  def declareTrait(lexicalName: Str, params: Ls[Str], base: Type): TraitSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = TraitSymbol(lexicalName, runtimeName, params, base)
    register(symbol)
    symbol
  }

  def declareTypeAlias(lexicalName: Str, params: Ls[Str], ty: Type): TypeAliasSymbol = {
    val symbol = TypeAliasSymbol(lexicalName, params, ty)
    register(symbol)
    symbol
  }

  def declareValue(lexicalName: Str): ValueSymbol = {
    val runtimeName = lexicalValueSymbols.get(lexicalName) match {
      // If we are implementing a stub symbol and the stub symbol did not shadow any other
      // symbols, it is safe to reuse its `runtimeName`.
      case S(sym: StubValueSymbol) if !sym.shadowing => sym.runtimeName
      case S(sym: BuiltinSymbol) if !sym.accessed    => sym.runtimeName
      case _                                         => allocateRuntimeName(lexicalName)
    }
    val symbol = ValueSymbol(lexicalName, runtimeName)
    register(symbol)
    symbol
  }

  def declareStubValue(lexicalName: Str)(implicit accessible: Bool): StubValueSymbol =
    declareStubValue(lexicalName, N)

  def declareStubValue(lexicalName: Str, previous: StubValueSymbol)(implicit
      accessible: Bool
  ): StubValueSymbol =
    declareStubValue(lexicalName, S(previous))

  private def declareStubValue(lexicalName: Str, previous: Opt[StubValueSymbol])(implicit
      accessible: Bool
  ): StubValueSymbol = {

    val symbol = lexicalValueSymbols.get(lexicalName) match {
      // If a stub with the same name has been defined, use the name.
      case S(value) => StubValueSymbol(lexicalName, value.runtimeName, true, previous)
      // Otherwise, we will allocate a new name.
      case N => StubValueSymbol(lexicalName, allocateRuntimeName(lexicalName), false, previous)
    }
    register(symbol)
    symbol
  }

  def stubize(sym: ValueSymbol, previous: StubValueSymbol)(implicit
      accessible: Bool
  ): StubValueSymbol = {
    unregister(sym)
    declareStubValue(sym.lexicalName, S(previous))
  }

  def declareRuntimeSymbol(): Str = {
    val name = allocateRuntimeName()
    runtimeSymbols += name
    name
  }

  def declareRuntimeSymbol(prefix: Str): Str = {
    val name = allocateRuntimeName(prefix)
    runtimeSymbols += name
    name
  }

  def existsRuntimeSymbol(name: Str): Bool = runtimeSymbols.contains(name)

  /**
    * Shorthands for deriving normal scopes.
    */
  def derive(name: Str): Scope = new Scope(name, S(this))

  /**
    * Shorthands for deriving function scopes.
    */
  def derive(name: Str, params: Ls[Str]): Scope = Scope(name, params, this)

  /**
    * An iterator over the type symbols declared in the current scope
    */
  def iterateTypeSymbols: Iterable[TypeSymbol] = lexicalTypeSymbols.values
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

/**
  * This class collects temporary variables declared during translation and
  * generates JavaScript declarations for them after the translation.
  */
final case class TemporaryVariableEmitter() {
  private val names = scala.collection.mutable.HashSet[Str]()

  /**
    * Add a new variable name. The name must be a runtime name.
    */
  def +=(name: Str): Unit = names += name

  /**
    * Emit a `let`-declaration for collected names and clear the collection.
    */
  def emit(): Opt[JSLetDecl] = if (names.isEmpty) {
    N
  } else {
    val decl = JSLetDecl.from(names.toList)
    names.clear()
    S(decl)
  }

  /**
    * Get all names and clear the collection.
    */
  def get(): Ls[Str] = {
    val vars = names.toList
    names.clear()
    vars
  }

  /**
    * A helper method to prepend the declaration to given statements. This calls
    * `emit` so the name collection will be cleared.
    */
  def `with`(stmts: Ls[JSStmt]): Ls[JSStmt] =
    emit() match {
      case S(decl) => decl :: stmts
      case N       => stmts
    }

  /**
    * A helper method to prepend temp variable declarations to given expression.
    * If no temp variables, return the expression as `Left`. This calls `emit`
    * so the name collection will be cleared.
    */
  def `with`(expr: JSExpr): JSExpr \/ Ls[JSStmt] =
    emit() match {
      case S(decl) => R(decl :: expr.`return` :: Nil)
      case N       => L(expr)
    }
}
