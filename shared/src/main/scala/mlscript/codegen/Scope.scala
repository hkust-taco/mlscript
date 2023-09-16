package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.{JSStmt, JSExpr, JSLetDecl}
import mlscript.Type
import scala.reflect.ClassTag
import mlscript.{TypeName, Top, Bot, TypeDef, Als, Trt, Cls, Mod, Mxn}
import mlscript.{MethodDef, Var}
import mlscript.{Term, Statement, Record}
import mlscript.utils.{AnyOps, lastWords}
import mlscript.JSField
import mlscript.{NuTypeDef, NuFunDef}

class Scope(name: Str, enclosing: Opt[Scope]) {
  private val lexicalTypeSymbols = scala.collection.mutable.HashMap[Str, TypeSymbol]()
  private val lexicalValueSymbols = scala.collection.mutable.HashMap[Str, RuntimeSymbol]()
  private val runtimeSymbols = scala.collection.mutable.HashSet[Str]()

  // To allow a class method/getter/constructor to access members of an outer class,
  // we insert `const outer = this;` before the class definition starts.
  // To access ALL outer variables correctly, we need to make sure
  // none of them would be shadowed.
  private val outerSymbols = scala.collection.mutable.HashSet[Str]()

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
      "NaN",
      "id",
      "emptyArray",
      "succ",
      "error",
      "length",
      "concat",
      "add",
      "sub",
      "mul",
      "div",
      "gt",
      "not",
      "ne",
      "eq",
      "sgt",
      "slt",
      "sge",
      "sle",
      "typeof",
      "toString",
      "negate",
      "eq",
      "unit",
      "log",
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

  private val allocateRuntimeNameIter = for {
    i <- (1 to Int.MaxValue).iterator
    c <- Scope.nameAlphabet.combinations(i)
    name = c.mkString
    if !hasRuntimeName(name)
  } yield {
    name
  }

  /**
    * Check if a runtime name is used recursively.
    *
    * @param name the name
    * @return whether it's available or not
    */
  private def hasRuntimeName(name: Str): Bool =
    runtimeSymbols.contains(name) || enclosing.exists(_.hasRuntimeName(name))

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
    // Replace ticks
    val realPrefix = Scope.replaceTicks(prefix)
    // Try just prefix.
    if (!runtimeSymbols.contains(realPrefix) && !Symbol.isKeyword(realPrefix)) {
      return realPrefix
    }
    // Try prefix with an integer.
    for (i <- 1 to Int.MaxValue) {
      val name = s"$realPrefix$i"
      if (!runtimeSymbols.contains(name)) {
        return name
      }
    }
    // Give up.
    throw CodeGenError(
      if (realPrefix.isEmpty())
        "Cannot allocate a runtime name"
      else
        s"Cannot allocate a runtime name starting with '$realPrefix'"
    )
  }

  private def register(symbol: TypeAliasSymbol): Unit = {
    lexicalTypeSymbols.put(symbol.lexicalName, symbol)
    ()
  }

  /**
    * Register a lexical symbol in both runtime name set and lexical name set.
    */
  def register(symbol: TypeSymbol with RuntimeSymbol): Unit = {
    lexicalTypeSymbols.put(symbol.lexicalName, symbol)
    lexicalValueSymbols.put(symbol.lexicalName, symbol)
    runtimeSymbols += symbol.runtimeName
    ()
  }

  /**
    * Register a lexical symbol in both runtime name set and lexical name set.
    */
  def register(symbol: RuntimeSymbol): Unit = {
    lexicalValueSymbols.put(symbol.lexicalName, symbol)
    runtimeSymbols += symbol.runtimeName
    ()
  }

  private def unregister(symbol: ValueSymbol): Unit = {
    lexicalTypeSymbols.remove(symbol.lexicalName)
    runtimeSymbols.remove(symbol.runtimeName)
    ()
  }

  def unregisterSymbol(symbol: ValueSymbol): Unit = {
    unregister(symbol)
  }

  def getType(name: Str): Opt[TypeSymbol] = lexicalTypeSymbols.get(name)

  /**
   * Look up for a class symbol locally.
   */
  def getClassSymbol(name: Str): Opt[ClassSymbol] =
    lexicalTypeSymbols.get(name) collect { case c: ClassSymbol => c }

  /**
   * Look up a trait symbol locally.
   */
  def getTraitSymbol(name: Str): Opt[TraitSymbol] = 
    lexicalTypeSymbols.get(name) collect { case c: TraitSymbol => c }

  /**
   * Look up a type alias symbol locally.
   */
  def getTypeAliasSymbol(name: Str): Opt[TypeAliasSymbol] =
    lexicalTypeSymbols.get(name) collect { case c: TypeAliasSymbol => c }

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
        case S(_: NuTypeSymbol) =>
          throw new CodeGenError(s"NuType symbol $name is not supported when resolving base classes")
        case N =>
          throw new CodeGenError(s"undeclared type name $name when resolving base classes")
      }
    }
    if (baseClasses.lengthIs > 1)
      throw CodeGenError(
        s"cannot have ${baseClasses.length} base classes: " +
        baseClasses.map { _.lexicalName }.mkString(", ")
      )
    else
      baseClasses.headOption
  }

  def resolveImplementedTraits(ty: Type): Ls[TraitSymbol] = {
    ty.collectTypeNames.flatMap { name =>
      this.getType(name) match {
        case S(sym: ClassSymbol) => N
        case S(sym: TraitSymbol) => S(sym)
        case S(sym: TypeAliasSymbol) =>
          throw new CodeGenError(s"cannot inherit from type alias $name" )
        case S(sym: NuTypeSymbol) =>
          throw new CodeGenError(s"NuType symbol $name is not supported when resolving implemented traits")
        case N =>
          throw new CodeGenError(s"undeclared type name $name when resolving implemented traits")
      }
    }
  }

  def declareTypeSymbol(typeDef: TypeDef): TypeSymbol = typeDef match {
    case TypeDef(Als, TypeName(name), tparams, body, _, _, _, _) =>
      declareTypeAlias(name, tparams map { _.name }, body)
    case TypeDef(Trt, TypeName(name), tparams, body, _, mthdDefs, _, _) =>
      declareTrait(name, tparams map { _.name }, body, mthdDefs)
    case TypeDef(Cls, TypeName(name), tparams, baseType, _, members, _, _) =>
      declareClass(name, tparams map { _.name }, baseType, members)
    case TypeDef(Mxn, _, _, _, _, _, _, _) =>
      throw CodeGenError("Mixins are not supported yet.")
    case TypeDef(Mod, _, _, _, _, _, _, _) =>
      throw CodeGenError("Modules are not supported yet.")
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

  // in DiffTests, we need to rename `TypingUnit` to some other names
  // because we would not indicate different names manually
  def declareTopModule(
    lexicalName: Str,
    stmts: Ls[Statement],
    nuTypes: Ls[NuTypeDef],
    allowRenaming: Bool
  ): ModuleSymbol = {
    val finalName =
      if (allowRenaming) allocateRuntimeName(lexicalName) else lexicalName
    val (ctor, mths) = stmts.partitionMap {
      case NuFunDef(isLetRec, Var(nme), _, tys, Left(rhs)) if (isLetRec.isEmpty || isLetRec.getOrElse(false)) =>
        Right(MethodDef[Left[Term, Type]](isLetRec.getOrElse(false), TypeName(finalName), Var(nme), tys, Left(rhs)))
      case s => Left(s)
    }
    val symbol = ModuleSymbol(finalName, Nil, Record(Nil), mths, ctor, Nil, nuTypes, false)
    register(symbol)
    symbol
  }

  def captureSymbol(
    outsiderSym: RuntimeSymbol,
    capturedSym: RuntimeSymbol
  ): Unit = {
    val symbol = CapturedSymbol(outsiderSym, capturedSym)
    lexicalValueSymbols.put(symbol.lexicalName, symbol); ()
  }

  // We don't want `outer` symbols to be shadowed by each other
  // Add all runtime names of `outer` symbols from the parent scope
  private def pullOuterSymbols(syms: scala.collection.mutable.HashSet[Str]) = {
    syms.foreach { s =>
      runtimeSymbols += s
      outerSymbols += s
    }

    this
  }

  def declareTrait(
      lexicalName: Str,
      params: Ls[Str],
      base: Type,
      methods: Ls[MethodDef[Left[Term, Type]]]
  ): TraitSymbol = {
    val runtimeName = allocateRuntimeName(lexicalName)
    val symbol = TraitSymbol(lexicalName, runtimeName, params, base, methods)
    register(symbol)
    symbol
  }

  def declareTypeAlias(lexicalName: Str, params: Ls[Str], ty: Type): TypeAliasSymbol = {
    val symbol = TypeAliasSymbol(lexicalName, params, ty)
    register(symbol)
    symbol
  }
  
  def declareThisAlias(): ValueSymbol = {
    val runtimeName = allocateRuntimeName("self")
    val symbol = ValueSymbol("this", runtimeName, Some(false), false)
    register(symbol)
    symbol
  }

  def declareValue(lexicalName: Str, isByvalueRec: Option[Boolean], isLam: Boolean, symbolicName: Opt[Str]): ValueSymbol = {
    val runtimeName = lexicalValueSymbols.get(lexicalName) match {
      // If we are implementing a stub symbol and the stub symbol did not shadow any other
      // symbols, it is safe to reuse its `runtimeName`.
      case S(sym: StubValueSymbol) if !sym.shadowing => sym.runtimeName
      case S(sym: BuiltinSymbol) if !sym.accessed    => sym.runtimeName
      case _                                         => allocateRuntimeName(lexicalName)
    }
    val symbol = ValueSymbol(lexicalName, runtimeName, isByvalueRec, isLam)
    register(symbol)
    symbolicName.foreach { symbolicName =>
      register(ValueSymbol(symbolicName, runtimeName, isByvalueRec, isLam))
    }
    symbol
  }

  def declareOuterSymbol(): ValueSymbol = {
    val lexicalName = "outer"
    val symbol = declareValue(lexicalName, Some(false), false, N)
    outerSymbols += symbol.runtimeName
    symbol
  }

  def declareStubValue(lexicalName: Str, symbolicName: Opt[Str])(implicit allowEscape: Bool): StubValueSymbol =
    declareStubValue(lexicalName, N, symbolicName)

  def declareStubValue(lexicalName: Str, previous: StubValueSymbol, symbolicName: Opt[Str])(implicit
      allowEscape: Bool
  ): StubValueSymbol =
    declareStubValue(lexicalName, S(previous), symbolicName)

  private def declareStubValue(lexicalName: Str, previous: Opt[StubValueSymbol], symbolicName: Opt[Str])(implicit
      allowEscape: Bool
  ): StubValueSymbol = {
    val symbol = lexicalValueSymbols.get(lexicalName) match {
      // If a stub with the same name has been defined, use the name.
      case S(value) => StubValueSymbol(lexicalName, value.runtimeName, true, previous)
      // Otherwise, we will allocate a new name.
      case N => StubValueSymbol(lexicalName, allocateRuntimeName(lexicalName), false, previous)
    }
    register(symbol)
    symbolicName.foreach { symbolicName =>
      register(StubValueSymbol(symbolicName, symbol.runtimeName, false, previous))
    }
    symbol
  }

  def stubize(sym: ValueSymbol, previous: StubValueSymbol)(implicit
      allowEscape: Bool
  ): StubValueSymbol = {
    unregister(sym)
    declareStubValue(sym.lexicalName, S(previous), N)
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

  /**
    * This function declares a parameter in current scope and returns the 
    * symbol's runtime name.
    *
    * @param name
    * @return
    */
  def declareParameter(name: Str): Str = {
    val prefix =
      if (JSField.isValidIdentifier(name)) name
      else if (Symbol.isKeyword(name)) name + "$"
      else Scope.replaceTicks(name)
    val runtimeName = allocateRuntimeName(prefix)
    register(ValueSymbol(name, runtimeName, Some(false), false))
    runtimeName
  }

  def existsRuntimeSymbol(name: Str): Bool = runtimeSymbols.contains(name)

  /**
    * Shorthands for deriving normal scopes.
    */
  def derive(name: Str): Scope =
    (new Scope(name, S(this))).pullOuterSymbols(outerSymbols)

  
  def refreshRes(): Unit = {
    lexicalValueSymbols("res") = ValueSymbol("res", "res", Some(false), false)
  }
}

object Scope {

  /**
  * Shorthands for creating top-level scopes.
  */
  def apply(name: Str): Scope = new Scope(name)

  private val nameAlphabet: Ls[Char] = Ls.from("abcdefghijklmnopqrstuvwxyz")

  private def replaceTicks(str: Str): Str = str.replace('\'', '$')
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
