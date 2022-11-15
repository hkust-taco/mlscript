package mlscript

import mlscript.utils._, shorthands._, algorithms._
import mlscript.codegen.Helpers._
import mlscript.codegen._
import scala.collection.mutable.ListBuffer
import mlscript.{JSField, JSLit}
import scala.collection.mutable.{Set => MutSet}

class JSBackend(allowUnresolvedSymbols: Boolean) {
  /**
    * The root scope of the program.
    */
  protected val topLevelScope = Scope("root")

  /**
    * The prelude code manager.
    */
  protected val polyfill = Polyfill()

  protected val visitedSymbols = MutSet[ValueSymbol]()

  /**
    * This function translates parameter destructions in `def` declarations.
    *
    * The production rules of MLscript `def` parameters are:
    *
    *     subterm ::= "(" term ")" | record | literal | identifier
    *     term ::= let | fun | ite | withsAsc | _match
    *
    * JavaScript supports following destruction patterns:
    *
    * - Array patterns: `[x, y, ...]` where `x`, `y` are patterns.
    * - Object patterns: `{x: y, z: w, ...}` where `z`, `w` are patterns.
    * - Identifiers: an identifier binds the position to a name.
    *
    * This function only translate name patterns and object patterns. I was thinking if we can
    * support literal parameter matching by merging multiple function `def`s into one.
    */
  private def translatePattern(t: Term)(implicit scope: Scope): JSPattern = t match {
    // fun x -> ... ==> function (x) { ... }
    // should returns ("x", ["x"])
    case Var(name) =>
      val runtimeName = scope.declareParameter(name)
      JSNamePattern(runtimeName)
    // fun { x, y } -> ... ==> function ({ x, y }) { ... }
    // should returns ("{ x, y }", ["x", "y"])
    case Rcd(fields) =>
      JSObjectPattern(fields map {
        case (Var(nme), Fld(_, _, Var(als))) =>
          val runtimeName = scope.declareParameter(als)
          val fieldName = JSField.emitValidFieldName(nme)
          if (runtimeName === fieldName) fieldName -> N
          else fieldName -> S(JSNamePattern(runtimeName))
        case (Var(nme), Fld(_, _, subTrm)) => 
          JSField.emitValidFieldName(nme) -> S(translatePattern(subTrm))
      })
    // This branch supports `def f (x: int) = x`.
    case Asc(trm, _) => translatePattern(trm)
    // Replace literals with wildcards.
    case _: Lit      => JSWildcardPattern()
    case Bra(_, trm) => translatePattern(trm)
    case Tup(fields) => JSArrayPattern(fields map { case (_, Fld(_, _, t)) => translatePattern(t) })
    // Others are not supported yet.
    case TyApp(base, _) =>
      translatePattern(base)
    case _: Lam | _: App | _: Sel | _: Let | _: Blk | _: Bind | _: Test | _: With | _: CaseOf | _: Subs | _: Assign
        | If(_, _) | New(_, _) | _: Splc =>
      throw CodeGenError(s"term ${inspect(t)} is not a valid pattern")
  }

  private def translateParams(t: Term)(implicit scope: Scope): Ls[JSPattern] = t match {
    case Tup(params) => params map { case _ -> Fld(_, _, p) => translatePattern(p) }
    case _           => throw CodeGenError(s"term $t is not a valid parameter list")
  }

  protected def translateVar(name: Str, isCallee: Bool)(implicit scope: Scope): JSExpr =
    scope.resolveValue(name) match {
      case S(sym: BuiltinSymbol) =>
        sym.accessed = true
        if (!polyfill.used(sym.feature))
          polyfill.use(sym.feature, sym.runtimeName)
        val ident = JSIdent(sym.runtimeName)
        if (sym.feature === "error") ident() else ident
      case S(sym: StubValueSymbol) =>
        if (sym.accessible)
          JSIdent(sym.runtimeName)
        else
          throw new UnimplementedError(sym)
      case S(sym: ValueSymbol) =>
        if (sym.isByvalueRec.getOrElse(false) && !sym.isLam) throw CodeGenError(s"unguarded recursive use of by-value binding $name")
        visitedSymbols += sym
        val ident = JSIdent(sym.runtimeName)
        if (sym.isByvalueRec.isEmpty && !sym.isLam) ident() else ident
      case S(sym: ClassSymbol) =>
        if (isCallee)
          JSNew(JSIdent(sym.runtimeName))
        else
          JSArrowFn(JSNamePattern("x") :: Nil, L(JSNew(JSIdent(sym.runtimeName))(JSIdent("x"))))
      case S(sym: TraitSymbol) =>
        JSIdent(sym.lexicalName)("build")
      case N => scope.getType(name) match {
        case S(sym: TypeAliasSymbol) =>
          throw CodeGenError(s"type alias ${name} is not a valid expression")
        case S(_) => throw new Exception("register mismatch in scope")
        case N =>
          if (allowUnresolvedSymbols)
            JSIdent(name)
          else
            throw CodeGenError(s"unresolved symbol ${name}")
      }
    }

  /**
    * Handle all possible cases of MLscript function applications. We extract
    * this method to prevent exhaustivity check from reaching recursion limit.
    */
  protected def translateApp(term: App)(implicit scope: Scope): JSExpr = term match {
    // Binary expressions
    case App(App(Var(op), Tup((N -> Fld(_, _, lhs)) :: Nil)), Tup((N -> Fld(_, _, rhs)) :: Nil))
        if JSBinary.operators contains op =>
      JSBinary(op, translateTerm(lhs), translateTerm(rhs))
    // If-expressions
    case App(App(App(Var("if"), tst), con), alt) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    // Function invocation
    case App(trm, Tup(args)) =>
      val callee = trm match {
        case Var(nme) => translateVar(nme, true)
        case _ => translateTerm(trm)
      }
      callee(args map { case (_, Fld(_, _, arg)) => translateTerm(arg) }: _*)
    case _ => throw CodeGenError(s"ill-formed application ${inspect(term)}")
  }

  /**
    * Translate MLscript terms into JavaScript expressions.
    */
  protected def translateTerm(term: Term)(implicit scope: Scope): JSExpr = term match {
    case Var(name) => translateVar(name, false)
    case Lam(params, body) =>
      val lamScope = scope.derive("Lam")
      val patterns = translateParams(params)(lamScope)
      JSArrowFn(patterns, lamScope.tempVars `with` translateTerm(body)(lamScope))
    case t: App => translateApp(t)
    case Rcd(fields) =>
      JSRecord(fields map { case (key, Fld(_, _, value)) =>
        key.name -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSField(translateTerm(receiver), fieldName.name)
    // Turn let into an IIFE.
    case Let(true, Var(name), Lam(args, body), expr) =>
      val letScope = scope.derive("Let")
      val runtimeName = letScope.declareParameter(name)
      val fn = {
        val fnScope = letScope.derive("Function")
        val params = translateParams(args)(fnScope)
        val fnBody = fnScope.tempVars.`with`(translateTerm(body)(fnScope))
        JSFuncExpr(S(runtimeName), params, fnBody.fold(_.`return` :: Nil, identity))
      }
      JSImmEvalFn(
        N,
        JSNamePattern(runtimeName) :: Nil,
        letScope.tempVars.`with`(translateTerm(expr)(letScope)),
        fn :: Nil
      )
    case Let(true, Var(name), _, _) =>
      throw new CodeGenError(s"recursive non-function definition $name is not supported")
    case Let(_, Var(name), value, body) =>
      val letScope = scope.derive("Let")
      val runtimeName = letScope.declareParameter(name)
      JSImmEvalFn(
        N,
        JSNamePattern(runtimeName) :: Nil,
        letScope.tempVars `with` translateTerm(body)(letScope),
        translateTerm(value) :: Nil
      )
    case Blk(stmts) =>
      val blkScope = scope.derive("Blk")
      val flattened = stmts.iterator.flatMap(_.desugared._2).toList
      JSImmEvalFn(
        N,
        Nil,
        R(blkScope.tempVars `with` (flattened.iterator.zipWithIndex.map {
          case (t: Term, index) if index + 1 == flattened.length => translateTerm(t)(blkScope).`return`
          case (t: Term, index)                                  => JSExprStmt(translateTerm(t)(blkScope))
          // TODO: find out if we need to support this.
          case (_: Def | _: TypeDef | _: NuFunDef /* | _: NuTypeDef */, _) =>
            throw CodeGenError("unsupported definitions in blocks")
        }.toList)),
        Nil
      )
    // Pattern match with only one branch -> comma expression
    case CaseOf(trm, Wildcard(default)) =>
      JSCommaExpr(translateTerm(trm) :: translateTerm(default) :: Nil)
    // Pattern match with two branches -> tenary operator
    case CaseOf(trm, Case(tst, csq, Wildcard(alt))) =>
      translateCase(translateTerm(trm), tst)(translateTerm(csq), translateTerm(alt))
    // Pattern match with more branches -> chain of ternary expressions with cache
    case CaseOf(trm, cases) =>
      val arg = translateTerm(trm)
      if (arg.isSimple) {
        translateCaseBranch(arg, cases)
      } else {
        val name = scope.declareRuntimeSymbol()
        scope.tempVars += name
        val ident = JSIdent(name)
        JSCommaExpr(JSAssignExpr(ident, arg) :: translateCaseBranch(ident, cases) :: Nil)
      }
    case IntLit(value) => JSLit(value.toString + (if (JSBackend isSafeInteger value) "" else "n"))
    case DecLit(value) => JSLit(value.toString)
    case StrLit(value) => JSExpr(value)
    case UnitLit(value) => JSLit(if (value) "undefined" else "null")
    // `Asc(x, ty)` <== `x: Type`
    case Asc(trm, _) => translateTerm(trm)
    // `c with { x = "hi"; y = 2 }`
    case With(trm, Rcd(fields)) =>
      JSInvoke(
        JSIdent(polyfill get "withConstruct" match {
          case S(fnName) => fnName
          case N         => polyfill.use("withConstruct", topLevelScope.declareRuntimeSymbol("withConstruct"))
        }),
        translateTerm(trm) :: JSRecord(fields map { case (Var(name), Fld(_, _, value)) =>
          name -> translateTerm(value)
        }) :: Nil
      )
    case Bra(_, trm) => translateTerm(trm)
    case Tup(terms) =>
      JSArray(terms map { case (_, Fld(_, _, term)) => translateTerm(term) })
    case Subs(arr, idx) =>
      JSMember(translateTerm(arr), translateTerm(idx))
    case Assign(lhs, value) =>
      lhs match {
        case _: Subs | _: Sel | _: Var =>
          JSCommaExpr(JSAssignExpr(translateTerm(lhs), translateTerm(value)) :: JSArray(Nil) :: Nil)
        case _ =>
          throw CodeGenError(s"illegal assignemnt left-hand side: ${inspect(lhs)}")
      }
    case iff: If =>
      iff.desugaredIf match {
        case N => throw CodeGenError(s"if expression has not been desugared")
        case S(term) => translateTerm(term)
      }
    case New(N, TypingUnit(Nil)) => JSRecord(Nil)
    case New(S(TypeName(className) -> Tup(args)), TypingUnit(Nil)) =>
      val callee = translateVar(className, true)
      callee(args.map { case (_, Fld(_, _, arg)) => translateTerm(arg) }: _*)
    case New(_, TypingUnit(_)) =>
      throw CodeGenError("custom class body is not supported yet")
    case _: Bind | _: Test | If(_, _) | TyApp(_, _) | _: Splc =>
      throw CodeGenError(s"cannot generate code for term ${inspect(term)}")
  }

  private def translateCaseBranch(scrut: JSExpr, branch: CaseBranches)(implicit
      scope: Scope
  ): JSExpr = branch match {
    case Case(pat, body, rest) =>
      translateCase(scrut, pat)(translateTerm(body), translateCaseBranch(scrut, rest))
    case Wildcard(body) => translateTerm(body)
    case NoCases        => JSImmEvalFn(N, Nil, R(JSInvoke(
      JSNew(JSIdent("Error")),
      JSExpr("non-exhaustive case expression") :: Nil
    ).`throw` :: Nil), Nil)
  }

  private def translateCase(scrut: JSExpr, pat: SimpleTerm) = {
    JSTenary(
      pat match {
        case Var("int") =>
          JSInvoke(JSField(JSIdent("Number"), "isInteger"), scrut :: Nil)
        case Var("bool") =>
          JSBinary("===", scrut.member("constructor"), JSLit("Boolean"))
        case Var(s @ ("true" | "false")) =>
          JSBinary("===", scrut, JSLit(s))
        case Var("string") =>
          // JS is dumb so `instanceof String` won't actually work on "primitive" strings...
          JSBinary("===", scrut.member("constructor"), JSLit("String"))
        case Var(name) => topLevelScope.getType(name) match {
          case S(ClassSymbol(_, runtimeName, _, _, _)) => JSInstanceOf(scrut, JSIdent(runtimeName))
          case S(TraitSymbol(_, runtimeName, _, _, _)) => JSIdent(runtimeName)("is")(scrut)
          case S(_: TypeAliasSymbol) => throw new CodeGenError(s"cannot match type alias $name")
          case N => throw new CodeGenError(s"unknown match case: $name")
        }
        case lit: Lit =>
          JSBinary("===", scrut, JSLit(lit.idStr))
      },
      _,
      _
    )
  }

  protected def translateTraitDeclaration(
      traitSymbol: TraitSymbol
  )(implicit scope: Scope): JSConstDecl = {
    import JSCodeHelpers._
    val instance = id("instance")
    val bases = traitSymbol.body.collectTypeNames.flatMap { name =>
      topLevelScope.getType(name) match {
        case S(t: TraitSymbol) => S(id(t.runtimeName)("implement")(instance).stmt)
        case S(_: ClassSymbol) | S(_: TypeSymbol) | N => N
      }
    }
    val members = traitSymbol.methods.map { method =>
      val name = method.nme.name
      val define = method.rhs.value match {
        // Define methods for functions.
        case Lam(params, body) =>
          val methodScope = scope.derive(s"Method $name")
          val methodParams = translateParams(params)(methodScope)
          methodScope.declareValue("this", Some(false), false)
          instance(name) := JSFuncExpr(
            N,
            methodParams,
            `return`(translateTerm(body)(methodScope)) :: Nil
          )
        // Define getters for pure expressions.
        case term =>
          val getterScope = scope.derive(s"Getter $name")
          getterScope.declareValue("this", Some(false), false)
          id("Object")("defineProperty")(
            instance,
            JSExpr(name),
            JSRecord(
              "get" -> JSFuncExpr(
                N,
                Nil,
                `return`(translateTerm(term)(getterScope)) :: Nil
              ) :: Nil
            )
          ).stmt
      }
      JSIfStmt(
        JSExpr(name).binary("in", instance).unary("!"),
        define :: Nil,
      )
    }
    val implement = JSFuncExpr(
      S("implement"),
      param("instance") :: Nil,
      JSIfStmt(
        id("tag").binary("in", instance),
        `return`() :: Nil,
      )
        :: id("Object")("defineProperty")(
          instance,
          id("tag"),
          JSRecord("value" -> JSRecord(Nil) :: Nil)
        ).stmt
        :: members
        ::: bases
    )
    // function build(instance) {
    //   if (typeof instance !== "object") {
    //     instance = Object.assign(instance, {});
    //   }
    //   this.implement(instance);
    //   return instance;
    // }
    val build = JSFuncExpr(
      S("build"),
      param("instance") :: Nil,
      JSIfStmt(
        instance.typeof().binary("!==", JSExpr("object")),
        (instance := id("Object")("assign")(instance, JSRecord(Nil))) :: Nil
      ) 
        :: id("this")("implement")(instance).stmt
        :: `return`(instance)
        :: Nil
    )
    val is = JSFuncExpr(
      S("is"),
      param("x") :: Nil,
      `return`(
        id("x").typeof()
          .binary("===", JSExpr("object"))
          .binary("&&", id("x").binary("!==", JSLit("null")))
          .binary("&&", id("tag").binary("in", id("x")))
      ) :: Nil
    )
    const(
      traitSymbol.runtimeName,
      JSFuncExpr(
        N,
        Nil,
        Ls(
          const("tag", id("Symbol")()),
          `return` {
            JSRecord("implement" -> implement :: "build" -> build :: "is" -> is :: Nil)
          }
        )
      )()
    )
  }
  /**
    * Translate MLscript class declaration to JavaScript class declaration.
    * First, we will analyze its fields and base class name.
    * Then, we will check if the base class exists.
    */
  protected def translateClassDeclaration(
      classSymbol: ClassSymbol,
      baseClassSymbol: Opt[ClassSymbol]
  )(implicit scope: Scope): JSClassDecl = {
    // Translate class methods and getters.
    val classScope = scope.derive(s"class ${classSymbol.lexicalName}")
    val members = classSymbol.methods.map {
      translateClassMember(_)(classScope)
    }
    // Collect class fields.
    val fields = classSymbol.body.collectFields ++
      classSymbol.body.collectTypeNames.flatMap(resolveTraitFields)
    val base = baseClassSymbol.map { sym => JSIdent(sym.runtimeName) }
    val traits = classSymbol.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }
    JSClassDecl(classSymbol.runtimeName, fields, base, members, traits)
  }

  /**
   * Translate class methods and getters.
   */
  private def translateClassMember(
      method: MethodDef[Left[Term, Type]],
  )(implicit scope: Scope): JSClassMemberDecl = {
    val name = method.nme.name
    // Create the method/getter scope.
    val memberScope = method.rhs.value match {
      case _: Lam => scope.derive(s"method $name")
      case _ => scope.derive(s"getter $name")
    }
    // Declare the alias for `this` before declaring parameters.
    val selfSymbol = memberScope.declareThisAlias()
    // Declare parameters.
    val (memberParams, body) = method.rhs.value match {
      case Lam(params, body) =>
        val methodParams = translateParams(params)(memberScope)
        (S(methodParams), body)
      case term =>
        (N, term)
    }
    // Translate class member body.
    val bodyResult = translateTerm(body)(memberScope).`return`
    // If `this` is accessed, add `const self = this`.
    val bodyStmts = if (visitedSymbols(selfSymbol)) {
      val thisDecl = JSConstDecl(selfSymbol.runtimeName, JSIdent("this"))
      visitedSymbols -= selfSymbol
      R(thisDecl :: bodyResult :: Nil)
    } else {
      R(bodyResult :: Nil)
    }
    // Returns members depending on what it is.
    memberParams match {
      case S(memberParams) => JSClassMethod(name, memberParams, bodyStmts)
      case N => JSClassGetter(name, bodyStmts)
    }
  }

  /**
    * Declare symbols for types, traits and classes.
    * Call this before the code generation.
    * 
    * @return defined class symbols
    */
  protected def declareTypeDefs(typeDefs: Ls[TypeDef]): (Ls[TraitSymbol], Ls[ClassSymbol]) = {
    val traits = new ListBuffer[TraitSymbol]()
    val classes = new ListBuffer[ClassSymbol]()
    typeDefs.foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _, _) =>
        topLevelScope.declareTypeAlias(name, tparams map { _.name }, body)
      case TypeDef(Trt, TypeName(name), tparams, body, _, methods, _) =>
        traits += topLevelScope.declareTrait(name, tparams map { _.name }, body, methods)
      case TypeDef(Cls, TypeName(name), tparams, baseType, _, members, _) =>
        classes += topLevelScope.declareClass(name, tparams map { _.name }, baseType, members)
      case TypeDef(Nms, _, _, _, _, _, _) => throw CodeGenError("Namespaces are not supported yet.")
    }
    (traits.toList, classes.toList)
  }

  /**
    * Recursively collect fields from trait definitions.
    * Caveat: this might cause stack overflow if cyclic inheritance exists.
    */
  private def resolveTraitFields(name: Str): Ls[Str] =
    topLevelScope.getType(name) match {
      case S(sym: TraitSymbol) => sym.body.collectFields ++ resolveTraitFields(sym)
      case S(_: TypeSymbol) | S(_: ClassSymbol) | N => Nil
    }

  /**
    * Recursively collect fields from trait definitions.
    * Caveat: this might cause stack overflow if cyclic inheritance exists.
    */
  private def resolveTraitFields(sym: TraitSymbol): Ls[Str] =
    sym.body.collectTypeNames.flatMap(resolveTraitFields)

  /**
    * Find the base class for a specific class.
    */
  private def resolveBaseClass(ty: Type): Opt[ClassSymbol] = {
    val baseClasses = ty.collectTypeNames.flatMap { name =>
      topLevelScope.getType(name) match {
        case S(sym: ClassSymbol) => S(sym)
        case S(sym: TraitSymbol) => N // TODO: inherit from traits
        case S(sym: TypeAliasSymbol) =>
          throw new CodeGenError(s"cannot inherit from type alias $name" )
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

  /**
    * Resolve inheritance of all declared classes.
    * 
    * @return sorted class symbols with their base classes
    */
  protected def sortClassSymbols(classSymbols: Ls[ClassSymbol]): Iterable[(ClassSymbol, Opt[ClassSymbol])] = {
    // Cache base classes for class symbols.
    val baseClasses = Map.from(classSymbols.iterator.flatMap { derivedClass =>
      topLevelScope.resolveBaseClass(derivedClass.body).map(derivedClass -> _)
    })
    val sorted = try topologicalSort(baseClasses, classSymbols) catch {
      case e: CyclicGraphError => throw CodeGenError("cyclic inheritance detected")
    }
    // Their base classes might be class symbols defined in previous translation
    // units. So we filter them out here.
    sorted.flatMap(sym => if (classSymbols.contains(sym)) S(sym -> baseClasses.get(sym)) else N)
  }
  
}

class JSWebBackend extends JSBackend(allowUnresolvedSymbols = true) {
  // Name of the array that contains execution results
  val resultsName: Str = topLevelScope declareRuntimeSymbol "results"

  val prettyPrinterName: Str = topLevelScope declareRuntimeSymbol "prettyPrint"

  polyfill.use("prettyPrint", prettyPrinterName)

  def apply(pgrm: Pgrm): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    val (traitSymbols, classSymbols) = declareTypeDefs(typeDefs)
    val defStmts = 
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      sortClassSymbols(classSymbols).map { case (derived, base) =>
        translateClassDeclaration(derived, base)(topLevelScope)
      }.toList

    val resultsIdent = JSIdent(resultsName)
    val stmts: Ls[JSStmt] =
      JSConstDecl(resultsName, JSArray(Nil)) ::
        defStmts
        // Generate something like:
        // ```js
        // const <name> = <expr>;
        // <results>.push(<name>);
        // ```
        .concat(otherStmts.flatMap {
          case Def(recursive, Var(name), L(body), isByname) =>
            val (originalExpr, sym) = if (recursive) {
              val isByvalueRecIn = if (isByname) None else Some(true)
              val sym = topLevelScope.declareValue(name, isByvalueRecIn, body.isInstanceOf[Lam])
              val translated = translateTerm(body)(topLevelScope)
              topLevelScope.unregisterSymbol(sym)
              val isByvalueRecOut = if (isByname) None else Some(false)
              (translated, topLevelScope.declareValue(name, isByvalueRecOut, body.isInstanceOf[Lam]))
            } else {
              val translatedBody = translateTerm(body)(topLevelScope)
              val isByvalueRec = if (isByname) None else Some(false)
              (translatedBody, topLevelScope.declareValue(name, isByvalueRec, body.isInstanceOf[Lam]))
            }
            val translatedBody = if (sym.isByvalueRec.isEmpty && !sym.isLam) JSArrowFn(Nil, L(originalExpr)) else originalExpr
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(resultsIdent("push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          // Ignore type declarations.
          case Def(_, _, R(_), isByname) => Nil
          // `exprs.push(<expr>)`.
          case term: Term =>
            topLevelScope.tempVars `with` JSInvoke(
              resultsIdent("push"),
              translateTerm(term)(topLevelScope) :: Nil
            ).stmt :: Nil
        })
    val epilogue = resultsIdent.member("map")(JSIdent(prettyPrinterName)).`return` :: Nil
    JSImmEvalFn(N, Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines
  }
}

class JSTestBackend extends JSBackend(allowUnresolvedSymbols = false) {
  private val lastResultSymbol = topLevelScope.declareValue("res", Some(false), false)
  private val resultIdent = JSIdent(lastResultSymbol.runtimeName)

  private var numRun = 0

  /**
    * Generate a piece of code for test purpose. It can be invoked repeatedly.
    */
  def apply(pgrm: Pgrm, allowEscape: Bool): JSTestBackend.Result =
    try generate(pgrm)(topLevelScope, allowEscape) catch {
      case e: CodeGenError => JSTestBackend.IllFormedCode(e.getMessage())
      case e: UnimplementedError => JSTestBackend.Unimplemented(e.getMessage())
      case e: Throwable => JSTestBackend.UnexpectedCrash(e.getClass().getName, e.getMessage())
    }

  /**
    * Generate JavaScript code which targets MLscript test from the given block.
    *
    * @param pgrm the program to translate
    * @param scope the top-level scope
    * @param allowEscape whether to try executing code even if it refers to unimplemented definitions
    * @return
    */
  private def generate(pgrm: Pgrm)(implicit scope: Scope, allowEscape: Bool): JSTestBackend.TestCode = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    val (traitSymbols, classSymbols) = declareTypeDefs(typeDefs)
    val defStmts = 
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      sortClassSymbols(classSymbols).map { case (derived, base) =>
        translateClassDeclaration(derived, base)(topLevelScope)
      }.toList

    val zeroWidthSpace = JSLit("\"\\u200B\"")
    val catchClause = JSCatchClause(
      JSIdent("e"),
      (zeroWidthSpace + JSIdent("e") + zeroWidthSpace).log() :: Nil
    )

    // Generate statements.
    val queries = otherStmts.map {
      case Def(recursive, Var(name), L(body), isByname) =>
        val bodyIsLam = body match { case _: Lam => true case _ => false }
        (if (recursive) {
          val isByvalueRecIn = if (isByname) None else Some(true)
          val sym = scope.declareValue(name, isByvalueRecIn, bodyIsLam)
          try {
            val translated = translateTerm(body)
            scope.unregisterSymbol(sym)
            val isByvalueRecOut = if (isByname) None else Some(false)
            R((translated, scope.declareValue(name, isByvalueRecOut, bodyIsLam)))
          } catch {
            case e: UnimplementedError =>
              scope.stubize(sym, e.symbol)
              L(e.getMessage())
            case e: Throwable =>
              scope.unregisterSymbol(sym)
              val isByvalueRecOut = if (isByname) None else Some(false)
              scope.declareValue(name, isByvalueRecOut, bodyIsLam)
              throw e
          }
        } else {
          (try R(translateTerm(body)) catch {
            case e: UnimplementedError =>
              scope.declareStubValue(name, e.symbol)
              L(e.getMessage())
            case e: Throwable => throw e
          }) map {
            val isByvalueRec = if (isByname) None else Some(false)
            expr => (expr, scope.declareValue(name, isByvalueRec, bodyIsLam))
          }
        }) match {
          case R((originalExpr, sym)) =>
            val expr = 
              if (sym.isByvalueRec.isEmpty && !sym.isLam)
                JSArrowFn(Nil, L(originalExpr))
              else
                originalExpr
            JSTestBackend.CodeQuery(
              scope.tempVars.emit(),
              ((JSIdent("globalThis").member(sym.runtimeName) := (expr match {
                case t: JSArrowFn => t.toFuncExpr(S(sym.runtimeName))
                case t            => t
              })) :: Nil),
              sym.runtimeName
            )
          case L(reason) => JSTestBackend.AbortedQuery(reason)
        }
      case Def(_, Var(name), _, _) =>
        scope.declareStubValue(name)
        JSTestBackend.EmptyQuery
      case term: Term =>
        try {
          val body = translateTerm(term)(scope)
          val res = JSTestBackend.CodeQuery(scope.tempVars.emit(), (resultIdent := body) :: Nil)
          scope.refreshRes()
          res
        } catch {
          case e: UnimplementedError => JSTestBackend.AbortedQuery(e.getMessage())
          case e: Throwable          => throw e
        }
    }

    // If this is the first time, insert the declaration of `res`.
    var prelude: Ls[JSStmt] = defStmts
    if (numRun === 0)
      prelude = JSLetDecl(lastResultSymbol.runtimeName -> N :: Nil) :: prelude

    // Increase the run number.
    numRun = numRun + 1

    JSTestBackend.TestCode(SourceCode.fromStmts(polyfill.emit() ::: prelude).toLines, queries)
  }
}

object JSTestBackend {
  sealed abstract class Query

  /**
    * The generation was aborted due to some reason.
    */
  final case class AbortedQuery(reason: Str) extends Query

  /**
    * The entry generates nothing.
    */
  final object EmptyQuery extends Query

  /**
    * The entry generates meaningful code.
    */
  final case class CodeQuery(prelude: Ls[Str], code: Ls[Str], res: Str) extends Query {
    
  }

  object CodeQuery {
    def apply(decls: Opt[JSLetDecl], stmts: Ls[JSStmt], res: Str = "res"): CodeQuery =
      CodeQuery(
        decls match {
          case S(stmt) => stmt.toSourceCode.toLines
          case N       => Nil
        },
        SourceCode.fromStmts(stmts).toLines,
        res
      )
  }

  /**
    * Represents the result of code generation.
    */
  abstract class Result {
    def showFirstResult(prefixLength: Int): Unit = ()
  }

  /**
    * Emitted code.
    */
  final case class TestCode(prelude: Ls[Str], queries: Ls[Query]) extends Result

  sealed abstract class ErrorMessage(val content: Str) extends Result

  /**
    * The input MLscript is ill-formed (e.g. impossible inheritance).
    */
  final case class IllFormedCode(override val content: Str) extends ErrorMessage(content)

  /**
    * Some referenced symbols are not implemented.
    */
  final case class Unimplemented(override val content: Str) extends ErrorMessage(content)

  /**
    * Code generation crashed.
    */
  final case class UnexpectedCrash(val name: Str, override val content: Str) extends ErrorMessage(content)

  /**
    * The result is not executed for some reasons. E.g. `:NoJS` flag.
    */
  final object ResultNotExecuted extends JSTestBackend.Result
}

object JSBackend {
  // For integers larger than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER
  val MaximalSafeInteger: BigInt = BigInt("9007199254740991")

  // For integers less than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER
  val MinimalSafeInteger: BigInt = BigInt("-9007199254740991")

  def isSafeInteger(value: BigInt): Boolean =
    MinimalSafeInteger <= value && value <= MaximalSafeInteger
}
