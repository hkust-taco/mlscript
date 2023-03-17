package mlscript

import mlscript.utils._, shorthands._, algorithms._
import mlscript.codegen.Helpers._
import mlscript.codegen._
import scala.collection.mutable.{ListBuffer, HashMap}
import mlscript.{JSField, JSLit}
import scala.collection.mutable.{Set => MutSet}
import scala.util.control.NonFatal

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
    case Inst(bod) => translatePattern(bod)
    case _: Lam | _: App | _: Sel | _: Let | _: Blk | _: Bind | _: Test | _: With | _: CaseOf | _: Subs | _: Assign
        | If(_, _) | New(_, _) | _: Splc | _: Forall | _: Where =>
      throw CodeGenError(s"term ${inspect(t)} is not a valid pattern")
  }

  private def translateParams(t: Term)(implicit scope: Scope): Ls[JSPattern] = t match {
    case Tup(params) => params map {
      case N -> Fld(_, _, p) => translatePattern(p)
      case S(nme) -> Fld(_, _, p) => translatePattern(nme)
    }
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
      case S(sym: MixinSymbol) =>
        JSIdent(sym.runtimeName)
      case S(sym: ModuleSymbol) =>
        JSIdent(sym.runtimeName)
      case S(sym: NewClassSymbol) =>
        JSIdent(sym.runtimeName)
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
    case App(App(App(Var("if"), Tup((_, Fld(_, _, tst)) :: Nil)), Tup((_, Fld(_, _, con)) :: Nil)), Tup((_, Fld(_, _, alt)) :: Nil)) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    case App(App(App(Var("if"), tst), con), alt) => die
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
    case _ if term.desugaredTerm.isDefined => translateTerm(term.desugaredTerm.getOrElse(die))
    case Var(name) => translateVar(name, false)
    case Super() => JSIdent("super")
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
          case (NuFunDef(isLetRec, Var(nme), _, L(rhs)), _) => {
            val pat = blkScope.declareValue(nme, isLetRec, isLetRec.isEmpty)
            JSLetDecl(Ls(pat.runtimeName -> S(translateTerm(rhs)(blkScope))))
          }
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
    case Inst(bod) => translateTerm(bod)
    case iff: If =>
      throw CodeGenError(s"if expression was not desugared")
    case New(N, TypingUnit(Nil)) => JSRecord(Nil)
    case New(S(TypeName(className) -> Tup(args)), TypingUnit(Nil)) =>
      val callee = translateVar(className, true)
      callee(args.map { case (_, Fld(_, _, arg)) => translateTerm(arg) }: _*)
    case New(_, TypingUnit(_)) =>
      throw CodeGenError("custom class body is not supported yet")
    case Forall(_, bod) => translateTerm(bod)
    case TyApp(base, _) => translateTerm(base)
    case _: Bind | _: Test | If(_, _)  | _: Splc | _: Where =>
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
          case S(NewClassSymbol(_, runtimeName, _, _, _)) => JSInstanceOf(scrut, JSMember(JSIdent(runtimeName), JSIdent(JSLit.makeStringLiteral("class"))))
          case S(ModuleSymbol(_, runtimeName, _, _, _)) => JSInstanceOf(scrut, JSMember(JSIdent(runtimeName), JSIdent(JSLit.makeStringLiteral("class"))))
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

  protected def translateMixinDeclaration(
      mixinSymbol: MixinSymbol,
      typingUnit: Boolean = true
  )(implicit scope: Scope): JSStmt = {
    val getterScope = scope.derive(s"getter ${mixinSymbol.lexicalName}")
    val mixinScope = getterScope.derive(s"mixin ${mixinSymbol.lexicalName}")
    // Collect class fields.
    val fields = mixinSymbol.body.collectFields ++
      mixinSymbol.body.collectTypeNames.flatMap(resolveTraitFields)

    val members = mixinSymbol.methods.map {
      translateNewClassMember(_, fields)(mixinScope)
    } 
    val constructorScope = mixinScope.derive(s"${mixinSymbol.lexicalName} constructor")
    fields.foreach(constructorScope.declareValue(_, Some(false), false))
    val rest = constructorScope.declareValue("rest", Some(false), false)
    val base = getterScope.declareValue("base", Some(false), false)

    val traits = mixinSymbol.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }
    
    val classBody = JSClassNewDecl(mixinSymbol.runtimeName, fields, S(JSIdent(base.runtimeName)),
      Ls(JSIdent(s"...${rest.runtimeName}")), S(rest.runtimeName), members, traits)
    if (typingUnit)
      JSClassMethod(mixinSymbol.lexicalName, Ls(JSNamePattern(base.runtimeName)), R(Ls(
        JSReturnStmt(S(JSClassExpr(classBody)))
      )))
    else
      JSFuncDecl(mixinSymbol.lexicalName, Ls(JSNamePattern(base.runtimeName)),
        Ls(JSReturnStmt(S(JSClassExpr(classBody)))))
  }

  private def translateParents(superFields: Ls[Term], constructorScope: Scope)(implicit scope: Scope): Opt[JSExpr] = {
    val bases = superFields.map { sym => sym match {
      case App(lhs, _) => S(translateTerm(App(lhs, Tup(Ls())))(constructorScope))
      case _ => S(translateTerm(sym)(constructorScope))
    } }

    bases match {
      case head :: tail => tail.foldLeft(
        head match {
          case Some(JSIdent(nme)) => scope.resolveValue(nme) match {
            case Some(sym: MixinSymbol) => Some(JSInvoke(JSIdent(nme), Ls(JSIdent("Object"))))
            case Some(_) => Some(JSMember(JSIdent(nme), JSLit(JSLit.makeStringLiteral("class"))))
            case _ => throw CodeGenError(s"unresolved symbol in parents: $nme")
          }
          case Some(JSInvoke(JSIdent(nme), _)) => scope.resolveValue(nme) match {
            case Some(sym: MixinSymbol) => Some(JSInvoke(JSIdent(nme), Ls(JSIdent("Object"))))
            case Some(_) => Some(JSMember(JSIdent(nme), JSLit(JSLit.makeStringLiteral("class"))))
            case _ => throw CodeGenError(s"unresolved symbol in parents: $nme")
          }
          case _ => throw CodeGenError("unresolved parents.")
        }
      )((res, next) => (res, next) match {
        case (S(res), S(JSIdent(next))) => scope.resolveValue(next) match {
          case Some(sym: MixinSymbol) => S(JSInvoke(JSIdent(next), Ls(res)))
          case Some(_) => throw CodeGenError("can not have more than one parents.")
          case _ => throw CodeGenError(s"unresolved symbol in parents: $res")
        }
        case (S(res), S(JSInvoke(JSIdent(next), _))) => scope.resolveValue(next) match {
          case Some(sym: MixinSymbol) => S(JSInvoke(JSIdent(next), Ls(res)))
          case Some(_) => throw CodeGenError("can not have more than one parents.")
          case _ => throw CodeGenError(s"unresolved symbol in parents: $res")
        }
        case _ => throw CodeGenError("unresolved parents.")
      })
      case Nil => N
    }
  }

  protected def translateModuleDeclaration(
      moduleSymbol: ModuleSymbol,
      superFields: Ls[Term] = Nil,
      typingUnit: Boolean = true
  )(implicit scope: Scope): JSStmt = {
    val getterScope = scope.derive(s"getter ${moduleSymbol.lexicalName}")
    val moduleScope = scope.derive(s"module ${moduleSymbol.lexicalName}")
    val constructorScope = moduleScope.derive(s"${moduleSymbol.lexicalName} constructor")
    // Collect class fields.
    val fields = moduleSymbol.body.collectFields ++
      moduleSymbol.body.collectTypeNames.flatMap(resolveTraitFields)
    val members = moduleSymbol.methods.map {
      translateNewClassMember(_, fields)(moduleScope)
    }
    val traits = moduleSymbol.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }
    val rest = constructorScope.declareValue("rest", Some(false), false)
    val base: Opt[JSExpr] =
      translateParents(superFields, constructorScope)
    val superParameters = (superFields map {
      case App(lhs, Tup(rhs)) => rhs map {
        case (_, Fld(mut, spec, trm)) => translateTerm(trm)(getterScope)
      }
      case _ => Nil
    }).flatten
    val decl = JSClassNewDecl(moduleSymbol.runtimeName,
                   fields,
                   base,
                   superParameters.reverse,
                   N,
                   members,
                   traits)

    if (typingUnit)
      JSClassGetter(moduleSymbol.runtimeName, R(Ls(
        JSIfStmt(JSBinary("===", JSField(JSField(JSIdent("this"), "cache"), moduleSymbol.runtimeName), JSIdent("undefined")), Ls(
          decl,
          JSExprStmt(JSAssignExpr(JSField(JSField(JSIdent("this"), "cache"), moduleSymbol.runtimeName),
            JSNew(JSInvoke(JSIdent(moduleSymbol.runtimeName), Nil)))),
          JSExprStmt(JSAssignExpr(JSMember(JSField(JSField(JSIdent("this"), "cache"), moduleSymbol.runtimeName), JSLit(JSLit.makeStringLiteral("class"))), JSIdent(moduleSymbol.runtimeName))),
        )),
        JSReturnStmt(S(JSField(JSField(JSIdent("this"), "cache"), moduleSymbol.runtimeName)))
      )))
    else
      JSExprStmt(
        JSImmEvalFn(N, Nil, R(
          Ls(
            JSIfStmt(JSBinary("===", JSField(JSIdent("globalThis"), moduleSymbol.runtimeName), JSIdent("undefined")), Ls(
              decl,
              JSExprStmt(JSAssignExpr(JSField(JSIdent("globalThis"), moduleSymbol.runtimeName),
                JSNew(JSInvoke(JSIdent(moduleSymbol.runtimeName), Nil)))),
              JSExprStmt(JSAssignExpr(JSMember(JSField(JSIdent("globalThis"), moduleSymbol.runtimeName), JSLit(JSLit.makeStringLiteral("class"))), JSIdent(moduleSymbol.runtimeName))),
            )),
            JSReturnStmt(S(JSField(JSIdent("globalThis"), moduleSymbol.runtimeName)))
          )
        ), Nil)
      )
  }

  protected def translateNewClassDeclaration(
      classSymbol: NewClassSymbol,
      superFields: Ls[Term] = Nil,
      rest: Opt[Str] = N,
      typingUnit: Boolean = true
  )(implicit scope: Scope): JSStmt = {
    val getterScope = scope.derive(s"${classSymbol.lexicalName} getter")
    val classBody = translateNewClassExpression(classSymbol, superFields, rest)(getterScope)
    val constructor = classBody match {
      case JSClassNewDecl(_, fields, _, _, _, _, _) => fields.map(JSNamePattern(_))
    }
    val params = classBody match {
      case JSClassNewDecl(_, fields, _, _, _, _, _) => fields.map(JSIdent(_))
    }

    if (typingUnit)
      JSClassGetter(classSymbol.runtimeName, R(Ls(
        JSIfStmt(JSBinary("===", JSField(JSField(JSIdent("this"), "cache"), classSymbol.runtimeName), JSIdent("undefined")), Ls(
          JSExprStmt(JSClassExpr(classBody)),
          JSExprStmt(JSAssignExpr(JSField(JSField(JSIdent("this"), "cache"), classSymbol.runtimeName),
            JSArrowFn(constructor, L(JSInvoke(JSNew(JSIdent(classSymbol.runtimeName)), params))))),
          JSExprStmt(JSAssignExpr(JSMember(JSField(JSField(JSIdent("this"), "cache"), classSymbol.runtimeName), JSLit(JSLit.makeStringLiteral("class"))), JSIdent(classSymbol.runtimeName)))
        )),
        JSReturnStmt(S(JSField(JSField(JSIdent("this"), "cache"), classSymbol.runtimeName)))
      )))
    else
      JSExprStmt(
        JSImmEvalFn(N, Nil, R(
          Ls(
            JSIfStmt(JSBinary("===", JSField(JSIdent("globalThis"), classSymbol.runtimeName), JSIdent("undefined")), Ls(
              JSExprStmt(JSClassExpr(classBody)),
              JSExprStmt(JSAssignExpr(JSField(JSIdent("globalThis"), classSymbol.runtimeName),
                JSArrowFn(constructor, L(JSInvoke(JSNew(JSIdent(classSymbol.runtimeName)), params))))),
              JSExprStmt(JSAssignExpr(JSMember(JSField(JSIdent("globalThis"), classSymbol.runtimeName), JSLit(JSLit.makeStringLiteral("class"))), JSIdent(classSymbol.runtimeName)))
            )),
            JSReturnStmt(S(JSField(JSIdent("globalThis"), classSymbol.runtimeName)))
          )
        ), Nil)
      )
  }

  protected def translateNewClassExpression(
      classSymbol: NewClassSymbol,
      superFields: Ls[Term] = Nil,
      rest: Opt[Str] = N
  )(implicit scope: Scope): JSClassNewDecl = {
    // Translate class methods and getters.
    val classScope = scope.derive(s"class ${classSymbol.lexicalName}")
    // Collect class fields.
    val fields = classSymbol.body.collectFields ++
      classSymbol.body.collectTypeNames.flatMap(resolveTraitFields)
    val members = classSymbol.methods.map {
      translateNewClassMember(_, fields)(classScope)
    }

    val constructorScope = classScope.derive(s"${classSymbol.lexicalName} constructor")
    fields.foreach(constructorScope.declareValue(_, Some(false), false))
    val restRuntime = rest.flatMap(name => S(constructorScope.declareValue(name, Some(false), false).runtimeName))
    val base: Opt[JSExpr] =
      translateParents(superFields, constructorScope)
    val traits = classSymbol.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }

    val superParameters = (superFields map {
      case App(lhs, Tup(rhs)) => rhs map {
        case (_, Fld(mut, spec, trm)) => translateTerm(trm)(constructorScope)
      }
      case _ => Nil
    }).flatten

    JSClassNewDecl(classSymbol.runtimeName, fields, base, restRuntime match {
      case Some(restRuntime) => superParameters.reverse :+ JSIdent(s"...$restRuntime")
      case _ => superParameters.reverse
    }, restRuntime, members, traits)
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

  private def translateNewClassMember(
      method: MethodDef[Left[Term, Type]],
      props: Ls[Str] = Nil
  )(implicit scope: Scope): JSClassMemberDecl = {
    val name = method.nme.name
    // Create the method/getter scope.
    val memberScope = method.rhs.value match {
      case _: Lam => scope.derive(s"method $name")
      case _ => scope.derive(s"getter $name")
    }
    // Declare the alias for `this` before declaring parameters.
    val selfSymbol = memberScope.declareThisAlias()
    val preDecs = props.map(p => {
      val runtime = memberScope.declareValue(p, Some(false), false)
      JSConstDecl(runtime.runtimeName, JSIdent(s"this.#$p"))
    })
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
      R(preDecs ::: (thisDecl :: bodyResult :: Nil))
    } else {
      R(preDecs ::: (bodyResult :: Nil))
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

  protected def declareNewTypeDefs(typeDefs: Ls[NuTypeDef]):
    (Ls[TraitSymbol], Ls[NewClassSymbol], Ls[MixinSymbol], Ls[ModuleSymbol], HashMap[String, Ls[Term]]) = {
    val traits = new ListBuffer[TraitSymbol]()
    val classes = new ListBuffer[NewClassSymbol]()
    val mixins = new ListBuffer[MixinSymbol]()
    val modules = new ListBuffer[ModuleSymbol]()
    val superParameters = HashMap[String, Ls[Term]]()
    def tt(trm: Term): Type = trm.toType match {
      case L(ds) => Top
      case R(ty) => ty
    }

    def prepare(nme: Str, fs: Ls[Opt[Var] -> Fld], pars: Ls[Term], unit: TypingUnit) = {
      val params = fs.map {
        case (S(nme), Fld(mut, spec, trm)) =>
          val ty = tt(trm)
          nme -> Field(if (mut) S(ty) else N, ty)
        case (N, Fld(mut, spec, nme: Var)) => nme -> Field(if (mut) S(Bot) else N, Top)
        case _ => die
      }
      val body = pars.map(tt).foldRight(Record(params): Type)(Inter)
      val members = unit.children.foldLeft(List[MethodDef[Left[Term, Type]]]())((lst, loc) => loc match {
        case NuFunDef(isLetRec, mnme, tys, Left(rhs)) => lst :+ MethodDef(isLetRec.getOrElse(false), TypeName(nme), mnme, tys, Left(rhs))
        case _ => lst
      })
      
      (body, members)
    }

    typeDefs.foreach {
      case NuTypeDef(Mxn, TypeName(mxName), tps, tup @ Tup(fs), sig, pars, sup, ths, unit) => {
        val (body, members) = prepare(mxName, fs, pars, unit)
        val sym = topLevelScope.declareMixin(mxName, tps map { _._2.name }, body, members)
        mixins += sym
        superParameters.put(sym.runtimeName, pars)
      }
      case NuTypeDef(Nms, TypeName(nme), tps, tup @ Tup(fs), sig, pars, sup, ths, unit) => {
        val (body, members) = prepare(nme, fs, pars, unit)
        val sym = topLevelScope.declareModule(nme, tps map { _._2.name }, body, members)
        modules += sym
        superParameters.put(sym.runtimeName, pars)
      }
      case NuTypeDef(Als, TypeName(nme), tps, _, sig, pars, _, _, _) => {
        topLevelScope.declareTypeAlias(nme, tps map { _._2.name }, sig.getOrElse(Top))
      }
      case NuTypeDef(Cls, TypeName(nme), tps, tup @ Tup(fs), sig, pars, sup, ths, unit) => {
        val (body, members) = prepare(nme, fs, pars, unit)
        val sym = topLevelScope.declareNewClass(nme, tps map { _._2.name }, body, members)
        classes += sym
        superParameters.put(sym.runtimeName, pars)
      }
      case NuTypeDef(k @ Trt, TypeName(nme), tps, tup @ Tup(fs), sig, pars, sup, ths, unit) => {
        val (body, members) = prepare(nme, fs, pars, unit)
        val sym = topLevelScope.declareTrait(nme, tps map { _._2.name }, body, members)
        traits += sym
        superParameters.put(sym.runtimeName, pars)
      }
    }
    (traits.toList, classes.toList, mixins.toList, modules.toList, superParameters)
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

class JSCompilerBackend extends JSBackend(allowUnresolvedSymbols = true) {
  private def generateNewDef(pgrm: Pgrm, exported: Bool): Ls[Str] = {
    val mlsModule = topLevelScope.declareValue("typing_unit", Some(false), false)
    val (diags, (typeDefs, otherStmts)) = pgrm.newDesugared

    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols, superParameters) = declareNewTypeDefs(typeDefs)

    val defs =
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      mixinSymbols.map { translateMixinDeclaration(_, false)(topLevelScope) } ++
      moduleSymbols.map((m) =>
        translateModuleDeclaration(m, superParameters.get(m.runtimeName) match {
          case Some(lst) => lst
          case _ => Nil
        }, false)(topLevelScope)
      ) ++
      classSymbols.map { sym =>
        superParameters.get(sym.runtimeName) match {
          case Some(sp) => translateNewClassDeclaration(sym, sp, N, false)(topLevelScope)
          case _ => translateNewClassDeclaration(sym, Nil, N, false)(topLevelScope)
        }
      }.toList

    val exports =
      if (exported)
        JSExport(traitSymbols.map { _.runtimeName } ++
        mixinSymbols.map { _.runtimeName } ++
        moduleSymbols.map{_.runtimeName} ++
        classSymbols.map { _.runtimeName }.toList) :: Nil
      else Nil

    val stmts: Ls[JSStmt] =
        defs
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
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) :: Nil
          // Ignore type declarations.
          case Def(_, _, R(_), isByname) => Nil
          // `exprs.push(<expr>)`.
          case term: Term =>
            translateTerm(term)(topLevelScope).stmt :: Nil
        }) ::: exports
    SourceCode.fromStmts(polyfill.emit() ::: stmts).toLines
  }

  def apply(pgrm: Pgrm, exported: Bool): Ls[Str] = generateNewDef(pgrm, exported)
}

class JSWebBackend extends JSBackend(allowUnresolvedSymbols = true) {
  // Name of the array that contains execution results
  val resultsName: Str = topLevelScope declareRuntimeSymbol "results"

  val prettyPrinterName: Str = topLevelScope declareRuntimeSymbol "prettyPrint"

  polyfill.use("prettyPrint", prettyPrinterName)

  private def generate(pgrm: Pgrm): (Ls[Str], Ls[Str]) = {
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
    (JSImmEvalFn(N, Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines, Nil)
  }

  private def generateNewDef(pgrm: Pgrm): (Ls[Str], Ls[Str]) = {
    val mlsModule = topLevelScope.declareValue("typing_unit", Some(false), false)
    val (diags, (typeDefs, otherStmts)) = pgrm.newDesugared

    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols, superParameters) = declareNewTypeDefs(typeDefs)
    def include(typeName: Str, moduleName: Str) =
      JSExprStmt(JSAssignExpr(JSField(JSIdent("globalThis"), typeName), JSField(JSIdent(moduleName), typeName)))
    val includes =
      traitSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)) ++
      mixinSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)) ++
      moduleSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)) ++
      classSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)).toList

    val defs =
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      mixinSymbols.map { translateMixinDeclaration(_)(topLevelScope) } ++
      moduleSymbols.map((m) =>
        translateModuleDeclaration(m, superParameters.get(m.runtimeName) match {
          case Some(lst) => lst
          case _ => Nil
        })(topLevelScope)
      ) ++
      classSymbols.map { sym =>
        superParameters.get(sym.runtimeName) match {
          case Some(sp) => translateNewClassDeclaration(sym, sp)(topLevelScope)
          case _ => translateNewClassDeclaration(sym)(topLevelScope)
        }
      }.toList

    val defStmts =
      JSLetDecl(Ls(mlsModule.runtimeName -> S(JSRecord(Ls("cache" -> JSRecord(Ls())), defs)))) :: includes

    val resultsIdent = JSIdent(resultsName)
    val resultNames = ListBuffer[Str]()
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
            resultNames += sym.runtimeName
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(resultsIdent("push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          // Ignore type declarations.
          case Def(_, _, R(_), isByname) => Nil
          // `exprs.push(<expr>)`.
          case term: Term =>
            val name = translateTerm(term)(topLevelScope)
            resultNames += name.toSourceCode.toString
            topLevelScope.tempVars `with` JSInvoke(
              resultsIdent("push"),
              name :: Nil
            ).stmt :: Nil
        })
    val epilogue = resultsIdent.member("map")(JSIdent(prettyPrinterName)).`return` :: Nil
    (JSImmEvalFn(N, Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines, resultNames.toList)
  }

  def apply(pgrm: Pgrm, newDefs: Bool): (Ls[Str], Ls[Str]) =
    if (newDefs) generateNewDef(pgrm) else generate(pgrm)
}

class JSTestBackend extends JSBackend(allowUnresolvedSymbols = false) {
  private val lastResultSymbol = topLevelScope.declareValue("res", Some(false), false)
  private val resultIdent = JSIdent(lastResultSymbol.runtimeName)

  private var numRun = 0

  /**
    * Generate a piece of code for test purpose. It can be invoked repeatedly.
    */
  def apply(pgrm: Pgrm, allowEscape: Bool, isNewDef: Boolean): JSTestBackend.Result =
    if (!isNewDef)
      try generate(pgrm)(topLevelScope, allowEscape) catch {
        case e: CodeGenError => JSTestBackend.IllFormedCode(e.getMessage())
        case e: UnimplementedError => JSTestBackend.Unimplemented(e.getMessage())
        // case e: Throwable => JSTestBackend.UnexpectedCrash(e.getClass().getName, e.getMessage())
      }
    else
      try generateNewDef(pgrm)(topLevelScope, allowEscape) catch {
        case e: CodeGenError => JSTestBackend.IllFormedCode(e.getMessage())
        case e: UnimplementedError => JSTestBackend.Unimplemented(e.getMessage())
        // case e: Throwable => JSTestBackend.UnexpectedCrash(e.getClass().getName, e.getMessage())
      }
    // generate(pgrm)(topLevelScope, allowEscape)

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

  private def generateNewDef(pgrm: Pgrm)(implicit scope: Scope, allowEscape: Bool): JSTestBackend.TestCode = {
    val mlsModule = topLevelScope.declareValue("typing_unit", Some(false), false)
    val (diags, (typeDefs, otherStmts)) = pgrm.newDesugared

    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols, superParameters) = declareNewTypeDefs(typeDefs)
    val defStmts = 
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      mixinSymbols.map { translateMixinDeclaration(_)(topLevelScope) } ++
      moduleSymbols.map((m) =>
        translateModuleDeclaration(m, superParameters.get(m.runtimeName) match {
          case Some(lst) => lst
          case _ => Nil
        })(topLevelScope)
      ) ++
      classSymbols.map { sym =>
        superParameters.get(sym.runtimeName) match {
          case Some(sp) => translateNewClassDeclaration(sym, sp)(topLevelScope)
          case _ => translateNewClassDeclaration(sym)(topLevelScope)
        }
      }.toList

    def include(typeName: Str, moduleName: Str) =
      JSExprStmt(JSAssignExpr(JSField(JSIdent("globalThis"), typeName), JSField(JSIdent(moduleName), typeName)))
    val includes =
      traitSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)) ++
      mixinSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)) ++
      moduleSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)) ++
      classSymbols.map((sym) => include(sym.runtimeName, mlsModule.runtimeName)).toList

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
    var prelude: Ls[JSStmt] = JSLetDecl(Ls(mlsModule.runtimeName -> S(JSRecord(Ls("cache" -> JSRecord(Ls())), defStmts)))) :: includes
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
  // final case class UnexpectedCrash(val name: Str, override val content: Str) extends ErrorMessage(content)

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
