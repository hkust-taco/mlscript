package mlscript

import mlscript.utils._, shorthands._, algorithms._
import mlscript.codegen.Helpers._
import mlscript.codegen._
import scala.collection.mutable.{ListBuffer, HashMap}
import mlscript.{JSField, JSLit}
import scala.collection.mutable.{Set => MutSet}
import scala.util.control.NonFatal
import scala.util.chaining._

class JSBackend(allowUnresolvedSymbols: Boolean) {
  /**
    * The root scope of the program.
    */
  protected val topLevelScope = Scope("root")

  /**
    * The prelude code manager.
    */
  protected val polyfill = Polyfill()

  protected val visitedSymbols = MutSet[RuntimeSymbol]()

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
        | If(_, _) | New(_, _) | _: Splc | _: Forall | _: Where | _: Super | _: Eqn =>
      throw CodeGenError(s"term ${inspect(t)} is not a valid pattern")
  }

  private def translateParams(t: Term)(implicit scope: Scope): Ls[JSPattern] = t match {
    case Tup(params) => params map {
      case N -> Fld(_, _, p) => translatePattern(p)
      case S(nme) -> Fld(_, _, p) => translatePattern(nme)
    }
    case _           => throw CodeGenError(s"term $t is not a valid parameter list")
  }

  private def translateNuTypeSymbol(sym: NuTypeSymbol with RuntimeSymbol)(implicit scope: Scope): JSExpr =
    if (!sym.isNested) JSIdent(sym.runtimeName) else
      scope.resolveValue("this") match {
        case Some(selfSymbol) =>
          visitedSymbols += selfSymbol
          JSIdent(selfSymbol.runtimeName).member(sym.runtimeName)
        case _ => throw CodeGenError(s"unexpected NuType symbol ${sym.runtimeName}")
      }

  protected def translateCapture(sym: CapturedSymbol): JSExpr = {
    visitedSymbols += sym.actualSym
    sym.actualSym match {
      case NewClassMemberSymbol(name, _, _, isPrivate) if isPrivate =>
        JSIdent(s"${sym.outsiderSym.runtimeName}.#$name")
      case _ =>
        JSIdent(sym.outsiderSym.runtimeName).member(sym.actualSym.lexicalName)
    }
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
      case S(sym: NuTypeSymbol with RuntimeSymbol) =>
        if (sym.isPlainJSClass || !isCallee) translateNuTypeSymbol(sym)
        else translateNuTypeSymbol(sym).member("class")
      case S(sym: NewClassMemberSymbol) =>
        if (sym.isByvalueRec.getOrElse(false) && !sym.isLam) throw CodeGenError(s"unguarded recursive use of by-value binding $name")
        visitedSymbols += sym
        scope.resolveValue("this") match {
          case Some(selfSymbol) =>
            visitedSymbols += selfSymbol
            val ident = if (sym.isPrivate) JSIdent(s"${selfSymbol.runtimeName}.#${sym.runtimeName}")
                        else JSIdent(selfSymbol.runtimeName).member(sym.runtimeName)
            if (sym.isByvalueRec.isEmpty && !sym.isLam) ident() else ident
          case _ => throw CodeGenError(s"unexpected new class member $name")
        }
      case S(sym: CapturedSymbol) =>
        translateCapture(sym)
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
        case Var(nme) => scope.resolveValue(nme) match {
          case S(sym: NuTypeSymbol with RuntimeSymbol) =>
            translateNuTypeSymbol(sym)
          case _ => translateVar(nme, true)
        }
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
      val flattened = stmts.iterator.flatMap {
        case nt: NuTypeDef => nt :: Nil
        case nf @ NuFunDef(_, Var(nme), _, _) =>
          blkScope.declareStubValue(nme)(true)
          nf.desugared._2
        case other => other.desugared._2
      }.toList
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
          case (nt: NuTypeDef, _) => translateLocalNewType(nt)(blkScope)
          // TODO: find out if we need to support this.
          case (_: Def | _: TypeDef | _: NuFunDef | _: DataDefn | _: DatatypeDefn | _: LetS | _: Constructor, _) =>
            throw CodeGenError("unsupported definitions in blocks")
        }.toList)),
        Nil
      )
    // Pattern match with only one branch -> comma expression
    case CaseOf(trm, Wildcard(default)) =>
      JSCommaExpr(translateTerm(trm) :: translateTerm(default) :: Nil)
    // Pattern match with two branches -> tenary operator
    case CaseOf(trm, Case(tst, csq, Wildcard(alt))) =>
      translateCase(translateTerm(trm), tst)(scope)(translateTerm(csq), translateTerm(alt))
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
      val callee = translateVar(className, true) match {
        case n: JSNew => n
        case t => JSNew(t)
      }
      callee(args.map { case (_, Fld(_, _, arg)) => translateTerm(arg) }: _*)
    case New(_, TypingUnit(_)) =>
      throw CodeGenError("custom class body is not supported yet")
    case Forall(_, bod) => translateTerm(bod)
    case TyApp(base, _) => translateTerm(base)
    case Eqn(Var(name), _) =>
      throw CodeGenError(s"assignment of $name is not supported outside a constructor")
    case _: Bind | _: Test | If(_, _)  | _: Splc | _: Where =>
      throw CodeGenError(s"cannot generate code for term ${inspect(term)}")
  }

  private def translateCaseBranch(scrut: JSExpr, branch: CaseBranches)(implicit
      scope: Scope
  ): JSExpr = branch match {
    case Case(pat, body, rest) =>
      translateCase(scrut, pat)(scope)(translateTerm(body), translateCaseBranch(scrut, rest))
    case Wildcard(body) => translateTerm(body)
    case NoCases        => JSImmEvalFn(N, Nil, R(JSInvoke(
      JSNew(JSIdent("Error")),
      JSExpr("non-exhaustive case expression") :: Nil
    ).`throw` :: Nil), Nil)
  }

  private def translateCase(scrut: JSExpr, pat: SimpleTerm)(implicit scope: Scope) = {
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
        case Var(name) => scope.resolveValue(name) match {
          case S(sym: NewClassSymbol) =>
            if (sym.isPlainJSClass)
              JSInstanceOf(scrut, translateVar(sym.lexicalName, false))
            else
              JSInstanceOf(scrut, translateVar(sym.lexicalName, false).member("class"))
          case S(sym: ModuleSymbol) =>
            JSInstanceOf(scrut, translateVar(sym.lexicalName, false).member("class"))
          case S(sym @ CapturedSymbol(out, cls: NewClassSymbol)) =>
            if (cls.isPlainJSClass)
              JSInstanceOf(scrut, translateCapture(sym))
            else
              JSInstanceOf(scrut, translateCapture(sym).member("class"))
          case S(CapturedSymbol(out, mdl: ModuleSymbol)) =>
            JSInstanceOf(scrut, translateCapture(CapturedSymbol(out, mdl)).member("class"))
          case S(_: MixinSymbol) => throw new CodeGenError(s"cannot match mixin $name")
          case S(CapturedSymbol(out, mdl: MixinSymbol)) =>
            throw new CodeGenError(s"cannot match mixin $name")
          case _ => topLevelScope.getType(name) match {
            case S(ClassSymbol(_, runtimeName, _, _, _)) => JSInstanceOf(scrut, JSIdent(runtimeName))
            case S(TraitSymbol(_, runtimeName, _, _, _)) => JSIdent(runtimeName)("is")(scrut)
            case S(_: TypeAliasSymbol) => throw new CodeGenError(s"cannot match type alias $name")
            case _ => throw new CodeGenError(s"unknown match case: $name")
          }
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

  protected def translateSelfDeclaration(self: ValueSymbol): Ls[JSStmt] =
    if (visitedSymbols(self)) {
      visitedSymbols -= self
      JSConstDecl(self.runtimeName, JSIdent("this")) :: Nil
    }
    else Nil

  
  protected def addNuTypeToGlobalThis(typeDef: NuTypeDef, moduleName: Str) = {
    import JSCodeHelpers._
    typeDef match {
      case NuTypeDef(Mxn, TypeName(nme), _, _, _, _, _, _, _, _) =>
        JSAssignExpr(id("globalThis").member(nme), JSArrowFn(param("base") :: Nil, L(
          JSInvoke(id(moduleName).member(nme), id("base") :: Nil)
        ))).stmt
      case NuTypeDef(_, TypeName(nme), _, _, _, _, _, _, _, _) =>
        JSAssignExpr(id("globalThis").member(nme), id(moduleName).member(nme)).stmt
    }
  }

  protected def translateLocalNewType(typeDef: NuTypeDef)(implicit scope: Scope): JSConstDecl = {
    // TODO: support traitSymbols
    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols) = declareNewTypeDefs(typeDef :: Nil, false)

    val sym = classSymbols match {
      case s :: _ => S(s)
      case Nil => mixinSymbols match {
        case s :: _ => S(s)
        case Nil => moduleSymbols match {
          case s :: _ => S(s)
          case _ => N
        }
      }
    }
    sym match {
      case S(sym: NewClassSymbol) =>
        val localScope = scope.derive(s"local ${sym.lexicalName}")
        val nd = translateNewTypeDefinition(sym, N, true, false)(localScope)
        val ctorMth = localScope.declareValue("ctor", Some(false), false).runtimeName
        val (constructor, params) = translateNewClassParameters(nd)
        val initList =
          if (sym.isPlainJSClass)
            Ls(JSReturnStmt(S(JSIdent(sym.lexicalName))))
          else
            Ls(
              JSLetDecl.from(Ls(ctorMth)),
              JSAssignExpr(JSIdent(ctorMth), JSArrowFn(constructor, L(JSInvoke(JSNew(JSIdent(sym.lexicalName)), params)))).stmt,
              JSExprStmt(JSAssignExpr(JSIdent(ctorMth).member("class"), JSIdent(sym.lexicalName))),
              JSReturnStmt(S(JSIdent(ctorMth)))
            )
        JSConstDecl(sym.lexicalName, JSImmEvalFn(
          N, Nil, R(nd :: initList), Nil
        ))
      case S(sym: MixinSymbol) =>
        val localScope = scope.derive(s"local ${sym.lexicalName}")
        val base = localScope.declareValue("base", Some(false), false)
        val nd = translateNewTypeDefinition(sym, S(base), false, false)(localScope)
        JSConstDecl(sym.lexicalName, JSArrowFn(
          Ls(JSNamePattern(base.runtimeName)), R(Ls(
            JSReturnStmt(S(JSClassExpr(nd)))
          ))
        ))
      case S(sym: ModuleSymbol) =>
        val localScope = scope.derive(s"local ${sym.lexicalName}")
        val nd = translateNewTypeDefinition(sym, N, false, false)(localScope)
        val ins = localScope.declareValue("ins", Some(false), false).runtimeName
        JSConstDecl(sym.lexicalName, JSImmEvalFn(
          N, Nil, R(Ls(
            nd, JSLetDecl.from(Ls(ins)),
            JSAssignExpr(JSIdent(ins), JSInvoke(JSNew(JSIdent(sym.lexicalName)), Nil)).stmt,
            JSExprStmt(JSAssignExpr(JSIdent(ins).member("class"), JSIdent(sym.lexicalName))),
            JSReturnStmt(S(JSIdent(ins)))
          )), Nil
        ))
      case _ => throw CodeGenError(s"unsupported NuTypeDef in local blocks: $typeDef")
    }
  }

  protected def translateMixinDeclaration(
      mixinSymbol: MixinSymbol,
      siblingsMembers: Ls[RuntimeSymbol]
  )(implicit scope: Scope): JSClassMethod = {
    val getterScope = scope.derive(s"getter ${mixinSymbol.lexicalName}")
    val base = getterScope.declareValue("base", Some(false), false)
    val outerSymbol = getterScope.declareOuterSymbol()
    siblingsMembers.foreach(getterScope.captureSymbol(outerSymbol, _))

    val classBody = translateNewTypeDefinition(mixinSymbol, S(base), false, false)(getterScope)
    JSClassMethod(mixinSymbol.lexicalName, Ls(JSNamePattern(base.runtimeName)),
      R((JSConstDecl(outerSymbol.runtimeName, JSIdent("this")) :: Nil) ::: Ls(
        JSReturnStmt(S(JSClassExpr(classBody)))
      ))
    )
  }

  private def translateParents(superFields: Ls[Term], constructorScope: Scope)(implicit scope: Scope): Opt[JSExpr] = {
    def translateParent(current: Term, base: JSExpr, mixinOnly: Bool): JSExpr = {
      def resolveName(term: Term): Str = term match {
        case App(lhs, _) => resolveName(lhs)
        case Var(name) => name
        case Sel(_, Var(fieldName)) => fieldName
        case TyApp(lhs, _) => resolveName(lhs)
        case _ => throw CodeGenError("unsupported parents.")
      }

      val name = resolveName(current)

      scope.resolveValue(name) match {
        case Some(CapturedSymbol(_, _: TraitSymbol)) => base // TODO:
        case Some(CapturedSymbol(out, sym: MixinSymbol)) =>
          JSInvoke(translateCapture(CapturedSymbol(out, sym)), Ls(base))
        case Some(CapturedSymbol(out, sym: NuTypeSymbol)) if !mixinOnly =>
          if (sym.isPlainJSClass)
            translateCapture(CapturedSymbol(out, sym))
          else
            translateCapture(CapturedSymbol(out, sym)).member("class")
        case Some(_: TraitSymbol) => base // TODO:
        case Some(sym: MixinSymbol) =>
          JSInvoke(translateVar(name, false), Ls(base))
        case Some(sym: NuTypeSymbol) if !mixinOnly =>
          if (sym.isPlainJSClass)
            translateVar(name, false)
          else
            translateVar(name, false).member("class")
        case Some(t) => throw CodeGenError(s"unexpected parent symbol $t.")
        case N => throw CodeGenError(s"unresolved parent $name.")
      }
    }

    // for non-first parent classes, they must be mixins or we would get more than one parent classes,
    // which is not allowed in JS
    superFields match {
      case head :: tail => S(tail.foldLeft(
        translateParent(head, JSIdent("Object"), false)
      )((res, next) => translateParent(next, res, true)))
      case Nil => N
    }
  }

  protected def translateTopModuleDeclaration(
    moduleSymbol: ModuleSymbol,
    keepTopLevelScope: Bool
  )(implicit scope: Scope): JSClassNewDecl =
    translateNewTypeDefinition(moduleSymbol, N, false, keepTopLevelScope)

  protected def translateModuleDeclaration(
      moduleSymbol: ModuleSymbol,
      siblingsMembers: Ls[RuntimeSymbol]
  )(implicit scope: Scope): JSClassGetter = {
    val getterScope = scope.derive(s"getter ${moduleSymbol.lexicalName}")
    val outerSymbol = getterScope.declareOuterSymbol()
    siblingsMembers.foreach(getterScope.captureSymbol(outerSymbol, _))

    val decl = translateNewTypeDefinition(moduleSymbol, N, false, false)(getterScope)
    val privateIdent = JSIdent(s"this.#${moduleSymbol.lexicalName}")
    JSClassGetter(moduleSymbol.lexicalName, R((JSConstDecl(outerSymbol.runtimeName, JSIdent("this")) :: Nil) :::
      Ls(
        JSIfStmt(JSBinary("===", privateIdent, JSIdent("undefined")), Ls(
          decl,
          JSExprStmt(JSAssignExpr(privateIdent,
            JSNew(JSInvoke(JSIdent(moduleSymbol.lexicalName), Nil)))),
          JSExprStmt(JSAssignExpr(privateIdent.member("class"), JSIdent(moduleSymbol.lexicalName))),
        )),
        JSReturnStmt(S(privateIdent))
      )))
  }

  protected def translateNewClassParameters(classBody: JSClassNewDecl) = {
    val constructor = classBody match {
      case dec: JSClassNewDecl => dec.fields.map(JSNamePattern(_))
    }
    val params = classBody match {
      case dec: JSClassNewDecl => dec.fields.map(JSIdent(_))
    }

    (constructor, params)
  }

  protected def translateNewClassDeclaration(
      classSymbol: NewClassSymbol,
      siblingsMembers: Ls[RuntimeSymbol]
  )(implicit scope: Scope): JSClassGetter = {
    val getterScope = scope.derive(s"${classSymbol.lexicalName} getter")
    val outerSymbol = getterScope.declareOuterSymbol()
    siblingsMembers.foreach(getterScope.captureSymbol(outerSymbol, _))

    val classBody =
      translateNewTypeDefinition(classSymbol, N, true, false)(getterScope)
    val (constructor, params) = translateNewClassParameters(classBody)

    val privateIdent = JSIdent(s"this.#${classSymbol.lexicalName}")
    val outerStmt = JSConstDecl(outerSymbol.runtimeName, JSIdent("this"))
    val initList =
      if (classSymbol.isPlainJSClass)
        Ls(JSExprStmt(JSAssignExpr(privateIdent, JSIdent(classSymbol.lexicalName))))
      else
        Ls(
          JSExprStmt(JSAssignExpr(privateIdent,
            JSArrowFn(constructor, L(
              JSInvoke(JSIdent("Object").member("freeze"), Ls(JSInvoke(JSNew(JSIdent(classSymbol.lexicalName)), params)))
            )))),
          JSExprStmt(JSAssignExpr(privateIdent.member("class"), JSIdent(classSymbol.lexicalName)))
        )
    JSClassGetter(classSymbol.lexicalName, R(outerStmt :: Ls(
      JSIfStmt(JSBinary("===", privateIdent, JSIdent("undefined")),
        JSExprStmt(JSClassExpr(classBody)) :: initList),
      JSReturnStmt(S(privateIdent))
    )))
  }

  protected def translateNewTypeDefinition(
    sym: TypeSymbol with RuntimeSymbol with NuTypeSymbol,
    baseSym: Opt[ValueSymbol],
    requireUnapply: Bool,
    keepTopLevelScope: Bool
  )(implicit scope: Scope): JSClassNewDecl = {
    val nuTypeScope = scope.derive(sym.toString)
    val constructorScope = nuTypeScope.derive(s"${sym.lexicalName} constructor")
    val selfSymbol = constructorScope.declareThisAlias()

    val memberList = ListBuffer[RuntimeSymbol]() // pass to the getter of nested types
    val typeList = ListBuffer[Str]()

    val fields = sym.body.collectFields ++
      sym.body.collectTypeNames.flatMap(resolveTraitFields)

    val ctorParams = sym.ctorParams.fold(
      fields.map { f =>
          memberList += NewClassMemberSymbol(f, Some(false), false, false).tap(nuTypeScope.register)
          constructorScope.declareValue(f, Some(false), false).runtimeName
        }
      )(lst => lst.map { p =>
          constructorScope.declareValue(p, Some(false), false).runtimeName
        })

    sym.methods.foreach {
      case MethodDef(_, _, Var(nme), _, _) => memberList += NewClassMemberSymbol(nme, N, true, false).tap(nuTypeScope.register)
    }
    sym.ctor.foreach {
      case nd @ NuFunDef(rec, Var(nme), _, _) =>
        memberList += NewClassMemberSymbol(nme, rec, false, !nd.genField).tap(nuTypeScope.register)
      case _ => ()
    }

    // TODO: support traitSymbols
    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols) = declareNewTypeDefs(sym.nested, true)(nuTypeScope)

    if (keepTopLevelScope) // also declare in the top level for diff tests
      declareNewTypeDefs(sym.nested, false)(topLevelScope)
    classSymbols.foreach(s => {memberList += s; typeList += s.lexicalName})
    mixinSymbols.foreach(s => {memberList += s;})
    moduleSymbols.foreach(s => {memberList += s; typeList += s.lexicalName})
    val members = sym.methods.map {
      translateNewClassMember(_, fields)(nuTypeScope)
    } ++
      mixinSymbols.map
        { translateMixinDeclaration(_, memberList.toList)(nuTypeScope) } ++
      moduleSymbols.map
        { translateModuleDeclaration(_, memberList.toList)(nuTypeScope) } ++
      classSymbols.map
        { translateNewClassDeclaration(_, memberList.toList)(nuTypeScope) }

    val base: Opt[JSExpr] = baseSym match {
      case Some(base) => S(JSIdent(base.runtimeName))
      case _ => translateParents(sym.superParameters, constructorScope)
    }

    val traits = sym.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }

    val (superParameters, rest) = if (baseSym.isDefined) {
      val rest = constructorScope.declareValue("rest", Some(false), false)
      (Ls(JSIdent(s"...${rest.runtimeName}")), S(rest.runtimeName))
    }
    else
      (sym.superParameters.map {
        case App(lhs, Tup(rhs)) => rhs map {
          case (_, Fld(mut, spec, trm)) => translateTerm(trm)(constructorScope)
        }
        case _ => Nil
      }.flatMap(_.reverse).reverse, N)

    val getters = new ListBuffer[Str]()
    val privateMems = new ListBuffer[Str]()
    val stmts = sym.ctor.flatMap {
      case Eqn(Var(name), rhs) => Ls(
        JSAssignExpr(JSIdent(s"this.#$name"), translateTerm(rhs)(constructorScope)).stmt,
        JSConstDecl(constructorScope.declareValue(name, S(false), false).runtimeName, JSIdent(s"this.#$name"))
      )
      case s: Term => JSExprStmt(translateTerm(s)(constructorScope)) :: Nil
      case nd @ NuFunDef(_, Var(nme), _, Left(rhs)) =>
        if (nd.genField) {
          getters += nme
          Ls[JSStmt](
            JSExprStmt(JSAssignExpr(JSIdent(s"this.#$nme"), translateTerm(rhs)(constructorScope))),
            JSConstDecl(constructorScope.declareValue(nme, S(false), false).runtimeName, JSIdent(s"this.#$nme"))
          )
        }
        else {
          val sym = nuTypeScope.resolveValue(nme) match {
            case Some(sym: NewClassMemberSymbol) => sym
            case _ => throw new AssertionError(s"error when handling $nme")
          }
          if (visitedSymbols.contains(sym)) {
            privateMems += nme
            visitedSymbols -= sym
            Ls[JSStmt](
              JSExprStmt(JSAssignExpr(JSIdent(s"this.#$nme"), translateTerm(rhs)(constructorScope))),
              JSConstDecl(constructorScope.declareValue(nme, S(false), false).runtimeName, JSIdent(s"this.#$nme"))
            )
          }
          else
            JSConstDecl(constructorScope.declareValue(nme, S(false), false).runtimeName,
              translateTerm(rhs)(constructorScope)) :: Nil
        }
      case _ => Nil
    }

    val tempDecs = constructorScope.tempVars.emit() match {
      case S(decs) => decs :: Nil
      case _ => Nil
    }

    JSClassNewDecl(
      sym.lexicalName,
      fields,
      fields ::: getters.toList,
      privateMems.toList,
      base,
      superParameters,
      ctorParams,
      rest,
      members,
      traits,
      translateSelfDeclaration(selfSymbol) ::: tempDecs ::: stmts,
      typeList.toList,
      sym.ctorParams.isDefined,
      requireUnapply && !sym.isPlainJSClass
    )
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
    props: Ls[Str] // for overriding
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
    val tempDecs = memberScope.tempVars.emit() match {
      case S(decs) => decs :: Nil
      case _ => Nil
    }

    // If `this` is accessed, add `const self = this`.
    val bodyStmts = if (visitedSymbols(selfSymbol)) {
      val thisDecl = JSConstDecl(selfSymbol.runtimeName, JSIdent("this"))
      visitedSymbols -= selfSymbol
      R(preDecs ::: tempDecs ::: (thisDecl :: bodyResult :: Nil))
    } else R(preDecs ::: tempDecs ::: (bodyResult :: Nil))
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
      case TypeDef(Mxn, _, _, _, _, _, _) => throw CodeGenError("Mixins are not supported yet.")
      case TypeDef(Mod, _, _, _, _, _, _) => throw CodeGenError("Namespaces are not supported yet.")
    }
    (traits.toList, classes.toList)
  }

  protected def declareNewTypeDefs(typeDefs: Ls[NuTypeDef], isNested: Bool)(implicit scope: Scope):
      (Ls[TraitSymbol], Ls[NewClassSymbol], Ls[MixinSymbol], Ls[ModuleSymbol]) = {
    val traits = new ListBuffer[TraitSymbol]()
    val classes = new ListBuffer[NewClassSymbol]()
    val mixins = new ListBuffer[MixinSymbol]()
    val modules = new ListBuffer[ModuleSymbol]()
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
      val members = unit.entities.collect {
        case NuFunDef(isLetRec, mnme, tys, Left(rhs)) if (isLetRec.isEmpty || isLetRec.getOrElse(false)) =>
          MethodDef[Left[Term, Type]](isLetRec.getOrElse(false), TypeName(nme), mnme, tys, Left(rhs))
      }

      val stmts = unit.entities.filter {
        case Asc(Var("this"), _) => false
        case Asc(Super(), _) => false
        case NuFunDef(S(false), _, _, Left(rhs)) => true
        case _: Term => true
        case _ => false
      }

      val nested = unit.entities.collect {
        case nd: NuTypeDef => nd
      }
      
      (body, members, stmts, nested)
    }

    typeDefs.foreach {
      case td @ NuTypeDef(Mxn, TypeName(mxName), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (body, members, stmts, nested) = prepare(mxName, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym = MixinSymbol(mxName, tps map { _._2.name }, body, members, stmts, nested, isNested).tap(scope.register)
        if (!td.isDecl) mixins += sym
      }
      case td @ NuTypeDef(Mod, TypeName(nme), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (body, members, stmts, nested) = prepare(nme, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym = ModuleSymbol(nme, tps map { _._2.name }, body, members, stmts, pars, nested, isNested).tap(scope.register)
        if (!td.isDecl) modules += sym
      }
      case td @ NuTypeDef(Als, TypeName(nme), tps, _, ctor, sig, pars, _, _, _) => {
        scope.declareTypeAlias(nme, tps map { _._2.name }, sig.getOrElse(Top))
      }
      case td @ NuTypeDef(Cls, TypeName(nme), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (params, preStmts) = ctor match {
          case S(Constructor(Tup(ls), Blk(stmts))) => (S(ls.map {
            case (S(Var(nme)), _) => nme
            case _ => throw CodeGenError(s"Unexpected constructor parameters in $nme.")
          }), stmts)
          case _ => (N, Nil)
        }
        val (body, members, stmts, nested) = prepare(nme, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym =
          NewClassSymbol(nme, tps map { _._2.name }, params, body, members, preStmts ++ stmts, pars, nested, isNested, td.isPlainJSClass).tap(scope.register)
        if (!td.isDecl) classes += sym
      }
      case td @ NuTypeDef(Trt, TypeName(nme), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (body, members, _, _) = prepare(nme, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym = scope.declareTrait(nme, tps map { _._2.name }, body, members)
        if (!td.isDecl) traits += sym
      }
    }
    (traits.toList, classes.toList, mixins.toList, modules.toList)
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
    val (typeDefs, otherStmts) = pgrm.tops.partitionMap {
      case ot: Terms => R(ot)
      case fd: NuFunDef => R(fd)
      case nd: NuTypeDef => L(nd)
      case _ => die
   }

    // don't pass `otherStmts` to the top-level module, because we need to execute them one by one later
    val topModule = topLevelScope.declareTopModule("TypingUnit", Nil, typeDefs, true)
    val moduleIns = topLevelScope.declareValue("typing_unit", Some(false), false)
    val moduleDecl = translateTopModuleDeclaration(topModule, true)(topLevelScope)
    val insDecl =
      JSConstDecl(moduleIns.runtimeName, JSNew(JSIdent(topModule.runtimeName)))

    val includes = typeDefs.filter(!_.isDecl).map(addNuTypeToGlobalThis(_, moduleIns.runtimeName))

    val resultsIdent = JSIdent(resultsName)
    val resultNames = ListBuffer[Str]()
    val stmts: Ls[JSStmt] =
      JSConstDecl(resultsName, JSArray(Nil)) ::
        (moduleDecl :: insDecl :: includes)
        // Generate something like:
        // ```js
        // const <name> = <expr>;
        // <results>.push(<name>);
        // ```
        .concat(otherStmts.flatMap {
          case NuFunDef(isLetRec, nme @ Var(name), tys, rhs @ L(body)) =>
            val recursive = isLetRec.getOrElse(true)
            val isByname = isLetRec.isEmpty
            val bodyIsLam = body match { case _: Lam => true case _ => false }
            val (originalExpr, sym) = (if (recursive) {
              val isByvalueRecIn = if (isByname) None else Some(true)
              val sym = topLevelScope.declareValue(name, isByvalueRecIn, bodyIsLam)
              val translated = translateTerm(body)(topLevelScope)
              topLevelScope.unregisterSymbol(sym)
              val isByvalueRecOut = if (isByname) None else Some(false)
              (translated, topLevelScope.declareValue(name, isByvalueRecOut, bodyIsLam))
            } else {
              val translated = translateTerm(body)(topLevelScope)
              val isByvalueRec = if (isByname) None else Some(false)
              (translated, topLevelScope.declareValue(name, isByvalueRec, bodyIsLam))
            })
            val translatedBody = if (sym.isByvalueRec.isEmpty && !sym.isLam) JSArrowFn(Nil, L(originalExpr)) else originalExpr
            resultNames += sym.runtimeName
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(resultsIdent("push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          case fd @ NuFunDef(isLetRec, Var(name), tys, R(ty)) =>
            Nil
          case _: Def | _: TypeDef =>
            throw CodeGenError("Def and TypeDef are not supported in NewDef files.")
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
    val (typeDefs, otherStmts) = pgrm.tops.partitionMap {
      case _: Constructor => throw CodeGenError("unexpected constructor.")
      case ot: Terms => R(ot)
      case fd: NuFunDef => R(fd)
      case nd: NuTypeDef => L(nd)
      case _ => die
    }

    // don't pass `otherStmts` to the top-level module, because we need to execute them one by one later
    val topModule = topLevelScope.declareTopModule("TypingUnit", Nil, typeDefs, true)
    val moduleIns = topLevelScope.declareValue("typing_unit", Some(false), false)
    val moduleDecl = translateTopModuleDeclaration(topModule, true)
    val insDecl =
      JSConstDecl(moduleIns.runtimeName, JSNew(JSIdent(topModule.runtimeName)))

    val includes = typeDefs.filter(!_.isDecl).map(addNuTypeToGlobalThis(_, moduleIns.runtimeName))

    val zeroWidthSpace = JSLit("\"\\u200B\"")
    val catchClause = JSCatchClause(
      JSIdent("e"),
      (zeroWidthSpace + JSIdent("e") + zeroWidthSpace).log() :: Nil
    )

    otherStmts.foreach {
      case fd @ NuFunDef(isLetRec, Var(nme), _, L(body)) if (isLetRec.isEmpty || isLetRec.getOrElse(false)) =>
        val isByname = isLetRec.isEmpty
        val isByvalueRecIn = if (isByname) None else Some(true)
        val bodyIsLam = body match { case _: Lam => true case _ => false }
        scope.declareValue(nme, isByvalueRecIn, bodyIsLam)
      case _ => ()
    }

    // Generate statements.
    val queries = otherStmts.map {
      case NuFunDef(isLetRec, nme @ Var(name), tys, rhs @ L(body)) =>
        val recursive = isLetRec.getOrElse(true)
        val isByname = isLetRec.isEmpty
        val bodyIsLam = body match { case _: Lam => true case _ => false }
        (if (recursive) {
          val isByvalueRecIn = if (isByname) None else Some(true)
          val sym = scope.resolveValue(name) match {
            case Some(s: ValueSymbol) => s
            case _ => scope.declareValue(name, isByvalueRecIn, bodyIsLam)
          }
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
      case fd @ NuFunDef(isLetRec, Var(name), tys, R(ty)) =>
        scope.declareStubValue(name)(allowEscape || fd.isDecl)
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
      case _: Def | _: TypeDef =>
        throw CodeGenError("Def and TypeDef are not supported in NewDef files.")
    }

    // If this is the first time, insert the declaration of `res`.
    var prelude: Ls[JSStmt] = Ls(moduleDecl, insDecl) ::: includes
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
