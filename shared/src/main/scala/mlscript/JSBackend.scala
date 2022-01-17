package mlscript

import mlscript.utils._, shorthands._
import scala.util.matching.Regex
import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList
import scala.collection.immutable
import mlscript.codegen.{CodeGenError, UnimplementedError, Scope, ValueSymbol}
import mlscript.codegen.ClassSymbol
import mlscript.codegen.BuiltinSymbol
import mlscript.codegen.StubValueSymbol
import mlscript.codegen.TraitSymbol
import mlscript.codegen.LexicalSymbol
import mlscript.codegen.FreeSymbol
import mlscript.codegen.ParamSymbol
import mlscript.codegen.TypeSymbol
import scala.collection.mutable.ArrayBuffer

class JSBackend {
  /**
    * The root scope of the program.
    */
  protected val topLevelScope = Scope("root")

  /**
    * The prelude code manager.
    */
  protected val polyfill = Polyfill()

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
  private def translatePattern(t: Term): JSPattern = t match {
    // fun x -> ... ==> function (x) { ... }
    // should returns ("x", ["x"])
    case Var(name) => JSNamePattern(name)
    // fun { x, y } -> ... ==> function ({ x, y }) { ... }
    // should returns ("{ x, y }", ["x", "y"])
    case Rcd(fields) =>
      JSObjectPattern(fields map {
        case (Var(nme), Var(als)) if nme === als => nme -> N
        case (Var(nme), subTrm)                  => nme -> S(translatePattern(subTrm))
      })
    // This branch supports `def f (x: int) = x`.
    case Asc(trm, _) => translatePattern(trm)
    // Replace literals with wildcards.
    case _: Lit      => JSWildcardPattern()
    case Bra(_, trm) => translatePattern(trm)
    case Tup(fields) => JSArrayPattern(fields map { case (_, t) => translatePattern(t) })
    // Others are not supported yet.
    case _: Lam | _: App | _: Sel | _: Let | _: Blk | _: Bind | _: Test | _: With | _: CaseOf =>
      throw CodeGenError(s"term ${JSBackend.inspectTerm(t)} is not a valid pattern")
  }

  private def translateParams(t: Term): Ls[JSPattern] = t match {
    case Tup(params) => params map { case _ -> p => translatePattern(p) }
    case _           => throw CodeGenError(s"term $t is not a valid parameter list")
  }

  protected def translateVar(sym: LexicalSymbol, isCallee: Bool)(implicit scope: Scope): JSExpr =
    sym match {
      case sym: ClassSymbol =>
        if (isCallee)
          JSIdent(sym.runtimeName, true)
        else
          JSArrowFn(JSNamePattern("x") :: Nil, L(JSIdent(sym.runtimeName, true)(JSIdent("x"))))
      case sym: BuiltinSymbol =>
        if (!polyfill.used(sym.feature))
          polyfill.use(sym.feature, sym.runtimeName)
        val ident = JSIdent(sym.runtimeName)
        if (sym.feature === "error") ident() else ident
      case sym: StubValueSymbol => throw new UnimplementedError(sym)
      case _: FreeSymbol => throw new CodeGenError(s"unresolved symbol ${sym.lexicalName}")
      case _: TraitSymbol | _: TypeSymbol => throw new CodeGenError(s"cannot use ${sym.shortName} in expressions")
      case _ => JSIdent(sym.runtimeName)
    }

  // Returns: temp identifiers and the expression
  protected def translateTerm(term: Term)(implicit scope: Scope): JSExpr = term match {
    case Var(name) => translateVar(scope.resolve(name), false)
    // TODO: need scope to track variables so that we can rename reserved words
    case Lam(params, body) =>
      val patterns = translateParams(params)
      val lamScope = Scope("Lam", patterns flatMap { _.bindings }, scope)
      JSArrowFn(patterns, lamScope.tempVars `with` translateTerm(body)(lamScope))
    // TODO: when scope symbols are ready, rewrite this
    // Binary expressions called by function names.
    // case App(App(Var(name), Tup((N -> lhs) :: Nil)), Tup((N -> rhs) :: Nil))
    //     if JSBackend.builtinFnOpMap contains name =>
    //   JSBinary(JSBackend.builtinFnOpMap(name), translateTerm(lhs), translateTerm(rhs))
    // Binary expressions called by operators.
    case App(App(Var(op), Tup((N -> lhs) :: Nil)), Tup((N -> rhs) :: Nil))
        if JSBinary.operators contains op =>
      JSBinary(op, translateTerm(lhs), translateTerm(rhs))
    // Tenary expressions.
    case App(App(App(Var("if"), tst), con), alt) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    case App(trm, Tup(args)) =>
      lazy val arguments = args map { case (_, arg) => translateTerm(arg) }
      trm match {
        case Var(name) => scope.resolve(name) match {
          case sym: TraitSymbol => arguments match {
            case head :: Nil => head
            case _ => throw new CodeGenError("trait construction should have only one argument")
          }
          case sym =>
            val callee = translateVar(sym, true)
            callee(arguments: _*)
        }
        case _ =>
          val callee = translateTerm(trm)
          callee(arguments: _*)
      }
    case Rcd(fields) =>
      JSRecord(fields map { case (key, value) =>
        key.name -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSMember(translateTerm(receiver), fieldName.name)
    // Turn let into an IIFE.
    case Let(isRec, Var(name), value, body) =>
      val letScope = scope.derive("Let", name :: Nil)
      JSImmEvalFn(
        name :: Nil,
        letScope.tempVars `with` translateTerm(body)(letScope),
        translateTerm(value)(letScope) :: Nil
      )
    case Blk(stmts) =>
      val blkScope = scope.derive("Blk")
      JSImmEvalFn(
        Nil,
        R(blkScope.tempVars `with` (stmts flatMap (_.desugared._2) map {
          case t: Term             => JSExprStmt(translateTerm(t))
          // TODO: find out if we need to support this.
          case _: Def | _: TypeDef => throw new CodeGenError("unexpected definitions in blocks")
        })),
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
    // `Asc(x, ty)` <== `x: Type`
    case Asc(trm, _) => translateTerm(trm)
    // `c with { x = "hi"; y = 2 }`
    case With(trm, Rcd(fields)) =>
      JSInvoke(
        JSIdent(polyfill get "withConstruct" match {
          case S(fnName) => fnName
          case N         => polyfill.use("withConstruct", topLevelScope.declareRuntimeSymbol("withConstruct"))
        }),
        translateTerm(trm) :: JSRecord(fields map { case (Var(name), value) =>
          name -> translateTerm(value)
        }) :: Nil
      )
    case Bra(_, trm) => translateTerm(trm)
    case Tup(terms) =>
      JSArray(terms map { case (_, term) => translateTerm(term) })
    case App(_, _) | _: Bind | _: Test =>
      throw CodeGenError(s"cannot generate code for term ${JSBackend.inspectTerm(term)}")
  }

  private def translateCaseBranch(scrut: JSExpr, branch: CaseBranches)(implicit
      scope: Scope
  ): JSExpr = branch match {
    case Case(pat, body, rest) =>
      translateCase(scrut, pat)(translateTerm(body), translateCaseBranch(scrut, rest))
    case Wildcard(body) => translateTerm(body)
    case NoCases        => JSImmEvalFn(Nil, R(JSInvoke(
      JSIdent("Error", true),
      JSExpr("non-exhaustive case expression") :: Nil
    ).`throw` :: Nil), Nil)
  }

  private def translateCase(scrut: JSExpr, pat: SimpleTerm) = {
    JSTenary(
      pat match {
        case Var("int") =>
          JSInvoke(JSMember(JSIdent("Number"), "isInteger"), scrut :: Nil)
        case Var("bool") =>
          JSBinary("==", JSMember(scrut, "constructor"), JSLit("Boolean"))
        case Var(s @ ("true" | "false")) =>
          JSBinary("==", scrut, JSLit(s))
        case Var("string") =>
          // JS is dumb so `instanceof String` won't actually work on "primitive" strings...
          JSBinary("==", JSMember(scrut, "constructor"), JSLit("String"))
        case Var(clsName) =>
          JSInstanceOf(scrut, JSIdent(clsName))
        case lit: Lit =>
          JSBinary("==", scrut, JSLit(lit.idStr))
      },
      _,
      _
    )
  } 

  // This function normalizes a type, removing all `AppliedType`s.
  private def substitute(
      body: Type,
      subs: collection.immutable.HashMap[Str, Type] = collection.immutable.HashMap.empty
  ): Type = {
    body match {
      case Neg(ty) =>
        Neg(substitute(ty, subs))
      case AppliedType(TypeName(name), targs) =>
        topLevelScope.get(name) match {
          case sym: ClassSymbol => TypeName(name) // Note that here we erase the arguments.
          case sym: TraitSymbol => ??? 
          case sym: TypeSymbol =>
            assert(targs.length === sym.params.length, targs -> sym.params)
            substitute(
              sym.body,
              collection.immutable.HashMap(
                sym.params zip targs map { case (k, v) => k -> v }: _*
              )
            )
          case _ => throw new CodeGenError(s"$name is none of class, trait or type")
        }
      case Function(lhs, rhs) =>
        Function(substitute(lhs, subs), substitute(rhs, subs))
      case Inter(lhs, rhs) =>
        Inter(substitute(lhs, subs), substitute(rhs, subs))
      case Record(fields) =>
        Record(fields map { case (k, v) => k -> substitute(v, subs) })
      case Union(lhs, rhs) =>
        Union(substitute(lhs, subs), substitute(rhs, subs))
      case Tuple(fields) =>
        Tuple(fields map { case (k, v) => k -> substitute(v, subs) })
      case TypeName(name) =>
        subs get name match {
          case N =>
            topLevelScope.get(name) match {
              case sym: ClassSymbol => TypeName(name)
              case sym: TraitSymbol => TypeName(name)
              case sym: TypeSymbol if sym.params.isEmpty => substitute(sym.body, subs)
              case sym: TypeSymbol => throw CodeGenError(
                  s"type $name expects ${sym.params.length} type parameters but nothing provided"
              )
              case _ => throw new CodeGenError(s"undeclared type name $name")
            }
          case S(ty) => ty
        }
      case Recursive(uv, ty) => Recursive(uv, substitute(ty, subs))
      case Rem(ty, fields)   => Rem(substitute(ty, subs), fields)
      case Bot | Top | _: Literal | _: TypeVar | _: Bounds | _: WithExtension => body
    }
  }

  // Translate MLscript class declaration to JavaScript class declaration.
  // First, we will analyze its fields and base class name.
  // Then, we will check if the base class exists.
  protected def translateClassDeclaration(
      name: Str,
      actualType: Type,
      methods: Ls[MethodDef[Left[Term, Type]]]
  )(implicit scope: Scope): JSClassDecl = {
    val members = methods map { translateClassMember(_) }
    topLevelScope.expect[ClassSymbol](name) match {
      case S(sym) => sym.baseClass match {
        case N => JSClassDecl(name, sym.fields.distinct, N, members)
        case S(clsNme) => sym.body match {
          case S(cls) => JSClassDecl(name, sym.fields.distinct, S(cls), members)
          // TODO: resolve inheritance graph before translation.
          case N => throw new CodeGenError("base class translated after the derived class")
        }
      }
      case N => throw new Exception(s"undeclared class $name, did you call `declareTypeDefs`?")
    }
  }

  private def translateClassMember(
      method: MethodDef[Left[Term, Type]]
  )(implicit scope: Scope): JSClassMemberDecl = {
    val name = method.nme.name
    method.rhs.value match {
      case Lam(params, body) =>
        JSClassMethod(name, translateParams(params), L(translateTerm(body)))
      case term => JSClassGetter(name, L(translateTerm(term)))
    }
  }

  /**
    * Declare symbols for types, traits and classes.
    * Call this before the code generation.
    */
  protected def declareTypeDefs(typeDefs: Ls[TypeDef]): Ls[ClassSymbol] = {
    val classes = new ArrayBuffer[ClassSymbol]()
    typeDefs foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
        topLevelScope.declareType(name, tparams map { _.name }, body)
      case TypeDef(Trt, TypeName(name), tparams, body, _, _) =>
        topLevelScope.declareTrait(name, tparams map { _.name }, body)
      case TypeDef(Cls, TypeName(name), tparams, baseType, _, members) =>
        val sym = topLevelScope.declareClass(name, tparams map { _.name }, baseType)
        sym.fields = resolveClassFields(baseType) // TODO: make it a constructor field
        members foreach { case MethodDef(_, _, Var(name), _, _) => sym.declareMember(name) }
        classes += sym
    }
    classes.toList
  }

  private def resolveClassFields(ty: Type): Ls[Str] = ty match {
    case Top => Nil
    case Record(fields) => fields.map(_._1.name)
    case TypeName(_) => Nil
    case Inter(Record(entries), ty) =>
      entries.map(_._1.name) ++ resolveClassFields(ty)
    case Inter(ty, Record(entries)) =>
      resolveClassFields(ty) ++ entries.map(_._1.name)
    case Inter(ty1, ty2) => resolveClassFields(ty1) ++ resolveClassFields(ty2)
    case AppliedType(TypeName(_), _) => Nil
    // Others are considered as ill-formed.
    case Rem(_, _) | TypeVar(_, _) | Literal(_) | Recursive(_, _) | Bot | Top | Tuple(_) | Neg(_) |
        Bounds(_, _) | WithExtension(_, _) | Function(_, _) | Union(_, _) =>
      throw CodeGenError(s"unable to derive from type $ty")
  }

  /**
    * Find the base class for a specific class.
    */
  private def resolveClassBase(ty: Type): Opt[ClassSymbol] = ty match {
    // `class A` ==> `class A {}`
    case Top => N
    // `class A { <items> }` ==>
    // `class A { constructor(fields) { <items> } }`
    case Record(_) => N
    // `class B: A` ==> `class B extends A {}`
    // If `A` is a type alias, it is replaced by its real type.
    // Otherwise just use the name.
    case TypeName(name) =>
      topLevelScope.get(name) match {
        // The name refers to a class.
        case sym: ClassSymbol => S(sym)
        // TODO: traits can inherit from classes!
        case sym: TraitSymbol => N
        case sym: TypeSymbol if sym.params.isEmpty =>
          // The base class is a type alias with no parameters.
          // Good, just make sure all term is normalized.
          resolveClassBase(substitute(sym.body))
        case sym: TypeSymbol => 
          throw CodeGenError(
            s"type $name expects ${sym.params.length} type parameters but none provided"
          )
        case _ => throw new CodeGenError(s"undeclared type name $name")
      }
    // `class C: <X> & <Y>`: resolve X and Y respectively.
    case Inter(ty1, ty2) => (resolveClassBase(ty1), resolveClassBase(ty2)) match {
      case (N, N) =>
        N
      case (N, S(cls)) =>
        S(cls)
      case (S(cls), N) =>
        S(cls)
      case (S(cls1), S(cls2)) =>
        if (cls1 === cls2) {
          S(cls1)
        } else {
          throw CodeGenError(s"cannot have two base classes: ${cls1.lexicalName}, ${cls2.lexicalName}")
        }
    }
    // `class C: F[X]` and (`F[X]` => `A`) ==> `class C extends A {}`
    // For applied types such as `Id[T]`, normalize them before translation.
    // Do not forget to normalize type arguments first.
    case AppliedType(TypeName(name), targs) =>
      topLevelScope.get(name) match {
        // The name refers to a class.
        case sym: ClassSymbol => S(sym)
        // TODO: traits can inherit from classes!
        case sym: TraitSymbol => N
        case sym: TypeSymbol if sym.params.isEmpty =>
          // The base class is a type alias with no parameters.
          // Good, just make sure all term is normalized.
          resolveClassBase(substitute(sym.body))
        case sym: TypeSymbol => 
          assert(targs.length === sym.params.length, targs -> sym.params)
          val normalized = substitute(
            sym.body,
            collection.immutable.HashMap(sym.params zip targs map { case (k, v) => k -> v }: _*)
          )
          resolveClassBase(normalized)
        case _ => throw new CodeGenError(s"undeclared type name $name")
      }
    // There is some other possibilities such as `class Fun[A]: A -> A`.
    // But it is not achievable in JavaScript.
    case Rem(_, _) | TypeVar(_, _) | Literal(_) | Recursive(_, _) | Bot | Top | Tuple(_) | Neg(_) |
        Bounds(_, _) | WithExtension(_, _) | Function(_, _) | Union(_, _) =>
      throw CodeGenError(s"unable to derive from type $ty")
  }

  /**
    * Resolve inheritance of all declared classes.
    * Make sure call `declareTypeDefs` before calling this.
    */
  protected def resolveInheritance(classSymbols: Ls[ClassSymbol]): Unit =
    classSymbols foreach { sym => resolveClassBase(sym.base) }

  /**
    * Sort class symbols topologically.
    * Therefore, all classes are declared before their derived classes.
    */
  protected def sortClassSymbols(classSymbols: Ls[ClassSymbol]): Unit = {
    import collection.mutable.{HashMap, HashSet, Queue}
    val derivedClasses = HashMap[ClassSymbol, HashSet[ClassSymbol]]()
    classSymbols foreach { sym =>
      sym.baseClass foreach { base =>
        derivedClasses.getOrElseUpdate(base, HashSet()) += sym
      }
    }
    val queue = Queue.from(classSymbols filter { _.baseClass.isEmpty })
    var order = 0
    while (!queue.isEmpty) {
      val sym = queue.dequeue()
      sym.order = order
      order += 1
      derivedClasses.get(sym) foreach { derived =>
        derived foreach { queue += _ }
      }
    }
  }

  protected def generateClassDeclarations(typeDefs: Ls[TypeDef]): Ls[JSClassDecl] = {
    val stmtsWithOrder = typeDefs flatMap {
      case TypeDef(Cls, TypeName(name), typeParams, actualType, _, mthDefs) =>
        topLevelScope.expect[ClassSymbol](name) match {
          case S(sym) =>
            val body = translateClassDeclaration(name, actualType, mthDefs)(topLevelScope)
            sym.body = S(body)
            S(body -> sym.order)
          // Should crash if the class is not defined.
          case N => throw new Exception(s"class $name should be declared")
        }
      case _ => N
    }
    // TODO: this is ugly!
    stmtsWithOrder.sortWith(_._2 < _._2).map(_._1)
  }
}

class JSWebBackend extends JSBackend {
  // Name of the array that contains execution results
  val resultsName: Str = topLevelScope declareRuntimeSymbol "results"

  val prettyPrinterName: Str = topLevelScope declareRuntimeSymbol "prettyPrint"

  polyfill.use("prettyPrint", prettyPrinterName)

  def apply(pgrm: Pgrm): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    var classSymbols = declareTypeDefs(typeDefs)
    resolveInheritance(classSymbols)
    sortClassSymbols(classSymbols)

    val resultsIdent = JSIdent(resultsName)
    val stmts: Ls[JSStmt] =
      JSConstDecl(resultsName, JSArray(Nil)) ::
        generateClassDeclarations(typeDefs)
        // Generate something like:
        // ```js
        // const <name> = <expr>;
        // <results>.push(<name>);
        // ```
        .concat(otherStmts.flatMap {
          case Def(recursive, Var(name), L(body)) =>
            val (translatedBody, sym) = if (recursive) {
              val sym = topLevelScope.declareValue(name)
              (translateTerm(body)(topLevelScope), sym)
            } else {
              val translatedBody = translateTerm(body)(topLevelScope)
              (translatedBody, topLevelScope.declareValue(name))
            }
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(JSMember(resultsIdent, "push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          // Ignore type declarations.
          case Def(_, _, R(_)) => Nil
          // `exprs.push(<expr>)`.
          case term: Term =>
            topLevelScope.tempVars `with` JSInvoke(
              JSMember(resultsIdent, "push"),
              translateTerm(term)(topLevelScope) :: Nil
            ).stmt :: Nil
        })
    val epilogue = resultsIdent.member("map")(JSIdent(prettyPrinterName)).`return` :: Nil
    JSImmEvalFn(Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines
  }
}

class JSTestBackend extends JSBackend {
  private val resultName = topLevelScope declareRuntimeSymbol "res"

  private var numRun = 0

  // TODO: make the return type more readable
  def apply(pgrm: Pgrm): (Str, Bool) \/ TestCode = try {
    R(generate(pgrm))
  } catch {
    case e: CodeGenError => L(e.getMessage() -> false) // Intended errors
    case e: Throwable => L(e.getMessage() -> true) // Unexpected crashes
  }

  /**
    * Generate JavaScript code which targets MLscript test from the given block.
    */
  private def generate(pgrm: Pgrm): TestCode = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    var classSymbols = declareTypeDefs(typeDefs)
    resolveInheritance(classSymbols)
    sortClassSymbols(classSymbols)

    val resultIdent = JSIdent(resultName)

    val defStmts = generateClassDeclarations(typeDefs)

    val zeroWidthSpace = JSLit("\"\\u200B\"")
    val catchClause = JSCatchClause(
      JSIdent("e"),
      (zeroWidthSpace + JSIdent("e") + zeroWidthSpace).log() :: Nil
    )

    // Generate statements.
    val queries: Ls[Opt[JSLetDecl] -> Ls[JSStmt]] =
      otherStmts.flatMap {
        // let <name>;
        // try { <name> = <expr>; res = <name>; }
        // catch (e) { console.log(e); }
        case Def(rec, Var(name), L(body)) =>
          val translatedBody = translateTerm(body)(topLevelScope)
          val sym = topLevelScope.declareValue(name)
          S(
            topLevelScope.tempVars.emit() ->
             ((JSIdent("globalThis").member(sym.runtimeName) := (translatedBody match {
                case t: JSArrowFn => t.toFuncExpr(S(sym.runtimeName))
                case t            => t
              })) ::
                (resultIdent := JSIdent(sym.runtimeName)) ::
                Nil)
          )
        case Def(_, Var(name), R(_)) =>
          // Check if the symbol has been implemented.
          topLevelScope.get(name) match {
            case N => topLevelScope.declareStubValue(name)
            case _ => ()
          }
          // Emit nothing for type declarations.
          N
        // try { res = <expr>; }
        // catch (e) { console.log(e); }
        case term: Term =>
          val body = translateTerm(term)(topLevelScope)
          S(topLevelScope.tempVars.emit() -> ((resultIdent := body) :: Nil))
      }

    // If this is the first time, insert the declaration of `res`.
    var prelude: Ls[JSStmt] = defStmts
    if (numRun === 0) {
      prelude = JSLetDecl(resultName -> N :: Nil) :: prelude
    }

    // Increase the run number.
    numRun = numRun + 1

    TestCode(
      SourceCode.fromStmts(polyfill.emit() ::: prelude).toLines,
      queries map { case (decls -> stmts) =>
        val prelude = decls match {
          case S(stmt) => stmt.toSourceCode.toLines
          case N       => Nil
        }
        val code = SourceCode.fromStmts(stmts).toLines
        Query(prelude, code)
      }
    )
  }
}

final case class Query(prelude: Ls[Str], code: Ls[Str])

final case class TestCode(prelude: Ls[Str], queries: Ls[Query])

object JSBackend {
  private def inspectTerm(t: Term): Str = t match {
    case Var(name)     => s"Var($name)"
    case Lam(lhs, rhs) => s"Lam(${inspectTerm(lhs)}, ${inspectTerm(rhs)})"
    case App(lhs, rhs) => s"App(${inspectTerm(lhs)}, ${inspectTerm(rhs)})"
    case Tup(fields) =>
      val entries = fields map {
        case (S(name), value) => s"$name: ${inspectTerm(value)}"
        case (N, value)       => s"_: ${inspectTerm(value)}"
      }
      s"Tup(${entries mkString ", "})"
    case Rcd(fields)                 => s"Rcd(...)"
    case Sel(receiver, fieldName)    => s"Sel(${inspectTerm(receiver)}, $fieldName)"
    case Let(isRec, name, rhs, body) => s"Let($isRec, $name)"
    case Blk(stmts)                  => s"Blk(...)"
    case Bra(rcd, trm)               => s"Bra(rcd = $rcd, ${inspectTerm(trm)})"
    case Asc(trm, ty)                => s"Asc(${inspectTerm(trm)}, $ty)"
    case Bind(lhs, rhs)              => s"Bind(...)"
    case Test(trm, ty)               => s"Test(...)"
    case With(trm, fields) =>
      s"With(${inspectTerm(trm)}, ${inspectTerm(fields)})"
    case CaseOf(trm, cases) =>
      def inspectCaseBranches(br: CaseBranches): Str = br match {
        case Case(clsNme, body, rest) =>
          s"Case($clsNme, ${inspectTerm(t)}, ${inspectCaseBranches(rest)})"
        case Wildcard(body) => s"Wildcard(${inspectTerm(body)})"
        case NoCases        => "NoCases"
      }
      s"CaseOf(${inspectTerm(trm)}, ${inspectCaseBranches(cases)}"
    case IntLit(value) => s"IntLit($value)"
    case DecLit(value) => s"DecLit($value)"
    case StrLit(value) => s"StrLit($value)"
  }

  // For integers larger than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER
  val MaximalSafeInteger: BigInt = BigInt("9007199254740991")

  // For integers less than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER
  val MinimalSafeInteger: BigInt = BigInt("-9007199254740991")

  def isSafeInteger(value: BigInt): Boolean =
    MinimalSafeInteger <= value && value <= MaximalSafeInteger
}
