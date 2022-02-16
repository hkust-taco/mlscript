package mlscript

import mlscript.utils._, shorthands._
import mlscript.codegen.Helpers._
import mlscript.codegen._

import scala.collection.immutable
import scala.util.matching.Regex

import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList
import scala.collection.mutable.ListBuffer

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
    case _: Lam | _: App | _: Sel | _: Let | _: Blk | _: Bind | _: Test | _: With | _: CaseOf | _: Subs =>
      throw CodeGenError(s"term ${inspect(t)} is not a valid pattern")
  }

  private def translateParams(t: Term): Ls[JSPattern] = t match {
    case Tup(params) => params map { case _ -> p => translatePattern(p) }
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
      case S(sym: ValueSymbol) => JSIdent(sym.runtimeName)
      case S(sym: ClassSymbol) =>
        if (isCallee)
          JSNew(JSIdent(sym.runtimeName))
        else
          JSArrowFn(JSNamePattern("x") :: Nil, L(JSNew(JSIdent(sym.runtimeName))(JSIdent("x"))))
      case S(sym: TraitSymbol) =>
        import JSCodeHelpers._
        // For now traits constructors do nothing (are identities):
        JSArrowFn(JSNamePattern("x") :: Nil, L(JSIdent("x")))
      case N => throw new CodeGenError(s"unresolved symbol ${name}")
    }

  // Returns: temp identifiers and the expression
  protected def translateTerm(term: Term)(implicit scope: Scope): JSExpr = term match {
    case Var(name) => translateVar(name, false)
    case Lam(params, body) =>
      val patterns = translateParams(params)
      val lamScope = Scope("Lam", patterns flatMap { _.bindings }, scope)
      JSArrowFn(patterns, lamScope.tempVars `with` translateTerm(body)(lamScope))
    case App(App(Var(op), Tup((N -> lhs) :: Nil)), Tup((N -> rhs) :: Nil))
        if JSBinary.operators contains op =>
      JSBinary(op, translateTerm(lhs), translateTerm(rhs))
    // Tenary expressions.
    case App(App(App(Var("if"), tst), con), alt) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    case App(trm, Tup(args)) =>
      val callee = trm match {
        case Var(nme) => translateVar(nme, true)
        case _ => translateTerm(trm)
      }
      callee(args map { case (_, arg) => translateTerm(arg) }: _*)
    case Rcd(fields) =>
      JSRecord(fields map { case (key, value) =>
        key.name -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSField(translateTerm(receiver), fieldName.name)
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
    case Subs(arr, idx) =>
      JSMember(translateTerm(arr), translateTerm(idx))
    case App(_, _) | _: Bind | _: Test =>
      throw CodeGenError(s"cannot generate code for term ${inspect(term)}")
  }

  private def translateCaseBranch(scrut: JSExpr, branch: CaseBranches)(implicit
      scope: Scope
  ): JSExpr = branch match {
    case Case(pat, body, rest) =>
      translateCase(scrut, pat)(translateTerm(body), translateCaseBranch(scrut, rest))
    case Wildcard(body) => translateTerm(body)
    case NoCases        => JSImmEvalFn(Nil, R(JSInvoke(
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
          JSBinary("==", scrut.member("constructor"), JSLit("Boolean"))
        case Var(s @ ("true" | "false")) =>
          JSBinary("==", scrut, JSLit(s))
        case Var("string") =>
          // JS is dumb so `instanceof String` won't actually work on "primitive" strings...
          JSBinary("==", scrut.member("constructor"), JSLit("String"))
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
  ): Type = body match {
    case Neg(ty) =>
      Neg(substitute(ty, subs))
    case AppliedType(TypeName(name), targs) =>
      topLevelScope.getType(name) match {
        case S(sym: ClassSymbol) => TypeName(name) // Note that here we erase the arguments.
        case S(sym: TraitSymbol) => ??? 
        case S(sym: TypeAliasSymbol) =>
          assert(targs.length === sym.params.length, targs -> sym.params)
          substitute(
            sym.actualType,
            collection.immutable.HashMap(
              sym.params zip targs map { case (k, v) => k -> v }: _*
            )
          )
        case N => throw new CodeGenError(s"$name is none of class, trait or type")
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
          topLevelScope.getType(name) match {
            case S(sym: ClassSymbol) => TypeName(name)
            case S(sym: TraitSymbol) => TypeName(name)
            case S(sym: TypeAliasSymbol) if sym.params.isEmpty => substitute(sym.actualType, subs)
            case S(sym: TypeAliasSymbol) => throw CodeGenError(
                s"type $name expects ${sym.params.length} type parameters but nothing provided"
            )
            case N => throw new CodeGenError(s"undeclared type name $name")
          }
        case S(ty) => ty
      }
    case Recursive(uv, ty) => Recursive(uv, substitute(ty, subs))
    case Rem(ty, fields)   => Rem(substitute(ty, subs), fields)
    case Bot | Top | _: Literal | _: TypeVar | _: Bounds | _: WithExtension | _: Arr => body
  }

  /**
    * Translate MLscript class declaration to JavaScript class declaration.
    * First, we will analyze its fields and base class name.
    * Then, we will check if the base class exists.
    */
  protected def translateClassDeclaration(
      classSymbol: ClassSymbol,
  )(implicit scope: Scope): JSClassDecl = {
    val members = classSymbol.methods.map { translateClassMember(_) }
    classSymbol.baseClass match {
      case N => JSClassDecl(classSymbol.runtimeName, classSymbol.fields.distinct, N, members)
      case S(baseClassSym) => baseClassSym.body match {
        case S(cls) => JSClassDecl(classSymbol.runtimeName, classSymbol.fields.distinct, S(cls), members)
        case N => throw new CodeGenError("base class translated after the derived class")
      }
    }
  }

  private def translateClassMember(
      method: MethodDef[Left[Term, Type]]
  )(implicit scope: Scope): JSClassMemberDecl = {
    val name = method.nme.name
    method.rhs.value match {
      case Lam(params, body) =>
        val methodParams = translateParams(params)
        val methodScope = scope.derive(s"Method $name", JSPattern.bindings(methodParams))
        methodScope.declareValue("this")
        JSClassMethod(name, methodParams, L(translateTerm(body)(methodScope)))
      case term =>
        val getterScope = scope.derive(s"Getter $name")
        getterScope.declareValue("this")
        JSClassGetter(name, L(translateTerm(term)(getterScope)))
    }
  }

  /**
    * Declare symbols for types, traits and classes.
    * Call this before the code generation.
    */
  protected def declareTypeDefs(typeDefs: Ls[TypeDef]): Ls[ClassSymbol] = {
    val classes = new ListBuffer[ClassSymbol]()
    typeDefs foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
        topLevelScope.declareTypeAlias(name, tparams map { _.name }, body)
      case TypeDef(Trt, TypeName(name), tparams, body, _, _) =>
        topLevelScope.declareTrait(name, tparams map { _.name }, body)
      case TypeDef(Cls, TypeName(name), tparams, baseType, _, members) =>
        classes += topLevelScope.declareClass(name, tparams map { _.name }, baseType, resolveClassFields(baseType), members)
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
        Bounds(_, _) | WithExtension(_, _) | Function(_, _) | Union(_, _) | _: Arr =>
      throw CodeGenError(s"unable to derive from type $ty")
  }

  /**
    * Find the base class for a specific class.
    */
  private def resolveClassBase(ty: Type): Opt[ClassSymbol] = {
    def resolveClassSymbol(name: Str): Opt[ClassSymbol] = topLevelScope.getType(name) match {
      case S(sym: ClassSymbol) => S(sym)
      case S(sym: TraitSymbol) => N // TODO: inherit from traits
      case S(sym: TypeAliasSymbol) =>
        throw new CodeGenError(s"cannot inherit from type alias $name")
      case N =>
        throw new CodeGenError(s"undeclared type name $name when resolving base classes")
    }
    def impl(ty: Type): Opt[ClassSymbol] = ty match {
      case Top | _: Record => N
      case TypeName(name) => resolveClassSymbol(name)
      case AppliedType(TypeName(name), _) => resolveClassSymbol(name)
      case Inter(ty1, ty2) => (resolveClassBase(ty1), resolveClassBase(ty2)) match {
        case (N, N) => N
        case (N, S(cls)) => S(cls)
        case (S(cls), N) => S(cls)
        case (S(cls1), S(cls2)) => if (cls1 === cls2)
          S(cls1)
        else
          throw CodeGenError(s"cannot have two base classes: ${cls1.lexicalName}, ${cls2.lexicalName}")
      }
      case Rem(_, _) | TypeVar(_, _) | Literal(_) | Recursive(_, _) | Bot | Top | Tuple(_) | Neg(_) |
          Bounds(_, _) | WithExtension(_, _) | Function(_, _) | Union(_, _) | _: Arr =>
        throw CodeGenError(s"cannot inherit from type $ty")
    }
    impl(ty)
  }

  /**
    * Resolve inheritance of all declared classes.
    */
  protected def resolveInheritance(classSymbols: Ls[ClassSymbol]): (Ls[ClassSymbol], Ls[ClassSymbol -> ClassSymbol]) = {
    val (noBase, relations) = classSymbols.partitionMap { derivedClass =>
      val baseClass = resolveClassBase(derivedClass.actualType)
      derivedClass.baseClass = baseClass
      baseClass.map(_ -> derivedClass).toRight(derivedClass)
    }
    val inRelations = Set.from(relations.iterator.flatMap { case (a, b) => a :: b :: Nil })
    (noBase.filterNot { inRelations.contains(_) }, relations)
  }

  protected def translateClassDeclarations(sortedClasses: Iterable[ClassSymbol]): Ls[JSClassDecl] = {
    sortedClasses.flatMap { sym =>
      sym.body match {
        case S(_) => N // Don't translate if done
        case N =>
          val body = translateClassDeclaration(sym)(topLevelScope)
          sym.body = S(body)
          S(body)
      }
    }.toList
  }
}

class JSWebBackend extends JSBackend {
  // Name of the array that contains execution results
  val resultsName: Str = topLevelScope declareRuntimeSymbol "results"

  val prettyPrinterName: Str = topLevelScope declareRuntimeSymbol "prettyPrint"

  polyfill.use("prettyPrint", prettyPrinterName)

  def apply(pgrm: Pgrm): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    val classSymbols = declareTypeDefs(typeDefs)
    val (isolatedClasses, relations) = resolveInheritance(classSymbols)
    val sortedClasses = try topologicallySort(relations) catch {
      case e: RuntimeException => throw CodeGenError("cyclic inheritance involving")
    }
    val defStmts = translateClassDeclarations(isolatedClasses ++ sortedClasses)

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
          case Def(recursive, Var(name), L(body)) =>
            val (translatedBody, sym) = if (recursive) {
              val sym = topLevelScope.declareValue(name)
              (translateTerm(body)(topLevelScope), sym)
            } else {
              val translatedBody = translateTerm(body)(topLevelScope)
              (translatedBody, topLevelScope.declareValue(name))
            }
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(resultsIdent("push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          // Ignore type declarations.
          case Def(_, _, R(_)) => Nil
          // `exprs.push(<expr>)`.
          case term: Term =>
            topLevelScope.tempVars `with` JSInvoke(
              resultsIdent("push"),
              translateTerm(term)(topLevelScope) :: Nil
            ).stmt :: Nil
        })
    val epilogue = resultsIdent.member("map")(JSIdent(prettyPrinterName)).`return` :: Nil
    JSImmEvalFn(Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines
  }
}

class JSTestBackend extends JSBackend {
  private val lastResultSymbol = topLevelScope declareValue "res"
  private val resultIdent = JSIdent(lastResultSymbol.runtimeName)

  private var numRun = 0

  /**
    * Generate a piece of code for test purpose. It can be invoked repeatedly.
    */
  def apply(pgrm: Pgrm, allowEscape: Bool): JSTestBackend.Result =
    try generate(pgrm)(topLevelScope, allowEscape) catch {
      case e: CodeGenError => JSTestBackend.IllFormedCode(e.getMessage())
      case e: UnimplementedError => JSTestBackend.Unimplemented(e.getMessage())
      case e: Throwable => JSTestBackend.UnexpectedCrash(e.getMessage())
    }

  /**
    * Generate JavaScript code which targets MLscript test from the given block.
    */
  private def generate(pgrm: Pgrm)(implicit scope: Scope, allowEscape: Bool): JSTestBackend.TestCode = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    val classSymbols = declareTypeDefs(typeDefs)
    val (isolatedClasses, relations) = resolveInheritance(classSymbols)
    val sortedClasses = try topologicallySort(relations) catch {
      case e: RuntimeException => throw CodeGenError("cyclic inheritance involving")
    }
    val defStmts = translateClassDeclarations(isolatedClasses ++ sortedClasses)

    val zeroWidthSpace = JSLit("\"\\u200B\"")
    val catchClause = JSCatchClause(
      JSIdent("e"),
      (zeroWidthSpace + JSIdent("e") + zeroWidthSpace).log() :: Nil
    )

    // Generate statements.
    val queries = otherStmts.map {
      case Def(recursive, Var(name), L(body)) =>
        (if (recursive) {
          val sym = scope.declareValue(name)
          try {
            R((translateTerm(body), sym))
          } catch {
            case e: UnimplementedError =>
              scope.stubize(sym, e.symbol)
              L(e.getMessage())
            case e: Throwable => throw e
          }
        } else {
          (try R(translateTerm(body)) catch {
            case e: UnimplementedError =>
              scope.declareStubValue(name, e.symbol)
              L(e.getMessage())
            case e: Throwable => throw e
          }) map { expr => (expr, scope.declareValue(name)) }
        }) match { 
          case R((expr, sym)) =>
            JSTestBackend.CodeQuery(
              scope.tempVars.emit(),
              ((JSIdent("globalThis").member(sym.runtimeName) := (expr match {
                case t: JSArrowFn => t.toFuncExpr(S(sym.runtimeName))
                case t            => t
              })) ::
                (resultIdent := JSIdent(sym.runtimeName)) ::
                Nil)
            )
          case L(reason) => JSTestBackend.AbortedQuery(reason)
        }
      case Def(_, Var(name), _) =>
        scope.declareStubValue(name)
        JSTestBackend.EmptyQuery
      case term: Term =>
        try {
          val body = translateTerm(term)(scope)
          JSTestBackend.CodeQuery(scope.tempVars.emit(), (resultIdent := body) :: Nil)
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
  final case class CodeQuery(prelude: Ls[Str], code: Ls[Str]) extends Query {
    
  }

  object CodeQuery {
    def apply(decls: Opt[JSLetDecl], stmts: Ls[JSStmt]): CodeQuery =
      CodeQuery(
        decls match {
          case S(stmt) => stmt.toSourceCode.toLines
          case N       => Nil
        },
        SourceCode.fromStmts(stmts).toLines
      )
  }

  /**
    * Represents the result of code generation.
    */
  abstract class Result

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
  final case class UnexpectedCrash(override val content: Str) extends ErrorMessage(content)

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
