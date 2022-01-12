package mlscript

import mlscript.utils._, shorthands._
import scala.util.matching.Regex
import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList
import scala.collection.immutable
import mlscript.codegen.{CodeGenError, Scope}

class JSBackend {
  // This object contains all classNames.
  protected val classNames: HashSet[Str] = HashSet()

  // TODO: let `Scope` track symbol kinds.
  protected val traitNames = HashSet[Str]()

  protected val topLevelScope = Scope()

  protected val polyfill = Polyfill()

  // Sometimes, identifiers declared by `let` use the same name as class names.
  // JavaScript does not allow this. So, we need to replace them.
  // The key is the name of the class, and the value is the name of the function.
  private val ctorAliasMap: HashMap[Str, Str] = HashMap()

  // I just realized `Statement` is unused.
  private def translateStatement(stmt: DesugaredStatement)(implicit scope: Scope): JSStmt =
    stmt match {
      case t: Term             => JSExprStmt(translateTerm(t))
      case _: Def | _: TypeDef => ??? // TODO
    }

  /** This function translates parameter destructions in `def` declarations.
    *
    * The production rules of MLscript `def` parameters are:
    *
    * subterm ::= "(" term ")" | record | literal | identifier term ::= let | fun | ite | withsAsc |
    * _match
    *
    * JavaScript supports following destruction patterns:
    *
    *   - Array patterns: `[x, y, ...]` where `x`, `y` are patterns.
    *   - Object patterns: `{x: y, z: w, ...}` where `z`, `w` are patterns.
    *   - Identifiers: an identifier binds the position to a name.
    *
    * This function only translate name patterns and object patterns. I was thinking if we can
    * support literal parameter matching by merging multiple function `def`s into one.
    *
    * @param t
    *   the term to translate
    * @return
    *   a `JSPattern` representing the pattern
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

  // For inheritance usage.
  protected val nameClsMap = collection.mutable.HashMap[Str, JSClassDecl]()

  // Returns: temp identifiers and the expression
  protected def translateTerm(term: Term)(implicit scope: Scope): JSExpr = term match {
    // TODO: when scope symbol is ready, udpate here
    case Var("error") => JSIdent("error")()
    case Var(mlsName) =>
      val (jsName, srcScope) = scope resolveWithScope mlsName
      // If it is a class name and the name is declared in the top-level scope.
      if ((classNames contains mlsName) && (srcScope exists { _.isTopLevel })) {
        // `mlsName === jsName` means no re-declaration, so it refers to the class.
        if (mlsName === jsName)
          JSArrowFn(JSNamePattern("x") :: Nil, L(JSIdent(jsName, true)(JSIdent("x"))))
        else
          JSIdent(jsName)
      } else {
        JSIdent(jsName)
      }
    // TODO: need scope to track variables so that we can rename reserved words
    case Lam(params, body) =>
      val patterns = translateParams(params)
      val lamScope = Scope(patterns flatMap { _.bindings }, scope)
      JSArrowFn(patterns, lamScope withTempVarDecls translateTerm(body)(lamScope))
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
    // Trait construction.
    // TODO: when scope symbol is ready, udpate here
    case App(Var(callee), Tup(N -> (trm: Term) :: Nil)) if (traitNames contains callee) =>
      translateTerm(trm)
    // TODO: when scope symbol is ready, remove the branch here
    case App(Var(mlsName), Tup(N -> (trm: Term) :: Nil)) =>
      val (jsName, srcScope) = scope resolveWithScope mlsName
      // If it is a class name and the name is declared in the top-level scope.
      (if ((classNames contains mlsName) && (srcScope exists { _.isTopLevel })) {
        // `mlsName === jsName` means no re-declaration, so it refers to the class.
        JSIdent(jsName, mlsName === jsName)
      } else {
        JSIdent(jsName)
      })((translateTerm(trm)))
    // Function application.
    case App(callee, Tup(args)) =>
      JSInvoke(translateTerm(callee), args map { case (_, arg) => translateTerm(arg) })
    case App(callee, arg) =>
      JSInvoke(translateTerm(callee), translateTerm(arg) :: Nil)
    case Rcd(fields) =>
      JSRecord(fields map { case (key, value) =>
        key.name -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSMember(translateTerm(receiver), fieldName.name)
    // Turn let into an IIFE.
    case Let(isRec, name, value, body) =>
      val letScope = Scope(name.name :: Nil, scope)
      JSImmEvalFn(
        name.name :: Nil,
        letScope withTempVarDecls translateTerm(body)(letScope),
        translateTerm(value)(letScope) :: Nil
      )
    case Blk(stmts) =>
      val blkScope = Scope(Nil, scope)
      JSImmEvalFn(
        Nil,
        R(blkScope withTempVarDecls (stmts flatMap (_.desugared._2) map {
          translateStatement(_)(blkScope)
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
        val name = JSIdent(scope.allocateTempVar())
        JSCommaExpr(JSAssignExpr(name, arg) :: translateCaseBranch(name, cases) :: Nil)
      }
    case IntLit(value) => JSLit(value.toString + (if (JSBackend isSafeInteger value) "" else "n"))
    case DecLit(value) => JSLit(value.toString)
    case StrLit(value) => JSLit(JSLit.makeStringLiteral(value))
    // `Asc(x, ty)` <== `x: Type`
    case Asc(trm, _) => translateTerm(trm)
    // `c with { x = "hi"; y = 2 }`
    case With(trm, Rcd(fields)) =>
      JSInvoke(
        JSIdent(polyfill get "withConstruct" match {
          case S(fnName) => fnName
          case N         => polyfill.use("withConstruct", topLevelScope allocateJavaScriptName "withConstruct")
        }),
        translateTerm(trm) :: JSRecord(fields map { case (Var(name), value) =>
          name -> translateTerm(value)
        }) :: Nil
      )
    case Bra(_, trm) => translateTerm(trm)
    case Tup(terms) =>
      JSArray(terms map { case (_, term) => translateTerm(term) })
    case _: Bind | _: Test =>
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

  protected val typeAliasMap =
    collection.mutable.HashMap[Str, Ls[Str] -> Type]()

  // This function normalizes something like `T[A, B]`.
  private def applyTypeAlias(name: Str, targs: Ls[Type]): Type =
    typeAliasMap get name match {
      case S(tparams -> body) =>
        assert(targs.length === tparams.length, targs -> tparams)
        substitute(
          body,
          collection.immutable.HashMap(
            tparams zip targs map { case (k, v) => k -> v }: _*
          )
        )
      case N =>
        if (classNames contains name) {
          // For classes with type parameters, we just erase the type parameters.
          TypeName(name)
        } else {
          throw CodeGenError(s"type $name is not defined")
        }
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
        applyTypeAlias(name, targs map { substitute(_, subs) })
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
            typeAliasMap get name match {
              case N              => TypeName(name)
              case S(Nil -> body) => substitute(body, subs)
              case S(tparams -> _) =>
                throw CodeGenError(
                  s"type $name expects ${tparams.length} type parameters but nothing provided"
                )
            }
          case S(ty) => ty
        }
      case Recursive(uv, ty) => Recursive(uv, substitute(ty, subs))
      case Rem(ty, fields)   => Rem(substitute(ty, subs), fields)
      case Bot | Top | _: Literal | _: TypeVar | _: Bounds | _: WithExtension => body
    }
  }

  // This function collects two things:
  // 1. fields from a series of intersection of records,
  // 2. name of the base class.
  // Only one base class is allowed.
  private def getBaseClassAndFields(ty: Type): (Ls[Str], Opt[Str]) = ty match {
    // `class A` ==> `class A {}`
    case Top => Nil -> N
    // `class A { <items> }` ==>
    // `class A { constructor(fields) { <items> } }`
    case Record(fields) => fields.map(_._1.name) -> N
    // `class B: A` ==> `class B extends A {}`
    // If `A` is a type alias, it is replaced by its real type.
    // Otherwise just use the name.
    case TypeName(name) =>
      if (traitNames contains name)
        Nil -> N
      else
        typeAliasMap get name match {
          // The base class is not a type alias.
          case N => Nil -> S(name)
          // The base class is a type alias with no parameters.
          // Good, just make sure all term is normalized.
          case S(Nil -> body) => getBaseClassAndFields(substitute(body))
          // The base class is a type alias with parameters.
          // Oops, we don't support this.
          case S(tparams -> _) =>
            throw CodeGenError(
              s"type $name expects ${tparams.length} type parameters but nothing provided"
            )
        }
    // `class C: { <items> } & A` ==>
    // `class C extends A { constructor(fields) { <items> } }`
    case Inter(Record(entries), ty) =>
      val (fields, cls) = getBaseClassAndFields(ty)
      entries.map(_._1.name) ++ fields -> cls
    // `class C: { <items> } & A` ==>
    // `class C extends A { constructor(fields) { <items> } }`
    case Inter(ty, Record(entries)) =>
      val (fields, cls) = getBaseClassAndFields(ty)
      fields ++ entries.map(_._1.name) -> cls
    // `class C: <X> & <Y>`: resolve X and Y respectively.
    case Inter(ty1, ty2) =>
      val (fields1, cls1) = getBaseClassAndFields(ty1)
      val (fields2, cls2) = getBaseClassAndFields(ty2)
      (cls1, cls2) match {
        case (N, N) =>
          fields1 ++ fields2 -> N
        case (N, S(cls)) =>
          fields1 ++ fields2 -> S(cls)
        case (S(cls), N) =>
          fields1 ++ fields2 -> S(cls)
        case (S(cls1), S(cls2)) =>
          if (cls1 === cls2) {
            fields1 ++ fields2 -> S(cls1)
          } else {
            throw CodeGenError(s"Cannot have two base classes: $cls1, $cls2")
          }
      }
    // `class C: F[X]` and (`F[X]` => `A`) ==> `class C extends A {}`
    // For applied types such as `Id[T]`, normalize them before translation.
    // Do not forget to normalize type arguments first.
    case AppliedType(TypeName(base), targs) =>
      if (traitNames contains base)
        Nil -> N
      else
        getBaseClassAndFields(applyTypeAlias(base, targs map { substitute(_) }))
    // There is some other possibilities such as `class Fun[A]: A -> A`.
    // But it is not achievable in JavaScript.
    case Rem(_, _) | TypeVar(_, _) | Literal(_) | Recursive(_, _) | Bot | Top | Tuple(_) | Neg(_) |
        Bounds(_, _) | WithExtension(_, _) | Function(_, _) | Union(_, _) =>
      throw CodeGenError(s"unable to derive from type $ty")
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
    getBaseClassAndFields(actualType) match {
      // Case 1: no base class, just fields.
      case fields -> N => JSClassDecl(name, fields.distinct, N, members)
      // Case 2: has a base class and fields.
      case fields -> S(clsNme) =>
        nameClsMap get clsNme match {
          case N      => throw CodeGenError(s"Class $clsNme is not defined.")
          case S(cls) => JSClassDecl(name, fields.distinct, S(cls), members)
        }
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
}

class JSWebBackend extends JSBackend {
  // This will be changed during code generation.
  private var hasWithConstruct = false

  // Name of the helper function for `with` construction.
  private val withConstructFnName = topLevelScope allocateJavaScriptName "withConstruct"

  // Name of the array that contains execution results
  val resultsName: Str = topLevelScope allocateJavaScriptName "results"

  // TODO: remove this when the prelude code manager is done
  val prettyPrinterName: Str = topLevelScope allocateJavaScriptName "prettyPrint"

  def apply(pgrm: Pgrm): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    // Collect type aliases into a map so we can normalize them.
    typeDefs foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
        val tnames = tparams map { case TypeName(nme) => nme }
        typeAliasMap(name) = tnames -> body
      case TypeDef(Trt, TypeName(name), _, _, _, _) =>
        traitNames += name
      case _ => ()
    }

    val resultsIdent = JSIdent(resultsName)
    val stmts: Ls[JSStmt] =
      JSConstDecl(resultsName, JSArray(Nil)) ::
        typeDefs
          .map { case TypeDef(kind, TypeName(name), typeParams, actualType, _, mthDefs) =>
            kind match {
              case Cls =>
                topLevelScope declare name
                classNames += name
                val cls = translateClassDeclaration(name, actualType, mthDefs)(topLevelScope)
                nameClsMap += name -> cls
                cls
              case Trt => JSComment(s"trait $name")
              case Als => JSComment(s"type alias $name")
            }
          }
          // Generate something like:
          // ```js
          // const <name> = <expr>;
          // <results>.push(<name>);
          // ```
          .concat(otherStmts.flatMap {
            case Def(_, mlsName, L(body)) =>
              val translatedBody = translateTerm(body)(topLevelScope)
              val jsName = topLevelScope declare mlsName.name
              topLevelScope withTempVarDecls JSConstDecl(jsName, translatedBody) ::
                JSInvoke(JSMember(resultsIdent, "push"), JSIdent(jsName) :: Nil).stmt :: Nil
            // Ignore type declarations.
            case Def(_, _, R(_)) => Nil
            // `exprs.push(<expr>)`.
            case term: Term =>
              topLevelScope withTempVarDecls JSInvoke(
                JSMember(resultsIdent, "push"),
                translateTerm(term)(topLevelScope) :: Nil
              ).stmt :: Nil
          })
    SourceCode
      .concat((polyfill.emit() ::: stmts) map { _.toSourceCode })
      .lines map { _.toString }
  }
}

class JSTestBackend extends JSBackend {
  private val resultName = topLevelScope allocateJavaScriptName "res"

  private var numRun = 0

  // TODO: make the return type more readable
  def apply(pgrm: Pgrm): (Str, Bool) \/ TestCode = try {
    R(generate(pgrm))
  } catch {
    case e: CodeGenError => L(e.getMessage() -> false) // Intended errors
    case e: Throwable => L(e.getMessage() -> true) // Unexpected crashes
  }

  // Generate code for test.
  private def generate(pgrm: Pgrm): TestCode = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    // TODO: insert them via the prelude manager.
    lazy val preludeFuncs =
      JSBackend.makeIdentity(topLevelScope allocateJavaScriptName "id") ::
        JSBackend.makeError(topLevelScope allocateJavaScriptName "error") ::
        JSBackend.makeSuccessor(topLevelScope allocateJavaScriptName "succ") ::
        JSBackend.makeBinaryFunc(topLevelScope allocateJavaScriptName "concat", "+") ::
        JSBackend.makeBinaryFunc(topLevelScope allocateJavaScriptName "add", "+") ::
        JSBackend.makeBinaryFunc(topLevelScope allocateJavaScriptName "sub", "-") ::
        JSBackend.makeBinaryFunc(topLevelScope allocateJavaScriptName "mul", "*") ::
        JSBackend.makeBinaryFunc(topLevelScope allocateJavaScriptName "div", "/") ::
        JSBackend.makeBinaryFunc(topLevelScope allocateJavaScriptName "gt", ">") ::
        JSBackend.makeUnaryFunc(topLevelScope allocateJavaScriptName "not", "!") ::
        Nil

    // Collect type aliases into a map so we can normalize them.
    typeDefs foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
        val tnames = tparams map { case TypeName(nme) => nme }
        typeAliasMap(name) = tnames -> body
      case TypeDef(Trt, TypeName(name), _, _, _, _) =>
        traitNames += name
      case _ => ()
    }

    val resultIdent = JSIdent(resultName)

    // Generate hoisted declarations.
    val defStmts = typeDefs
      .flatMap { case TypeDef(kind, TypeName(name), typeParams, actualType, _, mthDefs) =>
        kind match {
          case Cls =>
            topLevelScope declare name
            classNames += name
            val cls = translateClassDeclaration(name, actualType, mthDefs)(topLevelScope)
            nameClsMap += name -> cls
            S(cls)
          case Trt => N
          case Als => N
        }
      }

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
        case Def(_, mlsName, L(body)) =>
          val translatedBody = translateTerm(body)(topLevelScope)
          val jsName = topLevelScope declare mlsName.name
          S(
            topLevelScope.emitTempVarDecls() ->
             ((JSIdent("globalThis").member(jsName) := (translatedBody match {
                case t: JSArrowFn => t.toFuncExpr(S(jsName))
                case t            => t
              })) ::
                (resultIdent := JSIdent(jsName)) ::
                Nil)
          )
        // Ignore type declarations.
        case Def(_, _, R(_)) => N
        // try { res = <expr>; }
        // catch (e) { console.log(e); }
        case term: Term =>
          val body = translateTerm(term)(topLevelScope)
          S(topLevelScope.emitTempVarDecls() -> ((resultIdent := body) :: Nil))
      }

    // If this is the first time, insert the declaration of `res`.
    var prelude: Ls[JSStmt] = defStmts
    if (numRun === 0) {
      prelude = preludeFuncs ::: (JSLetDecl(resultName -> N :: Nil) :: prelude)
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

  /** 
    * This function makes the following function.
    *
    * ```js
    * function withConstruct(target, fields) {
    *   if (typeof target === "string" || typeof target === "number") {
    *     return Object.assign(target, fields);
    *   }
    *   if (target instanceof String || target instanceof Number) {
    *     return Object.assign(target.valueOf(), target, fields);
    *   }
    *   const copy = Object.assign({}, target, fields);
    *   Object.setPrototypeOf(copy, Object.getPrototypeOf(target));
    *   return copy;
    * }
    * ```
    */
  def makeWithConstructDecl(name: Str): JSFuncDecl = {
    val obj = JSIdent("Object")
    val tgt = JSIdent("target")
    val body: Ls[JSStmt] = JSIfStmt(
      (tgt.typeof() :=== JSExpr("string")) :|| (tgt.typeof() :=== JSExpr("number")) :||
        (tgt.typeof() :=== JSExpr("boolean")) :|| (tgt.typeof() :=== JSExpr("bigint")) :||
        (tgt.typeof() :=== JSExpr("symbol")),
      obj("assign")(tgt, JSIdent("fields")).`return` :: Nil,
    ) :: JSIfStmt(
      tgt.instanceOf(JSIdent("String")) :|| tgt.instanceOf(JSIdent("Number")) :||
        tgt.instanceOf(JSIdent("Boolean")) :|| tgt.instanceOf(JSIdent("BigInt")),
      obj("assign")(tgt("valueOf")(), tgt, JSIdent("fields")).`return` :: Nil,
    ) :: JSConstDecl("copy", obj("assign")(JSRecord(Nil), tgt, JSIdent("fields"))) ::
      obj("setPrototypeOf")(JSIdent("copy"), obj("getPrototypeOf")(tgt)).stmt ::
      JSIdent("copy").`return` ::
      Nil
    JSFuncDecl(
      name,
      JSNamePattern("target") :: JSNamePattern("fields") :: Nil,
      body
    )
  }

  private def makePrettyPrinter(name: Str, indent: Bool) = {
    val arg = JSIdent("value")
    val default = arg.member("constructor").member("name") + JSExpr(" ") +
      (if (indent) JSIdent("JSON").member("stringify")(arg, JSIdent("undefined"), JSIdent("2"))
       else JSIdent("JSON").member("stringify")(arg));
    JSFuncDecl(
      name,
      JSNamePattern("value") :: Nil,
      JSIdent(name)
        .typeof()
        .switch(
          default.`return` :: Nil,
          JSExpr("number") -> Nil,
          JSExpr("boolean") -> Nil,
          // Returns `"[Function: <name>]"`
          JSExpr("function") -> {
            val name = arg.member("name") ?? JSExpr("<anonymous>")
            val repr = JSExpr("[Function: ") + name + JSExpr("]")
            (repr.`return` :: Nil)
          },
          JSExpr("string") -> ((JSExpr("\"") + arg + JSExpr("\"")).`return` :: Nil)
        ) :: Nil,
    )
  }

  def makeIdentity(name: Str): JSFuncDecl =
    JSFuncDecl(name, JSNamePattern("x") :: Nil, JSIdent("x").`return` :: Nil)

  def makeSuccessor(name: Str): JSFuncDecl =
    JSFuncDecl(name, JSNamePattern("x") :: Nil, (JSIdent("x") + JSLit("1")).`return` :: Nil)

  def makeBinaryFunc(name: Str, op: Str): JSFuncDecl =
    JSFuncDecl(
      name,
      JSNamePattern("x") :: JSNamePattern("y") :: Nil,
      JSIfStmt(
        JSIdent("arguments").member("length") :=== JSLit("2"),
        (JSIdent("x").binary(op, JSIdent("y"))).`return` :: Nil,
        JSArrowFn(
          JSNamePattern("y") :: Nil,
          L(JSIdent("x").binary(op, JSIdent("y")))
        ).`return` :: Nil
      ) :: Nil
    )

  def makeUnaryFunc(name: Str, op: Str): JSFuncDecl =
    JSFuncDecl(
      name,
      JSNamePattern("x") :: Nil,
      (JSIdent("x").unary(op)).`return` :: Nil
    )

  def makeError(name: Str): JSFuncDecl = JSFuncDecl(
    name,
    Nil,
    JSInvoke(
      JSIdent("Error", true),
      JSExpr("unexpected runtime error") :: Nil
    ).`throw` :: Nil
  )

  // For integers larger than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER
  val MaximalSafeInteger: BigInt = BigInt("9007199254740991")

  // For integers less than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER
  val MinimalSafeInteger: BigInt = BigInt("-9007199254740991")

  def isSafeInteger(value: BigInt): Boolean =
    MinimalSafeInteger <= value && value <= MaximalSafeInteger
}
