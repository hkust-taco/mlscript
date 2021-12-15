package mlscript

import mlscript.utils._, shorthands._
import scala.util.matching.Regex
import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList
import scala.collection.immutable
import mlscript.codegen.Scope

class JSBackend(pgrm: Pgrm) {
  // For integers larger than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER
  val MaximalSafeInteger: BigInt = BigInt("9007199254740991")

  // For integers less than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER
  val MinimalSafeInteger: BigInt = BigInt("-9007199254740991")

  // This object contains all classNames.
  val classNames: HashSet[Str] = HashSet()

  // All names used in `def`s.
  val defNames: HashSet[Str] = HashSet.from(pgrm.desugared._2._2 flatMap {
    case Def(rec, nme, rhs) => S(nme)
    case _                  => N
  })

  private val topLevelScope = Scope(defNames.toSeq)

  // Sometimes, identifiers declared by `let` use the same name as class names.
  // JavaScript does not allow this. So, we need to replace them.
  // The key is the name of the class, and the value is the name of the function.
  private val ctorAliasMap: HashMap[Str, Str] = HashMap()

  // I just realized `Statement` is unused.
  def translateStatement(stmt: DesugaredStatement)(implicit scope: Scope): JSStmt = stmt match {
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
  def translatePattern(t: Term): JSPattern = t match {
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
    // Others are not supported yet.
    case _: Lam | _: App | _: Tup | _: Sel | _: Let | _: Blk | _: Bind | _: Test | _: With |
        _: CaseOf =>
      throw new Error(s"term ${JSBackend.inspectTerm(t)} is not a valid pattern")
  }

  def translateParams(t: Term): Ls[JSPattern] = t match {
    case Tup(params) => params map { case _ -> p => translatePattern(p) }
    case _ => throw new Error(s"term $t is not a valid parameter list")
  }

  // This will be changed during code generation.
  private var hasWithConstruct = false

  // Name of the helper function for `with` construction.
  private val withConstructFnName = topLevelScope allocate "withConstruct"

  private val builtinFnOpMap =
    immutable.HashMap(
      "add" -> "+",
      "sub" -> "-",
      "mul" -> "*",
      "div" -> "/",
      "lt" -> "<",
      "le" -> "<=",
      "gt" -> ">",
      "ge" -> ">=",
      "eq" -> "==",
      "ne" -> "!=",
    )

  private val binaryOps = Set.from(builtinFnOpMap.values.concat("&&" :: "||" :: Nil))

  private val nameClsMap = collection.mutable.HashMap[Str, JSClassDecl]()

  def translateTerm(term: Term)(implicit scope: Scope): JSExpr = term match {
    case Var(name) =>
      if (classNames.contains(name)) {
        ctorAliasMap.get(name) match {
          case N        => JSIdent(name, true)
          case S(alias) => JSIdent(alias, false)
        }
      } else {
        JSIdent(name)
      }
    // TODO: need scope to track variables so that we can rename reserved words
    case Lam(params, body) =>
      val patterns = translateParams(params)
      val lamScope = Scope(patterns flatMap { _.bindings }, scope)
      JSArrowFn(patterns, translateTerm(body)(lamScope))
    // Binary expressions called by function names.
    case App(App(Var(name), Tup((N -> lhs) :: Nil)), Tup((N -> rhs) :: Nil))
        if builtinFnOpMap contains name =>
      JSBinary(builtinFnOpMap(name), translateTerm(lhs), translateTerm(rhs))
    // Binary expressions called by operators.
    case App(App(Var(op), Tup((N -> lhs) :: Nil)), Tup((N -> rhs) :: Nil))
        if binaryOps contains op =>
      JSBinary(op, translateTerm(lhs), translateTerm(rhs))
    // Tenary expressions.
    case App(App(App(Var("if"), tst), con), alt) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
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
      val letScope = Scope(name :: Nil, scope)
      JSImmEvalFn(
        name :: Nil,
        Left(translateTerm(body)(letScope)),
        translateTerm(value)(letScope) :: Nil
      )
    case Blk(stmts) =>
      JSImmEvalFn(
        Nil,
        Right(stmts flatMap (_.desugared._2) map { translateStatement(_) }),
        JSPlaceholderExpr() :: Nil
      )
    case CaseOf(term, cases) => {
      val arg = translateTerm(term)
      val param = scope.allocate()
      JSImmEvalFn(
        param :: Nil,
        Right(translateCaseBranch(param, cases)(Scope(param :: Nil, scope))),
        arg :: Nil
      )
    }
    case IntLit(value) => {
      val useBigInt = MinimalSafeInteger <= value && value <= MaximalSafeInteger
      JSLit(if (useBigInt) { value.toString }
      else { value.toString + "n" })
    }
    case DecLit(value) => JSLit(value.toString)
    case StrLit(value) => JSLit(JSLit.makeStringLiteral(value))
    // `Asc(x, ty)` <== `x: Type`
    case Asc(trm, _) => translateTerm(trm)
    // `c with { x = "hi"; y = 2 }`
    case With(trm, Rcd(fields)) =>
      hasWithConstruct = true
      JSInvoke(
        JSIdent(withConstructFnName),
        translateTerm(trm) :: JSRecord(fields map { case (Var(name), value) =>
          name -> translateTerm(value)
        }) :: Nil
      )
    case Bra(_, trm) => translateTerm(trm)
    case _: Tup | _: Bind | _: Test =>
      throw new Error(s"cannot generate code for term ${JSBackend.inspectTerm(term)}")
  }

  // Translate consecutive case branches into a list of if statements.
  def translateCaseBranch(name: Str, branch: CaseBranches)(implicit scope: Scope): Ls[JSStmt] =
    branch match {
      case Case(className, body, rest) =>
        val scrut = JSIdent(name)
        JSIfStmt(
          className match {
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
          Ls(JSReturnStmt(translateTerm(body)))
        ) :: translateCaseBranch(name, rest)
      case Wildcard(body) => Ls(JSReturnStmt(translateTerm(body)))
      case NoCases        => Ls(JSThrowStmt())
    }

  private val typeAliasMap =
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
          throw new Error(s"type $name is not defined")
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
                throw new Error(
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
      typeAliasMap get name match {
        // The base class is not a type alias.
        case N => Nil -> S(name)
        // The base class is a type alias with no parameters.
        // Good, just make sure all term is normalized.
        case S(Nil -> body) => getBaseClassAndFields(substitute(body))
        // The base class is a type alias with parameters.
        // Oops, we don't support this.
        case S(tparams -> _) =>
          throw new Error(
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
            throw new Exception(s"Cannot have two base classes: $cls1, $cls2")
          }
      }
    // `class C: F[X]` and (`F[X]` => `A`) ==> `class C extends A {}`
    // For applied types such as `Id[T]`, normalize them before translation.
    // Do not forget to normalize type arguments first.
    case AppliedType(TypeName(base), targs) =>
      getBaseClassAndFields(applyTypeAlias(base, targs map { substitute(_) }))
    // There is some other possibilities such as `class Fun[A]: A -> A`.
    // But it is not achievable in JavaScript.
    case _ => ???
  }

  // Translate MLscript class declaration to JavaScript class declaration.
  // First, we will analyze its fields and base class name.
  // Then, we will check if the base class exists.
  def translateClassDeclaration(
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
          case N      => throw new Error(s"Class $clsNme is not defined.")
          case S(cls) => JSClassDecl(name, fields.distinct, S(cls), members)
        }
    }
  }

  def translateClassMember(
      method: MethodDef[Left[Term, Type]]
  )(implicit scope: Scope): JSClassMemberDecl = {
    val name = method.nme.name
    method.rhs.value match {
      case Lam(params, body) =>
        JSClassMethod(name, translateParams(params), L(translateTerm(body)))
      case term => JSClassGetter(name, L(translateTerm(term)))
    }
  }

  def apply(): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    // Collect type aliases into a map so we can normalize them.
    typeDefs foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
        val tnames = tparams map { case TypeName(nme) => nme }
        typeAliasMap(name) = tnames -> body
      case _ => ()
    }

    val defResultObjName = topLevelScope allocate "defs"
    val exprResultObjName = topLevelScope allocate "exprs"
    // This hash map counts how many times a name has been used.
    val resolveShadowName = new ShadowNameResolver
    val stmts: Ls[JSStmt] =
      JSConstDecl(defResultObjName, JSRecord(Nil)) ::
        JSConstDecl(exprResultObjName, JSArray(Nil)) ::
        typeDefs
          .map { case TypeDef(kind, TypeName(name), typeParams, actualType, _, mthDefs) =>
            kind match {
              case Cls =>
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
          // const name = <expr>;
          // defs.name = name;
          // ```
          .concat(otherStmts.flatMap {
            case Def(isRecursive, originalName, L(body)) =>
              val translatedBody = translateTerm(body)(topLevelScope)
              // `declName` menas the name used in the declaration.
              // We allow define functions with the same name as classes.
              // Get a name that not conflicts with class names.
              val declName = if (classNames contains originalName) {
                val alias = topLevelScope allocate originalName
                ctorAliasMap += originalName -> alias
                alias
              } else {
                originalName
              }
              // We need to save a snapshot after each computation.
              // The snapshot name will be same as the original name, or in the
              // format of `originalName@n` if the original name is used.
              val snapshotName = resolveShadowName(originalName)
              (if (snapshotName === originalName) {
                 // First time: `let <declName> = <expr>;`
                 JSLetDecl(declName, translatedBody)
               } else {
                 // Not first time: `<declName> = <expr>;`
                 JSExprStmt(JSAssignExpr(JSIdent(declName), translatedBody))
               }) :: // Save the value: `defs.<snapshotName> = <declName>;`
                JSExprStmt(
                  JSAssignExpr(
                    JSMember(JSIdent(defResultObjName), snapshotName),
                    JSIdent(declName)
                  )
                ) :: Nil
            // Ignore type declarations.
            case Def(isRecursive, name, R(body)) => Nil
            // `exprs.push(<expr>)`.
            case term: Term =>
              JSExprStmt(
                JSInvoke(
                  JSMember(JSIdent(exprResultObjName), "push"),
                  translateTerm(term)(topLevelScope) :: Nil
                )
              ) :: Nil
          })
          .concat(
            JSReturnStmt(
              JSArray(
                JSIdent(defResultObjName) :: JSIdent(exprResultObjName) :: Nil
              )
            ) :: Nil
          )

    SourceCode
      .concat(
        (if (hasWithConstruct) {
           JSBackend.makeWithConstructDecl(withConstructFnName) :: stmts
         } else { stmts }) map { _.toSourceCode }
      )
      .lines map { _.toString }
  }
}

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
    *   const copy = Object.assign({}, target, fields);
    *   Object.setPrototypeOf(copy, Object.getPrototypeOf(target));
    *   return copy;
    * }
    * ```
    */
  private def makeWithConstructDecl(name: Str) = JSFuncDecl(
    name,
    JSNamePattern("target") :: JSNamePattern("fields") :: Nil,
    JSConstDecl(
      "copy",
      JSInvoke(
        JSMember(JSIdent("Object"), "assign"),
        JSRecord(Nil) :: JSIdent("target") :: JSIdent("fields") :: Nil
      )
    ) :: JSInvoke(
      JSMember(JSIdent("Object"), "setPrototypeOf"),
      JSIdent("copy") ::
        JSInvoke(JSMember(JSIdent("Object"), "getPrototypeOf"), JSIdent("target") :: Nil) :: Nil
    ).stmt :: JSReturnStmt(JSIdent("copy")) :: Nil
  )
}
