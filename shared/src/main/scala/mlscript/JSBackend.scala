package mlscript

import mlscript.utils._, shorthands._
import scala.util.matching.Regex
import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList
import scala.collection.immutable

class JSBackend {
  // For integers larger than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER
  val MaximalSafeInteger: BigInt = BigInt("9007199254740991")

  // For integers less than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER
  val MinimalSafeInteger: BigInt = BigInt("-9007199254740991")

  // This object contains all classNames.
  val classNames: HashSet[Str] = HashSet()

  // Sometimes, identifiers declared by `let` use the same name as class names.
  // JavaScript does not allow this. So, we need to replace them.
  val letLhsAliasMap: HashMap[Str, Str] = HashMap()

  // I just realized `Statement` is unused.
  def translateStatement(stmt: DesugaredStatement): JSStmt = stmt match {
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
    case _: Lit => JSWildcardPattern()
    // Others are not supported yet.
    case _: Lam | _: App | _: Tup | _: Sel | _: Let | _: Blk | _: Bra | _: Bind | _: Test |
        _: With | _: CaseOf =>
      throw new Error(s"term $t is not a valid pattern")
  }

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

  def translateTerm(term: Term): JSExpr = term match {
    case Var(name) =>
      if (classNames.contains(name)) {
        letLhsAliasMap.get(name) match {
          case N        => JSIdent(name, true)
          case S(alias) => JSIdent(alias, false)
        }
      } else {
        JSIdent(name)
      }
    // TODO: need scope to track variables so that we can rename reserved words
    case Lam(lhs, rhs) =>
      JSArrowFn(translatePattern(lhs) :: Nil, translateTerm(rhs))
    // Binary expressions.
    case App(App(Var(name), left), right) if builtinFnOpMap contains name =>
      JSBinary(builtinFnOpMap(name), translateTerm(left), translateTerm(right))
    case App(App(Var(op), left), right) if binaryOps contains op =>
      JSBinary(op, translateTerm(left), translateTerm(right))
    // Tenary expressions.
    case App(App(App(Var("if"), tst), con), alt) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    // Function application.
    case App(lhs, rhs) => JSInvoke(translateTerm(lhs), translateTerm(rhs) :: Nil)
    case Rcd(fields) =>
      JSRecord(fields map { case (key, value) =>
        key.name -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSMember(translateTerm(receiver), fieldName.name)
    // Turn let into an IIFE.
    case Let(isRec, name, value, body) =>
      JSImmEvalFn(name :: Nil, Left(translateTerm(body)), translateTerm(value) :: Nil)
    case Blk(stmts) =>
      JSImmEvalFn(
        "" :: Nil,
        Right(stmts flatMap (_.desugared._2) map {
          translateStatement(_)
        }),
        JSPlaceholderExpr() :: Nil
      )
    case CaseOf(term, cases) => {
      val argument = translateTerm(term)
      val parameter = getTemporaryName("x")
      val body = translateCaseBranch(parameter, cases)
      JSImmEvalFn(parameter :: Nil, Right(body), argument :: Nil)
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
    case _: Tup | _: Bra | _: Bind | _: Test | _: With =>
      throw new Error(s"cannot generate code for term ${JSBackend.inspectTerm(term)}")
  }

  // Translate consecutive case branches into a list of if statements.
  def translateCaseBranch(name: Str, branch: CaseBranches): Ls[JSStmt] =
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
      case Recursive(uv, ty)                   => Recursive(uv, substitute(ty, subs))
      case Rem(ty, fields)                     => Rem(substitute(ty, subs), fields)
      case Bot | Top | _: Literal | _: TypeVar => body
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
  ): JSClassDecl = {
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
  ): JSClassMemberDecl = {
    val name = method.nme.name
    method.rhs.value match {
      case Lam(Var(param), rhs)         => JSClassMethod(name, param :: Nil, L(translateTerm(rhs)))
      case Lam(Asc(Var(param), _), rhs) => JSClassMethod(name, param :: Nil, L(translateTerm(rhs)))
      case term                         => JSClassGetter(name, L(translateTerm(term)))
    }
  }

  def apply(pgrm: Pgrm): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    // Collect type aliases into a map so we can normalize them.
    typeDefs foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _) =>
        val tnames = tparams map { case TypeName(nme) => nme }
        typeAliasMap(name) = tnames -> body
      case _ => ()
    }

    val defResultObjName = getTemporaryName("defs")
    val exprResultObjName = getTemporaryName("exprs")
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
                val cls = translateClassDeclaration(name, actualType, mthDefs)
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
            case Def(isRecursive, name, L(body)) =>
              val translatedBody = translateTerm(body)
              val tempName = getTemporaryName(name)
              if (tempName =/= name) {
                letLhsAliasMap += name -> tempName
              }
              //
              val shadowedName = resolveShadowName(tempName)
              if (shadowedName === tempName) {
                // Declare the name, assign and record the value.
                // ```
                // let <tempName> = <expr>;
                // defs.<name> = <tempName>;
                // ```
                JSLetDecl(tempName, translatedBody) ::
                  JSExprStmt(
                    JSAssignExpr(
                      JSMember(JSIdent(defResultObjName), name),
                      JSIdent(tempName)
                    )
                  ) :: Nil
              } else {
                // Re-assign and record the value as a new name:
                // ```
                // <tempName> = <expr>;
                // defs["<name>@<number of shadow>"] = <tempName>;
                // ```
                JSExprStmt(JSAssignExpr(JSIdent(tempName), translatedBody)) ::
                  JSExprStmt(
                    JSAssignExpr(
                      JSMember(JSIdent(defResultObjName), shadowedName),
                      JSIdent(tempName)
                    )
                  ) :: Nil
              }
            case Def(isRecursive, name, R(body)) => Nil
            case _: Term                         => Nil
          })
          // Generate something like `exprs.push(<expr>)`.
          .concat(otherStmts.zipWithIndex.collect { case (term: Term, index) =>
            JSExprStmt(
              JSInvoke(
                JSMember(JSIdent(exprResultObjName), "push"),
                translateTerm(term) :: Nil
              )
            )
          })
          .concat(
            JSReturnStmt(
              JSArray(
                JSIdent(defResultObjName) :: JSIdent(exprResultObjName) :: Nil
              )
            ) :: Nil
          )
    SourceCode.concat(stmts map { _.toSourceCode }).lines map { _.toString }
  }

  private def getTemporaryName(name: Str): Str = (name #:: LazyList
    .from(0)
    .map { name + _.toString }).dropWhile { classNames contains _ }.head
}

object JSBackend {
  private def inspectTerm(t: Term): Str = t match {
    case Var(name)                   => s"Var($name)"
    case Lam(lhs, rhs)               => s"Lam(${inspectTerm(lhs)}, ${inspectTerm(rhs)})"
    case App(lhs, rhs)               => s"App(${inspectTerm(lhs)}, ${inspectTerm(rhs)})"
    case Tup(fields)                 =>
      val entries = fields map {
        case (S(name), value) => s"$name: ${inspectTerm(value)}"
        case (N, value)       => s"_: ${inspectTerm(value)}"
      }
      s"Tup(${entries mkString ", "})"
    case Rcd(fields)                 => s"Rcd(...)"
    case Sel(receiver, fieldName)    => s"Sel(${inspectTerm(receiver)}, $fieldName)"
    case Let(isRec, name, rhs, body) => s"Let($isRec, $name)"
    case Blk(stmts)                  => s"Blk(...)"
    case Bra(rcd, trm)               => s"Bra(...)"
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
}
