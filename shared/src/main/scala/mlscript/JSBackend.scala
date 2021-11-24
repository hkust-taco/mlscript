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

  // This returns (codeFragment, declaredVariables)
  def translateLetPattern(t: Term): Str -> Ls[Str] = t match {
    // fun x -> ... ==> function (x) { ... }
    // should returns ("x", ["x"])
    case Var(name) => name -> Ls(name)
    // fun { x, y } -> ... ==> function ({ x, y }) { ... }
    // should returns ("{ x, y }", ["x", "y"])
    case Rcd(fields) => {
      // $ means an insertion point
      fields.foldLeft[Str -> Ls[Str]]("{ $ }" -> List.empty) {
        case ((code, names), (key, value)) =>
          value match {
            case Var(_) => code.replace("$", s"$key, ") -> (names :+ key)
            case rcd: Rcd => {
              val (subCode, subNames) = translateLetPattern(rcd)
              code.replace("$", s"$key: ${subCode}, ") -> (names ++ subNames)
            }
            // Is there any other cases?
            case _ => ???
          }
      }
    }
    // `fun x y -> ...` => `App(Var(x), Var(y))`
    case App(init, Var(last)) =>
      val (code, vars) = translateLetPattern(init)
      s"$code, $last" -> (vars ::: List(last))
    case _ =>
      println(
        s"unreachable case at translateLetPattern: ${JSBackend.inspectTerm(t)}"
      )
      ???
  }

  private def builtinFnOpMap =
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
    // TODO: need scope to track variables
    // so that we can rename reserved words
    case Lam(lhs, rhs) =>
      val (paramCode, declaredVars) = translateLetPattern(lhs)
      JSArrowFn(paramCode, translateTerm(rhs))
    // Binary expressions.
    case App(App(Var(name), left), right) if builtinFnOpMap contains name =>
      JSBinary(
        builtinFnOpMap(name),
        translateTerm(left),
        translateTerm(right)
      )
    // Tenary expressions.
    case App(App(App(Var("if"), tst), con), alt) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    // Function application.
    case App(lhs, rhs) => JSInvoke(translateTerm(lhs), translateTerm(rhs))
    case Rcd(fields) =>
      JSRecord(fields map { case (key, value) =>
        key -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSMember(translateTerm(receiver), fieldName)
    // Turn let into an IIFE.
    case Let(isRec, name, value, body) =>
      JSImmEvalFn(name, Left(translateTerm(body)), translateTerm(value))
    case Blk(stmts) =>
      JSImmEvalFn(
        "",
        Right(stmts flatMap (_.desugared._2) map {
          translateStatement(_)
        }),
        new JSPlaceholderExpr()
      )
    case CaseOf(term, cases) => {
      val argument = translateTerm(term)
      val parameter = getTemporaryName("x")
      val body = translateCaseBranch(parameter, cases)
      JSImmEvalFn(parameter, Right(body), argument)
    }
    case IntLit(value) => {
      val useBigInt = MinimalSafeInteger <= value && value <= MaximalSafeInteger
      JSLit(if (useBigInt) { value.toString }
      else { value.toString + "n" })
    }
    case DecLit(value) => JSLit(value.toString)
    case StrLit(value) => JSLit(JSLit.makeStringLiteral(value))
    case _             => ???
  }

  // Translate consecutive case branches into a list of if statements.
  def translateCaseBranch(name: Str, branch: CaseBranches): Ls[JSStmt] =
    branch match {
      case Case(className, body, rest) =>
        val scrut = JSIdent(name)
        JSIfStmt(
          className match {
            case Var("int") =>
              JSInvoke(JSMember(JSIdent("Number"), "isInteger"), scrut)
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

  // This function evaluates something like `T[A, B]`.
  private def applyTypeAlias(name: Str, targs: Ls[Type]): Type =
    typeAliasMap get name match {
      case S(tparams -> body) =>
        if (targs.length === tparams.length) {
          val subs = collection.immutable.HashMap(
            tparams zip targs map { case (k, v) => k -> v }: _*
          )
          substitute(body, subs)
        } else {
          throw new Error(
            s"expect ${tparams.length} arguments but provided ${targs.length}"
          )
        }
      case N => throw new Error(s"type $name is not defined")
    }

  // This function evaluates a type, removing all `AppliedType`s.
  private def substitute(
      body: Type,
      subs: collection.immutable.HashMap[Str, Type] =
        collection.immutable.HashMap.empty
  ): Type = {
    body match {
      case Neg(ty) =>
        Neg(substitute(ty, subs))
      // Question: substitute arguments or the result?
      case AppliedType(Primitive(name), targs) =>
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
      case Primitive(name) =>
        subs get name match {
          case N =>
            typeAliasMap get name match {
              case N              => Primitive(name)
              case S(Nil -> body) => substitute(body, subs)
              case S(tparams -> _) =>
                throw new Error(
                  s"type $name expects ${tparams.length} type parameters but nothing provided"
                )
            }
          case S(ty) => ty
        }
      // For `Bot`, `Literal`, and `Top`, we don't need to substitute.
      case _ => body
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
    case Record(fields) => fields.map(_._1) -> N
    // `class B: A` ==> `class B extends A {}`
    // If `A` is a type alias, it is replaced by its real type.
    // Otherwise just use the name.
    case Primitive(name) =>
      typeAliasMap get name match {
        // The base class is not a type alias.
        case N => Nil -> S(name)
        // The base class is a type alias with no parameters.
        // Good, just make sure all term is evaluated.
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
      entries.map(_._1) ++ fields -> cls
    // `class C: { <items> } & A` ==>
    // `class C extends A { constructor(fields) { <items> } }`
    case Inter(ty, Record(entries)) =>
      val (fields, cls) = getBaseClassAndFields(ty)
      fields ++ entries.map(_._1) -> cls
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
    // For applied types such as `Id[T]`, evaluate them before translation.
    // Do not forget to evaluate type arguments first.
    case AppliedType(Primitive(base), targs) =>
      getBaseClassAndFields(applyTypeAlias(base, targs map { substitute(_) }))
    // There is some other possibilities such as `class Fun[A]: A -> A`.
    // But it is not achievable in JavaScript.
    case _ => ???
  }

  // Translate MLscript class declaration to JavaScript class declaration.
  // First, we will analyze its fields and base class name.
  // Then, we will check if the base class exists.
  def translateClassDeclaration(name: Str, actualType: Type): JSClassDecl = {
    getBaseClassAndFields(actualType) match {
      // Case 1: no base class, just fields.
      case fields -> N => JSClassDecl(name, fields.distinct, N)
      // Case 2: has a base class and fields.
      case fields -> S(clsNme) =>
        nameClsMap get clsNme match {
          case N      => throw new Error(s"Class $clsNme is not defined.")
          case S(cls) => JSClassDecl(name, fields.distinct, S(cls))
        }
    }
  }

  def apply(pgrm: Pgrm): Ls[Str] = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    // Collect type aliases into a map so we can evaluate them.
    typeDefs foreach {
      case TypeDef(Als, Primitive(name), tparams, body) =>
        val tnames = tparams map { case Primitive(nme) => nme }
        typeAliasMap(name) = tnames -> body
      case _ => ()
    }

    val defResultObjName = getTemporaryName("defs")
    val exprResultObjName = getTemporaryName("exprs")
    val stmts: Ls[JSStmt] =
      JSConstDecl(defResultObjName, JSRecord(Nil)) ::
        JSConstDecl(exprResultObjName, JSArray(Nil)) ::
        typeDefs
          .map { case TypeDef(kind, Primitive(name), typeParams, actualType) =>
            kind match {
              case Cls =>
                classNames += name
                val cls = translateClassDeclaration(name, actualType)
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
              JSConstDecl(tempName, translatedBody) ::
                JSExprStmt(
                  JSAssignExpr(
                    JSMember(JSIdent(defResultObjName), name),
                    JSIdent(tempName)
                  )
                ) :: Nil
            case Def(isRecursive, name, R(body)) => Nil
            case _: Term                         => Nil
          })
          // Generate something like `exprs.push(<expr>)`.
          .concat(otherStmts.zipWithIndex.collect { case (term: Term, index) =>
            JSExprStmt(
              JSInvoke(
                JSMember(JSIdent(exprResultObjName), "push"),
                translateTerm(term)
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
    case Var(name)     => s"Var($name)"
    case Lam(lhs, rhs) => s"Lam(${inspectTerm(lhs)}, ${inspectTerm(rhs)})"
    case App(lhs, rhs) => s"App(${inspectTerm(lhs)}, ${inspectTerm(rhs)})"
    case Tup(fields)   => s"Tup(...)"
    case Rcd(fields)   => s"Rcd(...)"
    case Sel(receiver, fieldName)    => s"Sel()"
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
