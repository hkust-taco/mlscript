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

  // TODO: add field definitions
  def translateClassDeclaration(name: Str, actualType: Type): JSClassDecl =
    actualType match {
      // `class A` ==> `class A {}`
      case Top => JSClassDecl(name, Nil)
      // `class A { <items> }` ==> `class A { constructor(fields) { <items> } }`
      case Record(fields) => JSClassDecl(name, fields map { _._1 })
      // `class B: A` ==> `class B extends A {}`
      case Primitive(clsName) =>
        nameClsMap get clsName match {
          case N      => ???
          case S(cls) => JSClassDecl(name, Nil, S(cls))
        }
      // I noticed `class Fun[A]: A -> A` is okay.
      // But I have no idea about how to do it.
      case _ => ???
    }

  def apply(pgrm: Pgrm): Ls[Str] = {

    val (diags, (typeDefs, otherStmts)) = pgrm.desugared
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
              case Trt => JSComment(s"// trait $name")
              case Als => JSComment(s"// type alias $name")
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
    case With(trm, fieldNme, fieldVal) =>
      s"With(${inspectTerm(trm)}, $fieldNme, ${inspectTerm(fieldVal)})"
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
