package mlscript

import mlscript.utils._, shorthands._
import scala.util.matching.Regex
import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList
import scala.collection.immutable

// TODO: should I turn this into a class?
// Becasue type information for each run is local.
// Otherwise I could clear for each `apply`.
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
  def translateStatement(stmt: Statement): JSStmt = stmt match {
    case LetS(isRec, pat, rhs) => {
      var (code, ids) = translateLetPattern(pat)
      new JSLetDecl(code, translateTerm(rhs))
    }
    case _ => ???
  }

  // This returns (codeFragment, declaredVariables)
  def translateLetPattern(t: Term): Str -> Ls[Str] = t match {
    // f x ==> function (x) { }
    // should returns ("x", ["x"])
    case Var(name) => name -> Ls(name)
    // f { x, y } ==> function ({ x, y }) { }
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
    // `def f x y` => `App(Var(x), Var(y))`
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
    immutable.HashMap("add" -> "+", "sub" -> "-", "mul" -> "*", "div" -> "/")

  def translateTerm(term: Term): JSExpr = term match {
    case Var(name) =>
      if (classNames.contains(name)) {
        letLhsAliasMap.get(name) match {
          case N        => new JSIdent(name, true)
          case S(alias) => new JSIdent(alias, false)
        }
      } else {
        new JSIdent(name)
      }
    // TODO: need scope to track variables
    // so that we can rename reserved words
    case Lam(lhs, rhs) =>
      val (paramCode, declaredVars) = translateLetPattern(lhs)
      new JSArrowFn(paramCode, translateTerm(rhs))
    // Binary expressions.
    case App(App(Var(name), left), right) if builtinFnOpMap contains name =>
      JSBinary(
        builtinFnOpMap.get(name).get,
        translateTerm(left),
        translateTerm(right)
      )
    // Tenary expressions.
    case App(App(App(Var("if"), tst), con), alt) =>
      new JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    // Function application.
    case App(lhs, rhs) => new JSInvoke(translateTerm(lhs), translateTerm(rhs))
    case Rcd(fields) =>
      new JSRecord(fields map { case (key, value) =>
        key -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      new JSMember(translateTerm(receiver), fieldName)
    // Turn let into an IIFE.
    case Let(isRec, name, value, body) =>
      new JSImmEvalFn(name, Left(translateTerm(body)), translateTerm(value))
    case Blk(stmts) =>
      new JSImmEvalFn(Right(stmts map { translateStatement(_) }))
    case CaseOf(term, cases) => {
      val argument = translateTerm(term)
      val parameter = getTemporaryName("x")
      val body = translateCaseBranch(parameter, cases)
      new JSImmEvalFn(parameter, Right(body), argument)
    }
    case IntLit(value) => {
      val useBigInt = MinimalSafeInteger <= value && value <= MaximalSafeInteger
      new JSLit(if (useBigInt) { value.toString }
      else { value.toString + "n" })
    }
    case DecLit(value) => new JSLit(value.toString)
    case StrLit(value) => new JSLit(JSLit.makeStringLiteral(value))
    case _             => ???
  }

  // Translate consecutive case branches into a list of if statements.
  def translateCaseBranch(name: Str, branch: CaseBranches): Ls[JSStmt] =
    branch match {
      case Case(className, body, rest) =>
        new JSIfStmt(
          new JSInstanceOf(new JSIdent(name), new JSIdent(className.idStr)),
          Ls(new JSReturnStmt(translateTerm(body)))
        ) :: translateCaseBranch(name, rest)
      case Wildcard(body) => Ls(new JSReturnStmt(translateTerm(body)))
      case NoCases        => Ls(new JSThrowStmt())
    }

  // TODO: add field definitions
  def translateClassDeclaration(name: Str, actualType: Type): JSClassDecl =
    actualType match {
      case Record(fields) => new JSClassDecl(name, fields map { _._1 })
      // I noticed `class Fun[A]: A -> A` is okay.
      // But I have no idea about how to do it.
      case _ => ???
    }

  def apply(pgrm: Pgrm): Ls[Str] = {
    val defResultObjName = getTemporaryName("defs")
    val exprResultObjName = getTemporaryName("exprs")
    val stmts: Ls[JSStmt] =
      JSConstDecl(defResultObjName, JSRecord(Nil)) ::
        JSConstDecl(exprResultObjName, JSArray(Nil)) ::
        pgrm.typeDefs
          .map { case TypeDef(kind, Primitive(name), typeParams, actualType) =>
            kind match {
              case Cls =>
                classNames += name
                translateClassDeclaration(name, actualType)
              case Trt => new JSComment(s"// trait $name")
              case Als => new JSComment(s"// type alias $name")
            }
          }
          // Generate something like:
          // ```js
          // const name = <expr>;
          // defs.name = name;
          // ```
          .concat(pgrm.defs.flatMap {
            case Def(isRecursive, name, L(body)) =>
              val translatedBody = translateTerm(body)
              val tempName = getTemporaryName(name)
              if (tempName =/= name) {
                letLhsAliasMap += name -> tempName
              }
              new JSConstDecl(tempName, translatedBody) ::
                new JSExprStmt(
                  JSAssignExpr(
                    JSMember(JSIdent(defResultObjName), name),
                    JSIdent(tempName)
                  )
                ) :: Nil
            case Def(isRecursive, name, R(body)) =>
              ???
          })
          // Generate something like `exprs.push(<expr>)`.
          .concat(pgrm.statements.zipWithIndex.map {
            case (term: Term, index) =>
              new JSExprStmt(
                JSInvoke(
                  JSMember(JSIdent(exprResultObjName), "push"),
                  translateTerm(term)
                )
              )
            case _ => ???
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
