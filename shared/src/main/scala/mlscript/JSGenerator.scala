package mlscript

import mlscript.utils._, shorthands._
import scala.util.matching.Regex
import collection.mutable.{HashMap, HashSet, Stack}
import collection.immutable.LazyList

// TODO: should I turn this into a class?
// Becasue type information for each run is local.
// Otherwise I could clear for each `apply`.
class JSGenerator {
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
  def translateStatement(stmt: Statement): Str = stmt match {
    case LetS(isRec, pat, rhs) => {
      // TODO: use `isRec` later.
      var (code, ids) = translateLetPattern(pat)
      "let " + code + " = " + translateTerm(rhs)
    }
    // BEGIN: Unused in MLscript
    case DataDefn(body)           => ???
    case DatatypeDefn(head, body) => ???
    case _                        => ???
    // END: Unused in MLscript
  }

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
      println(s"translateLetPattern: ${inspectTerm(t)}")
      ???
  }

  def translateTerm(term: Term): Str = term match {
    case Var(name) => name
    // TODO: need scope to track variables
    // so that we can rename reserved words
    case Lam(lhs, rhs) =>
      val (paramCode, declaredVars) = translateLetPattern(lhs)
      s"($paramCode) => ${translateTerm(rhs)}"
    case App(App(App(Var("if"), tst), con), alt) =>
      s"(${translateTerm(tst)}) ? (${translateTerm(con)}) : (${translateTerm(alt)})"
    case App(lhs, rhs) =>
      lhs match {
        case Var(callee) =>
          if (classNames.contains(callee)) {
            letLhsAliasMap.get(callee) match {
              case N        => s"new $callee(${translateTerm(rhs)})"
              case S(alias) => s"$alias(${translateTerm(rhs)})"
            }
          } else {
            s"$callee(${translateTerm(rhs)})"
          }
        case App(_, _) => s"${translateTerm(lhs)}(${translateTerm(rhs)})"
        case _ =>
          "(" + translateTerm(lhs) + ")" + "(" + translateTerm(rhs) + ")"
      }

    // Note: unused for now
    case Tup(fields) =>
      // TODO: find a representation for named tuple
      fields
        .map { case (key, value) => translateTerm(value) }
        .mkString("[", ", ", "]")
    case Rcd(fields) =>
      fields
        .map { case (key, value) => key + ":" + translateTerm(value) }
        .mkString("{", ", ", "}")
    case Sel(receiver, fieldName) =>
      "(" + translateTerm(receiver) + ")" + (if (isValidIdentifier(fieldName)) {
                                               s".$fieldName"
                                             } else {
                                               s"[${makeStringLiteral(fieldName)}]"
                                             })
    // Turn let into an IIFE.
    case Let(isRec, name, rhs, body) =>
      s"(($name) => ${translateTerm(body)})" + s"(${translateTerm(rhs)})"
    case Blk(stmts) =>
      "(function () {" + stmts
        .map { translateStatement(_) }
        .mkString(";") + "})()"
    // Begin: unused in MLParser
    case Bra(rcd, trm)                 => ???
    case Asc(trm, _type)               => ???
    case Bind(lhs, rhs)                => ???
    case Test(trm, ty)                 => ???
    case With(trm, fieldNme, fieldVal) => ???
    // End: unused in MLParser
    case CaseOf(term, cases) => {
      val argument = translateTerm(term)
      val parameter = getTemporaryName("x")
      val body = translateCaseBranch(parameter, cases).mkString("\n")
      s"(($parameter) => { $body })($argument)"
    }

    case IntLit(value) =>
      if (MinimalSafeInteger <= value && value <= MaximalSafeInteger) {
        value.toString
      } else {
        value.toString + "n"
      }
    case DecLit(value) => value.toString
    case StrLit(value) => makeStringLiteral(value)
  }

  def translateCaseBranch(name: Str, branch: CaseBranches): Ls[Str] =
    branch match {
      case Case(className, body, rest) =>
        (
          s"if ($name instanceof ${className.idStr}) {" +
            s"return ${translateTerm(body)};" +
            s"}"
        ) :: translateCaseBranch(name, rest)
      case Wildcard(body) => List("return " + translateTerm(body))
      case NoCases =>
        List("throw new Error(\"non-exhaustive case expression\");")
    }

  // TODO: add field definitions
  def translateClassDeclaration(name: Str, actualType: Type): Ls[Str] =
    actualType match {
      case Record(fields) =>
        Ls(s"class $name {", "  constructor(fields) {") ::: fields.map {
          case (name, _ty) => s"    this.$name = fields.$name"
        } ::: Ls("  }", "}")
      // I noticed `class Fun[A]: A -> A` is okay.
      // But I have no idea about how to do it.
      case _ => ???
    }

  def apply(pgrm: Pgrm): Ls[Str] = pgrm.typeDefs
    .flatMap { case TypeDef(kind, Primitive(name), typeParams, actualType) =>
      kind match {
        // So `class Right[A]: { value: A }`
        // Will be `TypeDef(Cls,Primitive(name),typeParams,actualType)` where
        // - kind = Cls
        // - name = "Right"
        // - typeParams = List(A)
        // - actualType = Record(List((value,Primitive(A)))))
        case Cls =>
          classNames += name
          translateClassDeclaration(name, actualType)
        // For debug use
        case Trt => s"// trait $name" :: Nil
        // For debug use
        case Als => s"// type alias $name" :: Nil
      }
    }
    .concat(pgrm.defs.map {
      case Def(isRecursive, name, L(body)) =>
        val translatedBody = translateTerm(body)
        s"let ${getTemporaryName(name)} = $translatedBody"
      case Def(isRecursive, name, R(body)) =>
        ???
    })

  private def getTemporaryName(name: Str): Str = (name #:: LazyList
    .from(0)
    .map { name + _.toString }).dropWhile { classNames contains _ }.head

  private val identifierPattern: Regex = "^[A-Za-z$][A-Za-z0-9$]*$".r

  private def isValidIdentifier(s: Str): Boolean = identifierPattern.matches(s)

  // Make a JavaScript compatible string literal
  private def makeStringLiteral(s: Str): Str = {
    s.map[Str] {
      _ match {
        case '"'  => "\\\""
        case '\\' => "\\\\"
        case '\b' => "\\b"
        case '\f' => "\\f"
        case '\n' => "\\n"
        case '\r' => "\\r"
        case '\t' => "\\t"
        case c =>
          if (0 < c && c <= 255 && !c.isControl) {
            c.toString
          } else {
            s"\\u${c.toInt}"
          }
      }
    }.mkString("\"", "", "\"")
  }

}
