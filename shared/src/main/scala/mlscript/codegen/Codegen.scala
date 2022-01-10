package mlscript

// Goals:
// - Better readability.
//  - Remove unnecessary parentheses.
//  - Add better indentations.
// - Consistent runtime behavior.
//  - Currying methods declared in MLscript.
//  - Combine curry calls on other functions.

import mlscript.utils._, shorthands._
import scala.collection.immutable
import scala.util.matching.Regex

class SourceLine(val content: Str, indent: Int = 0) {
  def indented: SourceLine = new SourceLine(content, indent + 1)
  def +(that: SourceLine): SourceLine =
    new SourceLine(content + that.content, indent)
  def withPrefix(prefix: Str): SourceLine =
    new SourceLine(prefix + content, indent)
  def withPostfix(postfix: Str): SourceLine =
    new SourceLine(content + postfix, indent)
  def between(prefix: Str, postfix: Str): SourceLine =
    new SourceLine(prefix + content + postfix, indent)
  override def toString: Str = "  " * indent + content
}

object SourceLine {
  def apply(line: Str): SourceLine = new SourceLine(line)
}

class SourceCode(val lines: Ls[SourceLine]) {

  /** Concat two parts of source code vertically. "1 \\ 2" + "3 \\ 4" == "1 \\ 2 \\ 3 \\ 4"
    *
    * @param that
    *   another part of source code
    * @return
    */
  def +(that: SourceCode): SourceCode = new SourceCode(lines ++ that.lines)

  /** Concat two parts of source code horizontally. "1 \\ 2" ++ "3 \\ 4" == "1 \\ 2 3 \\ 4"
    *
    * @param that
    *   another part of source code
    * @return
    */
  def ++(that: SourceCode): SourceCode = that.lines match {
    case head :: next =>
      if (lines.length > 0) {
        new SourceCode(lines.init ::: Ls(lines.last + head) ::: next)
      } else {
        that
      }
    case Nil => this
  }

  def isSingleLine: Bool = lines.length == 1

  def isMultipleLine: Bool = lines.length > 1

  def isEmpty: Bool = lines.isEmpty
  def indented: SourceCode = new SourceCode(lines map { _.indented })
  def parenthesized(implicit run: Bool = true): SourceCode =
    if (run) {
      lines.length match {
        case 0 => SourceCode("()")
        case 1 => new SourceCode(lines map { _.between("(", ")") })
        case _ =>
          val head = lines.head
          val middle = lines.tail.dropRight(1)
          val last = lines.last
          new SourceCode(
            head.withPrefix("(") :: middle ::: Ls(last.withPostfix(")"))
          )
      }
    } else {
      this
    }
  def clause: SourceCode =
    lines.length match {
      case 0 | 1 => this
      case _ =>
        val head = lines.head
        val middle = lines.tail.dropRight(1)
        val last = lines.last
        new SourceCode(
          head.withPrefix("(") :: middle ::: Ls(last.withPostfix(")"))
        )
    }
  def condition: SourceCode =
    lines.length match {
      case 0 => this
      case 1 => new SourceCode(lines map { _.between("(", ")") })
      case _ =>
        new SourceCode(
          SourceLine("(")
            :: lines.map({ _.indented })
            ::: Ls(SourceLine(")"))
        )
    }
  // Surround the source code with braces in a block style.
  def block: SourceCode =
    lines.length match {
      case 0 => SourceCode("{}")
      case _ =>
        new SourceCode(
          SourceLine("{")
            :: lines.map({ _.indented })
            ::: Ls(SourceLine("}"))
        )
    }
  override def toString: Str = lines.mkString("\n")

  def toLines: Ls[Str] = lines.map(_.toString)
}

object SourceCode {
  def apply(line: Str): SourceCode = new SourceCode(Ls(new SourceLine(line, 0)))
  def apply(lines: Ls[Str]): SourceCode = new SourceCode(lines map {
    new SourceLine(_, 0)
  })
  def fromStmts(stmts: Ls[JSStmt]): SourceCode = SourceCode.concat(stmts map { _.toSourceCode })

  val space: SourceCode = SourceCode(" ")
  val semicolon: SourceCode = SourceCode(";")
  val comma: SourceCode = SourceCode(",")
  val commaSpace: SourceCode = SourceCode(", ")
  val empty: SourceCode = SourceCode(Nil)

  def concat(codes: Ls[SourceCode]): SourceCode =
    codes.foldLeft(SourceCode.empty) { _ + _ }

  def record(entries: Ls[SourceCode]): SourceCode =
    entries match {
      case Nil         => SourceCode("{}")
      case entry :: Nil => if (entry.isMultipleLine) {
        SourceCode("{") + entry.indented + SourceCode("}")
      } else {
        SourceCode("{ ") ++ entry ++ SourceCode(" }")
      }
      case _ =>
        (entries.zipWithIndex.foldLeft(SourceCode("{")) { case (acc, (entry, index)) =>
          acc + (if (index + 1 === entries.length) { entry }
                 else { entry ++ SourceCode.comma }).indented
        }) + SourceCode("}")
    }

  /**
    * Surround the source code with braces.
    */
  def array(entries: Ls[SourceCode]): SourceCode =
    entries match {
      case Nil         => SourceCode("[]")
      case entry :: Nil => if (entry.isMultipleLine) {
        SourceCode("[") + entry.indented + SourceCode("]")
      } else {
        SourceCode("[") ++ entry ++ SourceCode("]")
      }
      case _ =>
        (entries.zipWithIndex.foldLeft(SourceCode("[")) { case (acc, (entry, index)) =>
          acc + (if (index + 1 === entries.length) { entry }
                 else { entry ++ SourceCode.comma }).indented
        }) + SourceCode("]")
    }

  def sepBy(codes: Ls[SourceCode], sep: SourceCode = this.commaSpace): SourceCode =
    codes.zipWithIndex
      .foldLeft(this.empty) { case (x, (y, i)) =>
        x ++ y ++ (if (i === codes.length - 1) this.empty else sep)
      }

}

abstract class JSCode {
  def toSourceCode: SourceCode
}

abstract class JSPattern extends JSCode {
  def bindings: Ls[Str]
}

final case class JSArrayPattern(elements: Ls[JSPattern]) extends JSPattern {
  def bindings: Ls[Str] = elements flatMap { _.bindings }
  def toSourceCode: SourceCode = SourceCode.array(elements map { _.toSourceCode })
}

final case class JSObjectPattern(properties: Ls[Str -> Opt[JSPattern]]) extends JSPattern {
  // If no sub-patterns, use the property name as the binding name.
  def bindings: Ls[Str] = properties flatMap {
    case name -> Some(subPattern) => subPattern.bindings
    case name -> None             => name :: Nil
  }
  def toSourceCode: SourceCode = SourceCode.record(
    properties
      .map {
        case name -> Some(JSWildcardPattern()) => SourceCode(name)
        case name -> Some(subPattern) =>
          SourceCode(s"$name: ") ++ subPattern.toSourceCode
        case name -> N => SourceCode(name)
      }
  )
}

final case class JSWildcardPattern() extends JSPattern {
  def bindings: Ls[Str] = Nil
  def toSourceCode: SourceCode = SourceCode.empty
}

final case class JSNamePattern(name: Str) extends JSPattern {
  def bindings: Ls[Str] = name :: Nil
  def toSourceCode: SourceCode = SourceCode(name)
}

abstract class JSExpr extends JSCode {
  // See: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence
  def precedence: Int

  def isSimple: Bool = false

  def stmt: JSExprStmt = JSExprStmt(this)
  def `return`: JSReturnStmt = JSReturnStmt(this)

  def member(name: Str): JSMember = JSMember(this, name)

  def apply(name: Str): JSMember = JSMember(this, name)

  def apply(args: JSExpr*): JSInvoke = JSInvoke(this, args.toList)

  def unary(op: Str): JSUnary = JSUnary(op, this)

  def binary(op: Str, rhs: JSExpr): JSBinary = JSBinary(op, this, rhs)

  def typeof(): JSUnary = JSUnary("typeof", this)

  def instanceOf(rhs: JSExpr): JSBinary = JSBinary("instanceof", this, rhs)

  def +(rhs: JSExpr): JSBinary = binary("+", rhs)

  def ??(rhs: JSExpr): JSBinary = binary("??", rhs)

  def :||(rhs: JSExpr): JSBinary = binary("||", rhs)

  def :===(rhs: JSExpr): JSBinary = binary("===", rhs)

  def :=(value: JSExpr): JSStmt = JSAssignExpr(this, value).stmt

  def switch(default: Ls[JSStmt], cases: (JSExpr -> Ls[JSStmt])*): JSSwitchStmt =
    JSSwitchStmt(
      this,
      (cases map { case (t, c) => JSSwitchCase(t, c) }).toList,
      S(JSDefaultCase(default))
    )

  def switch(cases: (JSExpr -> Ls[JSStmt])*): JSSwitchStmt =
    JSSwitchStmt(this, (cases map { case (t, c) => JSSwitchCase(t, c) }).toList)

  def log(): JSStmt = JSIdent("console").member("log")(this).stmt

  def embed(parentPrecedence: Int): SourceCode =
    if (precedence < parentPrecedence) {
      this.toSourceCode.parenthesized
    } else {
      this.toSourceCode
    }
}

object JSExpr {
  // Helper function for creating string literals.
  def apply(str: Str): JSLit = JSLit(JSLit.makeStringLiteral(str))

  def params(params: Ls[JSPattern]): SourceCode =
    params.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ (y match {
          case JSWildcardPattern() => SourceCode(s"_$i")
          case pattern             => pattern.toSourceCode
        }) ++ (if (i === params.length - 1) SourceCode.empty else SourceCode(", "))
      }
      .parenthesized
  def arguments(exprs: Ls[JSExpr]): SourceCode =
    exprs.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ y.toSourceCode ++ (if (i === exprs.length - 1) SourceCode.empty
                                else SourceCode(", "))
      }
      .parenthesized
}

final case class JSCommaExpr(exprs: Ls[JSExpr]) extends JSExpr {
  def precedence: Int = 1
  def toSourceCode: SourceCode = SourceCode.sepBy(exprs map { _.toSourceCode })
}

final case class JSAssignExpr(lhs: JSExpr, rhs: JSExpr) extends JSExpr {
  def precedence: Int = 3
  def toSourceCode: SourceCode =
    lhs.embed(precedence) ++ SourceCode(" = ") ++ rhs.embed(precedence)
}

final case class JSPlaceholderExpr() extends JSExpr {
  def precedence: Int = ???
  def toSourceCode: SourceCode = SourceCode.empty
}

final case class JSArrowFn(params: Ls[JSPattern], body: JSExpr \/ Ls[JSStmt]) extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode =
    params.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ (y match {
          case JSWildcardPattern() => SourceCode(s"_$i")
          case pattern             => pattern.toSourceCode
        }) ++ (if (i === params.length - 1) SourceCode.empty else SourceCode(", "))
      }
      .parenthesized ++ SourceCode(" => ") ++ (body match {
      case L(expr)  => expr.toSourceCode.parenthesized(expr.precedence < precedence)
      case R(stmts) => SourceCode.concat(stmts map { _.toSourceCode }).block
    })
  def toFuncExpr(name: Opt[Str]): JSFuncExpr = JSFuncExpr(name, params, body match {
    case L(expr) => expr.`return` :: Nil
    case R(stmts) => stmts
  })
}

final case class JSFuncExpr(name: Opt[Str], params: Ls[JSPattern], body: Ls[JSStmt]) extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode =
    SourceCode(s"function ${name getOrElse ""}") ++
      JSExpr.params(params) ++
      SourceCode.space ++
      SourceCode.concat(body map { _.toSourceCode }).block
}

// IIFE: immediately invoked function expression
final case class JSImmEvalFn(
    params: Ls[Str],
    body: Either[JSExpr, Ls[JSStmt]],
    arguments: Ls[JSExpr]
) extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode = {
    (SourceCode(s"function (${params mkString ", "}) ") ++ (body match {
      case Left(expr) => new JSReturnStmt(expr).toSourceCode
      case Right(stmts) =>
        stmts.foldLeft(SourceCode.empty) { _ + _.toSourceCode }
    }).block).parenthesized ++ JSExpr.arguments(arguments)
  }
}

final case class JSTenary(tst: JSExpr, csq: JSExpr, alt: JSExpr) extends JSExpr {
  def precedence: Int = 4
  def toSourceCode =
    tst.toSourceCode.parenthesized(tst.precedence < precedence) ++
      SourceCode(" ? ") ++
      csq.toSourceCode.parenthesized(csq.precedence < precedence) ++
      SourceCode(" : ") ++
      alt.toSourceCode.parenthesized(alt.precedence < precedence)
}

final case class JSInvoke(callee: JSExpr, arguments: Ls[JSExpr]) extends JSExpr {
  def precedence: Int = 20
  def toSourceCode = {
    val body = callee.toSourceCode.parenthesized(
      callee.precedence < precedence
    ) ++ arguments.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ y.toSourceCode ++ (if (i === arguments.length - 1) SourceCode.empty
                                else SourceCode(", "))
      }
      .parenthesized
    callee match {
      case JSIdent(_, true) => SourceCode("new ") ++ body
      case _                => body
    }
  }
}

final case class JSUnary(op: Str, arg: JSExpr) extends JSExpr {
  def precedence: Int = 15

  override def toSourceCode: SourceCode = (op match {
    case "typeof" => SourceCode("typeof ")
    case _        => SourceCode(op)
  }) ++ arg.toSourceCode.parenthesized(arg.precedence < precedence)
}

final case class JSBinary(op: Str, left: JSExpr, right: JSExpr) extends JSExpr {
  def apply(op: Str, left: JSExpr, right: JSExpr): JSBinary =
    new JSBinary(op, left, right)

  def precedence: Int = JSBinary.opPrecMap get op match {
    case Some(prec) => prec
    case None       => throw new Error(s"Unknown binary operator: $op")
  }

  override def toSourceCode: SourceCode =
    left.toSourceCode.parenthesized(left.precedence < precedence) ++
      SourceCode(s" $op ") ++
      right.toSourceCode.parenthesized(right.precedence < precedence)
}

object JSBinary {
  private def opPrecMap =
    immutable.HashMap[Str, Int](
      // infixr 14
      "**" -> 14,
      // infixl 13
      "*" -> 13,
      "/" -> 13,
      "%" -> 13,
      // infixl 12
      "+" -> 12,
      "-" -> 12,
      // infixl 11
      "<<" -> 11,
      ">>" -> 11,
      ">>>" -> 11,
      // infixl 10
      "<" -> 10,
      "<=" -> 10,
      ">" -> 10,
      ">=" -> 10,
      "in" -> 10,
      "instanceof" -> 10,
      // infixl 9
      "==" -> 9,
      "!=" -> 9,
      "===" -> 9,
      "!==" -> 9,
      // infixl 8
      "&" -> 8,
      // infixl 7
      "^" -> 7,
      // infixl 6
      "|" -> 6,
      // infixl 5
      "&&" -> 5,
      // infixl 4
      "||" -> 4,
      "??" -> 4
    )
  
  val operators: Set[Str] = opPrecMap.keySet
}

final case class JSLit(literal: Str) extends JSExpr {
  // Literals has the highest precedence.
  def precedence: Int = 22
  def toSourceCode = SourceCode(literal)
}

object JSLit {
  def makeStringLiteral(s: Str): Str = {
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

final case class JSInstanceOf(left: JSExpr, right: JSExpr) extends JSExpr {
  def precedence: Int = 12
  def toSourceCode: SourceCode =
    left.toSourceCode ++ SourceCode(" instanceof ") ++ right.toSourceCode
}

final case class JSIdent(name: Str, val isClassName: Bool = false) extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode = SourceCode(name)
}

final case class JSMember(target: JSExpr, field: Str) extends JSExpr {
  override def precedence: Int = 20
  override def toSourceCode: SourceCode =
    target.toSourceCode.parenthesized(
      target.precedence < precedence || target.isInstanceOf[JSRecord]
    ) ++ SourceCode(
      if (JSMember.isValidIdentifier(field)) {
        s".$field"
      } else {
        s"[${JSLit.makeStringLiteral(field)}]"
      }
    )

  override def isSimple: Bool = target.isSimple
}

final case class JSArray(items: Ls[JSExpr]) extends JSExpr {
  // Precedence of literals is zero.
  override def precedence: Int = 22
  // Make
  override def toSourceCode: SourceCode = SourceCode.array(items map { _.toSourceCode })
}

final case class JSRecord(entries: Ls[Str -> JSExpr]) extends JSExpr {
  // Precedence of literals is zero.
  override def precedence: Int = 22
  // Make
  override def toSourceCode: SourceCode = SourceCode
    .record(entries map { case (key, value) =>
      val body = if (JSMember.isValidIdentifier(key)) { key }
      else { JSLit.makeStringLiteral(key) }
      SourceCode(body + ": ") ++ value.toSourceCode
    })
}

object JSMember {
  private val identifierPattern: Regex = "^[A-Za-z$][A-Za-z0-9$]*$".r

  def isValidIdentifier(s: Str): Bool = identifierPattern.matches(s)
}

abstract class JSStmt extends JSCode

final case class JSExprStmt(expr: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    expr.toSourceCode.parenthesized(expr.isInstanceOf[JSRecord]) ++ SourceCode.semicolon
}

// A single if statement without else clauses
final case class JSIfStmt(test: JSExpr, body: Ls[JSStmt], `else`: Ls[JSStmt] = Nil) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode("if ") ++
    test.toSourceCode.condition ++
    SourceCode.space ++
    body.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block ++ (`else` match {
      case Nil => SourceCode.empty
      case _   => SourceCode("else ") ++ `else`.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block
    })
}

// A single return statement.
final case class JSReturnStmt(value: JSExpr) extends JSStmt {
  def toSourceCode =
    SourceCode(
      "return "
    ) ++ value.toSourceCode.clause ++ SourceCode.semicolon
}

final case class JSTryStmt(block: Ls[JSStmt], handler: JSCatchClause) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode("try ") ++
    block.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block ++
    handler.toSourceCode
}

final case class JSCatchClause(param: JSIdent, body: Ls[JSStmt]) extends JSCode {
  def toSourceCode: SourceCode = SourceCode(s" catch (${param.name}) ") ++
    body.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block
}

// Throw statement currently only used in non-exhaustive pattern matchings.
final case class JSThrowStmt() extends JSStmt {
  def toSourceCode =
    SourceCode("throw new Error(\"non-exhaustive case expression\");")
}

final case class JSSwitchStmt(
    discriminant: JSExpr,
    cases: Ls[JSSwitchCase],
    default: Opt[JSDefaultCase] = N
) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode("switch (") ++ discriminant.toSourceCode ++ SourceCode(") {") +
      cases.foldLeft(SourceCode.empty) { _ + _.toSourceCode.indented } +
      (default match {
        case S(default) => default.toSourceCode.indented + SourceCode("}")
        case N => SourceCode("}")
      })
}

final case class JSSwitchCase(test: JSExpr, consequent: Ls[JSStmt]) {
  def toSourceCode: SourceCode =
    SourceCode("case ") ++ test.toSourceCode ++ SourceCode(": ") +
      consequent.foldLeft(SourceCode.empty) { _ + _.toSourceCode.indented }
}

final case class JSDefaultCase(consequent: Ls[JSStmt]) {
  def toSourceCode: SourceCode =
    SourceCode("default:") +
      consequent.foldLeft(SourceCode.empty) { _ + _.toSourceCode.indented }
}

final case class JSLetDecl(decls: Ls[Str -> Opt[JSExpr]]) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode(s"let ") ++ decls.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ (y match {
          case (pat, N)       => SourceCode(pat)
          case (pat, S(init)) => SourceCode(pat) ++ SourceCode(" = ") ++ init.toSourceCode
        }) ++ (if (i === decls.length - 1) SourceCode.empty else SourceCode(", "))
      } ++ SourceCode.semicolon
}

object JSLetDecl {
  def from(names: Ls[Str]): JSLetDecl = JSLetDecl(names map { _ -> N })
}

final case class JSConstDecl(pattern: Str, body: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode(s"const $pattern = ") ++ (body match {
      case _: JSCommaExpr => body.toSourceCode.parenthesized
      case _              => body.toSourceCode
    }) ++ SourceCode.semicolon
}

final case class JSFuncDecl(name: Str, params: Ls[JSPattern], body: Ls[JSStmt]) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode(s"function $name") ++ JSExpr.params(params) ++ SourceCode.space ++ body
      .foldLeft(SourceCode.empty) { case (x, y) => x + y.toSourceCode }
      .block
}

abstract class JSClassMemberDecl extends JSStmt;

final case class JSClassGetter(name: Str, body: JSExpr \/ Ls[JSStmt]) extends JSClassMemberDecl {
  def toSourceCode: SourceCode =
    SourceCode(s"get $name() ") ++ (body match {
      case Left(expr) => new JSReturnStmt(expr).toSourceCode
      case Right(stmts) =>
        stmts.foldLeft(SourceCode.empty) { case (x, y) => x + y.toSourceCode }
    }).block
}

final case class JSClassMethod(
    name: Str,
    params: Ls[JSPattern],
    body: JSExpr \/ Ls[JSStmt]
) extends JSClassMemberDecl {
  def toSourceCode: SourceCode =
    SourceCode(name) ++ JSExpr.params(params) ++ SourceCode.space ++ (body match {
      case Left(expr) => new JSReturnStmt(expr).toSourceCode
      case Right(stmts) =>
        stmts.foldLeft(SourceCode.empty) { case (x, y) => x + y.toSourceCode }
    }).block
}

final case class JSClassMember(name: Str, body: JSExpr) extends JSClassMemberDecl {
  def toSourceCode: SourceCode =
    SourceCode(name) ++ SourceCode(" = ") ++ body.toSourceCode ++ SourceCode.semicolon
}

final case class JSClassDecl(
    val name: Str,
    fields: Ls[Str],
    base: Opt[JSClassDecl] = N,
    methods: Ls[JSClassMemberDecl] = Nil
) extends JSStmt {
  def toSourceCode: SourceCode = {
    val ctor = SourceCode(
      "  constructor(fields) {" :: (if (base.isEmpty) {
                                      Nil
                                    } else {
                                      "    super(fields);" :: Nil
                                    }) ::: (fields map { case name =>
        s"    this.$name = fields.$name;"
      }) concat "  }" :: Nil
    )
    val methodsSourceCode = methods.foldLeft(SourceCode.empty) { case (x, y) =>
      x + y.toSourceCode.indented
    }
    val epilogue = SourceCode("}" :: Nil)
    base match {
      case Some(baseCls) =>
        SourceCode(
          s"class $name extends ${baseCls.name} {" :: Nil
        ) + ctor + methodsSourceCode + epilogue
      case None =>
        if (fields.isEmpty && methods.isEmpty) {
          SourceCode(s"class $name {}")
        } else {
          SourceCode(
            s"class $name {" :: Nil
          ) + ctor + methodsSourceCode + epilogue
        }
    }
  }
  private val fieldsSet = collection.immutable.HashSet.from(fields)
}

final case class JSComment(text: Str) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode(s"// $text")
}
