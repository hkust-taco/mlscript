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
  def from(line: Str): SourceLine = new SourceLine(line)
}

class SourceCode(val lines: Ls[SourceLine]) {

  /** Concat two parts of source code vertically. "1 \\ 2" + "3 \\ 4" == "1 \\ 2
    * \\ 3 \\ 4"
    *
    * @param that
    *   another part of source code
    * @return
    */
  def +(that: SourceCode): SourceCode = new SourceCode(lines ++ that.lines)

  /** Concat two parts of source code horizontally. "1 \\ 2" ++ "3 \\ 4" == "1
    * \\ 2 3 \\ 4"
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
  def isEmpty: Bool = lines.isEmpty
  def indented: SourceCode = new SourceCode(lines map { _.indented })
  def parenthesized(implicit run: Bool = true): SourceCode =
    if (run) {
      lines.length match {
        case 0 => this
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
          SourceLine.from("(")
            :: lines.map({ _.indented })
            ::: Ls(SourceLine.from(")"))
        )
    }
  // Surround the source code with braces in a array style.
  def array: SourceCode =
    lines.length match {
      case 0 => SourceCode.from("[]")
      case 1 => new SourceCode(lines map { _.between("[", "]") })
      case _ =>
        new SourceCode(
          SourceLine.from("[")
            :: lines.map({ _.indented.withPostfix(",") })
            ::: Ls(SourceLine.from("]"))
        )
    }
  // Surround the source code with braces in a record style.
  def record: SourceCode =
    lines.length match {
      case 0 => SourceCode.from("{}")
      case 1 => new SourceCode(lines map { _.between("{ ", " }") })
      case _ =>
        new SourceCode(
          SourceLine.from("{")
            :: lines.map({ _.indented.withPostfix(",") })
            ::: SourceLine.from("}")
            :: Nil
        )
    }
  // Surround the source code with braces in a block style.
  def block: SourceCode =
    lines.length match {
      case 0 => SourceCode.from("{}")
      case _ =>
        new SourceCode(
          SourceLine.from("{")
            :: lines.map({ _.indented })
            ::: Ls(SourceLine.from("}"))
        )
    }
  override def toString: Str = lines.mkString("\n")
}

object SourceCode {
  def from(line: Str): SourceCode = new SourceCode(Ls(new SourceLine(line, 0)))
  def fromLines(lines: Ls[Str]): SourceCode = new SourceCode(lines map {
    new SourceLine(_, 0)
  })
  def space: SourceCode = SourceCode.from(" ")
  def semicolon: SourceCode = SourceCode.from(";")
  def empty: SourceCode = new SourceCode(Nil)
  def concat(codes: Ls[SourceCode]): SourceCode =
    codes.foldLeft(SourceCode.empty) { case (x, y) => x + y }
}

abstract class JSCode {
  def toSourceCode: SourceCode
}

abstract class JSExpr extends JSCode {
  // See: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence
  def precedence: Int
}

final case class JSAssignExpr(lhs: JSExpr, rhs: JSExpr) extends JSExpr {
  def precedence: Int = 3
  def toSourceCode: SourceCode =
    lhs.toSourceCode ++ SourceCode.from(" = ") ++ rhs.toSourceCode
}

final case class JSPlaceholderExpr() extends JSExpr {
  def precedence: Int = ???
  def toSourceCode: SourceCode = SourceCode.empty
}

final case class JSArrowFn(param: Str, body: JSExpr) extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode =
    SourceCode.from(s"($param) => ") ++ body.toSourceCode
}

// IIFE: immediately invoked function expression
final case class JSImmEvalFn(
    name: Str,
    body: Either[JSExpr, Ls[JSStmt]],
    argument: JSExpr
) extends JSExpr {
  def this(body: Either[JSExpr, Ls[JSStmt]]) =
    this("", body, new JSPlaceholderExpr())
  def precedence: Int = 22
  def toSourceCode: SourceCode = {
    (SourceCode.from(s"function ($name) ") ++ (body match {
      case Left(expr) => new JSReturnStmt(expr).toSourceCode
      case Right(stmts) =>
        stmts.foldLeft(SourceCode.empty) { case (x, y) => x + y.toSourceCode }
    }).block).parenthesized ++ argument.toSourceCode.parenthesized
  }
}

final case class JSTenary(tst: JSExpr, csq: JSExpr, alt: JSExpr)
    extends JSExpr {
  def precedence: Int = 4
  def toSourceCode =
    tst.toSourceCode.parenthesized(tst.precedence < precedence) ++
      SourceCode.from(" ? ") ++
      csq.toSourceCode.parenthesized(csq.precedence < precedence) ++
      SourceCode.from(" : ") ++
      alt.toSourceCode.parenthesized(alt.precedence < precedence)
}

final case class JSInvoke(callee: JSExpr, argument: JSExpr) extends JSExpr {
  def precedence: Int = 20
  def toSourceCode = {
    val body = callee.toSourceCode.parenthesized(
      callee.precedence < precedence
    ) ++ argument.toSourceCode.parenthesized
    callee match {
      case JSIdent(_, true) => SourceCode.from("new ") ++ body
      case _                => body
    }
  }
}

final case class JSBinary(op: Str, left: JSExpr, right: JSExpr) extends JSExpr {
  def apply(op: Str, left: JSExpr, right: JSExpr): JSBinary =
    new JSBinary(op, left, right)

  def precedence: Int = JSBinary.opPrecMap get op match {
    case Some(prec) => prec
    case None       => ???
  }

  override def toSourceCode: SourceCode =
    left.toSourceCode.parenthesized(left.precedence < precedence) ++
      SourceCode.from(s" $op ") ++
      right.toSourceCode.parenthesized(right.precedence < precedence)
}

object JSBinary {
  private def opPrecMap =
    immutable.HashMap[Str, Int](
      "**" -> 16,
      "*" -> 15,
      "/" -> 15,
      "%" -> 15,
      "+" -> 14,
      "-" -> 14,
      "<<" -> 13,
      ">>" -> 13,
      ">>>" -> 13,
      "<" -> 12,
      "<=" -> 12,
      ">" -> 12,
      ">=" -> 12,
      "in" -> 12,
      "instanceof" -> 12,
      "==" -> 11,
      "&&" -> 7,
      "||" -> 7
    )
}

final case class JSLit(literal: Str) extends JSExpr {
  // Literals has the highest precedence.
  def precedence: Int = 22
  def toSourceCode = SourceCode.from(literal)
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
    left.toSourceCode ++ SourceCode.from(" instanceof ") ++ right.toSourceCode
}

final case class JSIdent(name: Str, val isClassName: Bool = false)
    extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode = SourceCode.from(name)
}

final case class JSMember(target: JSExpr, field: Str) extends JSExpr {
  override def precedence: Int = 20
  override def toSourceCode: SourceCode =
    target.toSourceCode.parenthesized(
      target.precedence < precedence
    ) ++ SourceCode.from(
      if (JSMember.isValidIdentifier(field)) {
        s".$field"
      } else {
        s"[${JSLit.makeStringLiteral(field)}]"
      }
    )
}

final case class JSArray(items: Ls[JSExpr]) extends JSExpr {
  // Precedence of literals is zero.
  override def precedence: Int = 22
  // Make
  override def toSourceCode: SourceCode = SourceCode
    .concat(items map { _.toSourceCode })
    .array
}

final case class JSRecord(entries: Ls[(Str, JSExpr)]) extends JSExpr {
  // Precedence of literals is zero.
  override def precedence: Int = 22
  // Make
  override def toSourceCode: SourceCode = SourceCode
    .concat(entries map { case (key, value) =>
      val body = if (JSMember.isValidIdentifier(key)) { key }
      else { JSLit.makeStringLiteral(key) }
      SourceCode.from(body + ": ") ++ value.toSourceCode
    })
    .record
}

object JSMember {
  private val identifierPattern: Regex = "^[A-Za-z$][A-Za-z0-9$]*$".r

  def isValidIdentifier(s: Str): Bool = identifierPattern.matches(s)
}

abstract class JSStmt extends JSCode

final case class JSExprStmt(expr: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode = expr.toSourceCode ++ SourceCode.semicolon
}

// A single if statement without else clauses
final case class JSIfStmt(test: JSExpr, body: Ls[JSStmt]) extends JSStmt {
  def toSourceCode: SourceCode = {
    val bodySourceCode = body.foldLeft(SourceCode.empty) { case (x, y) =>
      x + y.toSourceCode
    }
    SourceCode.from(
      "if "
    ) ++ test.toSourceCode.condition ++ SourceCode.space ++ bodySourceCode.block
  }
}

// A single return statement.
final case class JSReturnStmt(value: JSExpr) extends JSStmt {
  def toSourceCode =
    SourceCode.from(
      "return "
    ) ++ value.toSourceCode.clause ++ SourceCode.semicolon
}

// Throw statement currently only used in non-exhaustive pattern matchings.
final case class JSThrowStmt() extends JSStmt {
  def toSourceCode =
    SourceCode.from("throw new Error(\"non-exhaustive case expression\");")
}

final case class JSLetDecl(pattern: Str, body: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode.from(
      s"let $pattern = "
    ) ++ body.toSourceCode ++ SourceCode.semicolon
}

final case class JSConstDecl(pattern: Str, body: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode.from(
      s"const $pattern = "
    ) ++ body.toSourceCode ++ SourceCode.semicolon
}

final case class JSClassDecl(name: Str, fields: Ls[Str], base: Opt[Str] = N)
    extends JSStmt {
  def toSourceCode: SourceCode = {
    val ext = (base map { case name => s"extends $name " }).getOrElse("")
    if (fields.isEmpty) { SourceCode.from(s"class $name $ext{}") }
    else {
      val prologue =
        s"class $name $ext{" ::
          "  constructor(fields) {" ::
          (if (base.isEmpty)
             "    super();" :: Nil
           else
             Nil)
      val inits = fields map { case name =>
        s"    this.$name = fields.$name"
      }
      new SourceCode(
        prologue ::: inits ::: ("  }" :: "}" :: Nil) map SourceLine.from
      )
    }
  }
}

final case class JSComment(text: Str) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode.from(s"// $text")
}
