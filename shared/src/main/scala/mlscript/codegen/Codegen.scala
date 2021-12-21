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
}

object SourceCode {
  def apply(line: Str): SourceCode = new SourceCode(Ls(new SourceLine(line, 0)))
  def apply(lines: Ls[Str]): SourceCode = new SourceCode(lines map {
    new SourceLine(_, 0)
  })

  val space: SourceCode = SourceCode(" ")
  val semicolon: SourceCode = SourceCode(";")
  val comma: SourceCode = SourceCode(",")
  val empty: SourceCode = SourceCode(Nil)

  def concat(codes: Ls[SourceCode]): SourceCode =
    codes.foldLeft(SourceCode.empty) { _ + _ }

  def record(entries: Ls[SourceCode]): SourceCode =
    entries match {
      case Nil         => SourceCode("{}")
      case sole :: Nil => SourceCode("{ ") + sole + SourceCode(" }")
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
      case sole :: Nil => SourceCode("[") + sole + SourceCode("]")
      case _ =>
        (entries.zipWithIndex.foldLeft(SourceCode("[")) { case (acc, (entry, index)) =>
          acc + (if (index + 1 === entries.length) { entry }
                 else { entry ++ SourceCode.comma }).indented
        }) + SourceCode("]")
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

  def stmt: JSExprStmt = JSExprStmt(this)
}

object JSExpr {
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

final case class JSAssignExpr(lhs: JSExpr, rhs: JSExpr) extends JSExpr {
  def precedence: Int = 3
  def toSourceCode: SourceCode =
    lhs.toSourceCode ++ SourceCode(" = ") ++ rhs.toSourceCode
}

final case class JSPlaceholderExpr() extends JSExpr {
  def precedence: Int = ???
  def toSourceCode: SourceCode = SourceCode.empty
}

final case class JSArrowFn(params: Ls[JSPattern], body: JSExpr) extends JSExpr {
  def precedence: Int = 22
  def toSourceCode: SourceCode =
    params.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ (y match {
          case JSWildcardPattern() => SourceCode(s"_$i")
          case pattern             => pattern.toSourceCode
        }) ++ (if (i === params.length - 1) SourceCode.empty else SourceCode(", "))
      }
      .parenthesized ++ SourceCode(" => ") ++ body.toSourceCode
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

final case class JSBinary(op: Str, left: JSExpr, right: JSExpr) extends JSExpr {
  def apply(op: Str, left: JSExpr, right: JSExpr): JSBinary =
    new JSBinary(op, left, right)

  def precedence: Int = JSBinary.opPrecMap get op match {
    case Some(prec) => prec
    case None       => ???
  }

  override def toSourceCode: SourceCode =
    left.toSourceCode.parenthesized(left.precedence < precedence) ++
      SourceCode(s" $op ") ++
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
      "||" -> 7,
    )
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
      target.precedence < precedence
    ) ++ SourceCode(
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
  def toSourceCode: SourceCode = expr.toSourceCode ++ SourceCode.semicolon
}

// A single if statement without else clauses
final case class JSIfStmt(test: JSExpr, body: Ls[JSStmt]) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode("if ") ++
    test.toSourceCode.condition ++
    SourceCode.space ++
    body.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block
}

// A single return statement.
final case class JSReturnStmt(value: JSExpr) extends JSStmt {
  def toSourceCode =
    SourceCode(
      "return "
    ) ++ value.toSourceCode.clause ++ SourceCode.semicolon
}

// Throw statement currently only used in non-exhaustive pattern matchings.
final case class JSThrowStmt() extends JSStmt {
  def toSourceCode =
    SourceCode("throw new Error(\"non-exhaustive case expression\");")
}

final case class JSLetDecl(pattern: Str, body: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode(
      s"let $pattern = "
    ) ++ body.toSourceCode ++ SourceCode.semicolon
}

final case class JSConstDecl(pattern: Str, body: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode(
      s"const $pattern = "
    ) ++ body.toSourceCode ++ SourceCode.semicolon
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
