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
import scala.collection.mutable.ListBuffer
import mlscript.codegen.Symbol

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

/**
  * SourceCode is a list of SourceLines that can be exported to a code file
  * 
  * SourceCode provides a number of helper methods to create SourceCode
  * from strings and manipulate them. It also abstracts common code patterns
  * like block, condition, clause
  *
  * @param lines
  */
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
      if (lines.nonEmpty) {
        new SourceCode(lines.init ::: Ls(lines.last + head) ::: next)
      } else {
        that
      }
    case Nil => this
  }

  def isSingleLine: Bool = lines.sizeCompare(1) === 0

  def isMultipleLine: Bool = lines.lengthIs > 1

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

  val ampersand: SourceCode = SourceCode(" & ")
  val space: SourceCode = SourceCode(" ")
  val semicolon: SourceCode = SourceCode(";")
  val colon: SourceCode = SourceCode(": ")
  val separator: SourceCode = SourceCode(" | ")
  val comma: SourceCode = SourceCode(",")
  val commaSpace: SourceCode = SourceCode(", ")
  val empty: SourceCode = SourceCode(Nil)
  val openCurlyBrace: SourceCode = SourceCode("{")
  val closeCurlyBrace: SourceCode = SourceCode("}")
  val openAngleBracket: SourceCode = SourceCode("<")
  val closeAngleBracket: SourceCode = SourceCode(">")
  val fatArrow: SourceCode = SourceCode(" => ")
  val equalSign: SourceCode = SourceCode(" = ")

  def concat(codes: Ls[SourceCode]): SourceCode =
    codes.foldLeft(SourceCode.empty) { _ + _ }

  // concatenate source codes without intermediate allocations
  def bulkConcat(codes: Iterable[SourceCode]): SourceCode =
    new SourceCode(codes.iterator.map(_.lines).foldRight(List.empty[SourceLine])((lines, accum) => lines ::: accum))

  /**
    * Comma-separate elements of List[SourceCode] and wrap with curly braces.
    * Each element is on a new line.
    * 
    * @param entries
    * @return
    */
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
    * Comma separate elements of List[SourceCode] and wrap with curly braces
    * on the same horizontal line
    * 
    * @param entries
    * @return
    */
    def horizontalRecord(entries: Ls[SourceCode]): SourceCode = {
      entries match {
        case Nil => SourceCode("{}")
        case _ =>
          (entries
            .zipWithIndex.foldLeft(SourceCode("{")) { case (acc, (entry, index)) =>
            acc ++ entry ++ (if (index + 1 === entries.length) SourceCode.closeCurlyBrace else SourceCode.commaSpace)
          })
      }
    }


    def recordWithEntries(entries: List[SourceCode -> SourceCode]): SourceCode = {
      entries match {
        case Nil => SourceCode("{}")
        case _ =>
          (entries
            .map(entry => entry._1 ++ colon ++ entry._2)
            .zipWithIndex.foldLeft(SourceCode("{")) { case (acc, (entry, index)) =>
            acc ++ entry ++ (if (index + 1 === entries.length) SourceCode.closeCurlyBrace else SourceCode.commaSpace)
          })
      }
    }
    
    /** ',' separate and wrap in angled brackets the given source code instances
      * and return empty string if list is empty 
      *
      * @param entries
      * @return
      */
    def paramList(entries: List[SourceCode]): SourceCode = {
      entries match {
        case Nil => SourceCode("")
        case _ =>
          (entries
            .zipWithIndex.foldLeft(SourceCode.openAngleBracket) { case (acc, (entry, index)) =>
            acc ++ entry ++ (if (index + 1 === entries.length) SourceCode.closeAngleBracket else SourceCode.commaSpace)
          })
      }
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

  /**
    * Surround source code with square brackets concatenating elements
    * horizontally only. Single element is still wrapped in brackets
    *
    * @param entries
    * @return
    */
  def horizontalArray(entries: Ls[SourceCode]): SourceCode =
    (entries.zipWithIndex.foldLeft(SourceCode("[")) { case (acc, (entry, index)) =>
      acc ++ entry ++ (if (index + 1 === entries.length) SourceCode("]") else SourceCode.commaSpace)
    })


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
}

object JSPattern {
}

final case class JSArrayPattern(elements: Ls[JSPattern]) extends JSPattern {
  def toSourceCode: SourceCode = SourceCode.array(elements map { _.toSourceCode })
}

final case class JSObjectPattern(properties: Ls[Str -> Opt[JSPattern]]) extends JSPattern {
  // If no sub-patterns, use the property name as the binding name.
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
  def toSourceCode: SourceCode = SourceCode.empty
}

final case class JSNamePattern(name: Str) extends JSPattern {
  def toSourceCode: SourceCode = SourceCode(name)
}

abstract class JSExpr extends JSCode {
  // See: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence
  implicit def precedence: Int

  def isSimple: Bool = false

  def prop(property: JSExpr): JSMember = JSMember(this, property)

  def stmt: JSExprStmt = JSExprStmt(this)
  
  def `return`: JSReturnStmt = JSReturnStmt(S(this))

  def `throw`: JSThrowStmt = JSThrowStmt(this)

  def member(name: Str): JSField = JSField(this, name)

  def apply(name: Str): JSField = JSField(this, name)

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

  def embed(implicit parentPrecedence: Int): SourceCode =
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
  implicit def precedence: Int = 1
  def toSourceCode: SourceCode = SourceCode.sepBy(exprs map { _.toSourceCode })
}

object JSCommaExpr {
  val outerPrecedence: Int = 2
}

final case class JSAssignExpr(lhs: JSExpr, rhs: JSExpr) extends JSExpr {
  implicit def precedence: Int = 3
  def toSourceCode: SourceCode =
    lhs.embed(precedence) ++ SourceCode(" = ") ++ rhs.embed(precedence)
}

final case class JSPlaceholderExpr() extends JSExpr {
  implicit def precedence: Int = ???
  def toSourceCode: SourceCode = SourceCode.empty
}

final case class JSArrowFn(params: Ls[JSPattern], body: JSExpr \/ Ls[JSStmt]) extends JSExpr {
  // If the precedence is 2. We will have x => (x, 0) and (x => x)(1).
  implicit def precedence: Int = 2
  def toSourceCode: SourceCode =
    params.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ (y match {
          case JSWildcardPattern() => SourceCode(s"_$i")
          case pattern             => pattern.toSourceCode
        }) ++ (if (i === params.length - 1) SourceCode.empty else SourceCode(", "))
      }
      .parenthesized ++ SourceCode(" => ") ++ (body match {
      // TODO: Figure out how `=>` competes with other operators.
      case L(expr: JSRecord) => expr.toSourceCode.parenthesized
      case L(expr)  => expr.embed
      case R(stmts) => SourceCode.concat(stmts map { _.toSourceCode }).block
    })
  def toFuncExpr(name: Opt[Str]): JSFuncExpr = JSFuncExpr(name, params, body match {
    case L(expr) => expr.`return` :: Nil
    case R(stmts) => stmts
  })
}

final case class JSFuncExpr(name: Opt[Str], params: Ls[JSPattern], body: Ls[JSStmt]) extends JSExpr {
  implicit def precedence: Int = 22
  def toSourceCode: SourceCode =
    SourceCode(s"function ${name getOrElse ""}") ++
      JSExpr.params(params) ++
      SourceCode.space ++
      SourceCode.concat(body map { _.toSourceCode }).block
}

// IIFE: immediately invoked function expression
final case class JSImmEvalFn(
    name: Opt[Str],
    params: Ls[JSPattern],
    body: Either[JSExpr, Ls[JSStmt]],
    arguments: Ls[JSExpr]
) extends JSExpr {
  implicit def precedence: Int = 22
  def toSourceCode: SourceCode = name match {
    case None =>
      (SourceCode(s"${JSExpr.params(params)} => ") ++ (body match {
        case Left(expr: JSRecord) => expr.toSourceCode.parenthesized
        case Left(expr) => expr.toSourceCode
        case Right(stmts) =>
          stmts.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block
      })).parenthesized ++ JSExpr.arguments(arguments)
    case Some(fnName) =>
      (SourceCode(s"function $fnName${JSExpr.params(params)} ") ++ (body match {
        case Left(expr) => expr.`return`.toSourceCode
        case Right(stmts) =>
          stmts.foldLeft(SourceCode.empty) { _ + _.toSourceCode }
      }).block).parenthesized ++ JSExpr.arguments(arguments)
  }
}

final case class JSTenary(tst: JSExpr, csq: JSExpr, alt: JSExpr) extends JSExpr {
  implicit def precedence: Int = 4
  def toSourceCode =
    tst.embed ++ SourceCode(" ? ") ++ csq.embed ++ SourceCode(" : ") ++ alt.embed
}

final case class JSInvoke(callee: JSExpr, arguments: Ls[JSExpr]) extends JSExpr {
  implicit def precedence: Int = 20
  def toSourceCode =
    callee.embed(precedence) ++ arguments.zipWithIndex
      .foldLeft(SourceCode.empty) { case (x, (y, i)) =>
        x ++ y.embed(JSCommaExpr.outerPrecedence) ++
        (if (i === arguments.length - 1) SourceCode.empty else SourceCode(", "))
      }
      .parenthesized
}

final case class JSUnary(op: Str, arg: JSExpr) extends JSExpr {
  implicit def precedence: Int = 15

  override def toSourceCode: SourceCode = (op match {
    case "typeof" => SourceCode("typeof ")
    case _        => SourceCode(op)
  }) ++ arg.embed
}

final case class JSBinary(op: Str, left: JSExpr, right: JSExpr) extends JSExpr {
  def apply(op: Str, left: JSExpr, right: JSExpr): JSBinary =
    new JSBinary(op, left, right)

  implicit def precedence: Int = JSBinary.opPrecMap get op match {
    case Some(prec) => prec
    case None       => throw new Error(s"Unknown binary operator: $op")
  }

  override def toSourceCode: SourceCode =
    left.embed ++ SourceCode(s" $op ") ++ right.embed
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
  implicit def precedence: Int = 22
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
            f"\\u${c.toInt}%04X"
          }
      }
    }.mkString("\"", "", "\"")
  }
}

final case class JSInstanceOf(left: JSExpr, right: JSExpr) extends JSExpr {
  implicit def precedence: Int = 12
  def toSourceCode: SourceCode =
    left.toSourceCode ++ SourceCode(" instanceof ") ++ right.toSourceCode
}

final case class JSIdent(name: Str) extends JSExpr {
  implicit def precedence: Int = 22
  def toSourceCode: SourceCode = SourceCode(name)
}

final case class JSNew(ctor: JSExpr) extends JSExpr {
  implicit def precedence: Int = 21
  def toSourceCode: SourceCode = SourceCode("new ") ++ ctor.toSourceCode
}

class JSMember(`object`: JSExpr, property: JSExpr) extends JSExpr {
  override def precedence: Int = 20
  override def toSourceCode: SourceCode =
    `object`.toSourceCode.parenthesized(
      `object`.precedence < precedence || `object`.isInstanceOf[JSRecord]
    ) ++ SourceCode("[") ++ property.toSourceCode ++ SourceCode("]")

  override def isSimple: Bool = `object`.isSimple
}

object JSMember {
  def apply(`object`: JSExpr, property: JSExpr): JSMember = new JSMember(`object`, property)
}

class JSField(`object`: JSExpr, val property: JSIdent) extends JSMember(`object`, property) {
  override def toSourceCode: SourceCode =
    `object`.toSourceCode.parenthesized(
      `object`.precedence < precedence || `object`.isInstanceOf[JSRecord]
    ) ++ SourceCode(
      if (JSField.isValidFieldName(property.name)) {
        s".${property.name}"
      } else {
        s"[${JSLit.makeStringLiteral(property.name)}]"
      }
    )
}

object JSField {
  def apply(`object`: JSExpr, property: String): JSField = new JSField(`object`, JSIdent(property))

  private val identifierPattern: Regex = "^[A-Za-z$][A-Za-z0-9$]*$".r

  def isValidIdentifier(s: Str): Bool = identifierPattern.matches(s) && !Symbol.isKeyword(s)

  // in this case, a keyword can be used as a field name
  // e.g. `something.class` is valid
  def isValidFieldName(s: Str): Bool = identifierPattern.matches(s)

  def emitValidFieldName(s: Str): Str = if (isValidIdentifier(s)) s else JSLit.makeStringLiteral(s)
}

final case class JSArray(items: Ls[JSExpr]) extends JSExpr {
  // Precedence of literals is zero.
  override def precedence: Int = 22
  // Make
  override def toSourceCode: SourceCode =
    SourceCode.array(items map { _.embed(JSCommaExpr.outerPrecedence) })
}

final case class JSRecord(entries: Ls[Str -> JSExpr], methods: Ls[JSStmt] = Nil) extends JSExpr {
  override def precedence: Int = 22
  // Make
  override def toSourceCode: SourceCode = SourceCode
    .record((entries map { case (key, value) =>
      SourceCode(JSField.emitValidFieldName(key) + ": ") ++ value.embed(JSCommaExpr.outerPrecedence)
    }) ++ (methods.map((m) => m.toSourceCode)))
}

final case class JSClassExpr(cls: JSClassNewDecl) extends JSExpr {
  implicit def precedence: Int = 22
  def toSourceCode: SourceCode = cls.toSourceCode
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
      case _   => SourceCode(" else ") ++ `else`.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block
    })
}

final case class JSForInStmt(pattern: JSPattern, iteratee: JSExpr, body: Ls[JSStmt]) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode("for (const ") ++
    pattern.toSourceCode ++
    SourceCode(" in ") ++
    iteratee.toSourceCode ++
    SourceCode(")") ++
    body.foldLeft(SourceCode.empty) { _ + _.toSourceCode }.block
}

// A single return statement.
final case class JSReturnStmt(value: Opt[JSExpr]) extends JSStmt {
  def toSourceCode = (value match {
    case Some(value) => SourceCode("return ") ++ value.toSourceCode.clause
    case None => SourceCode("return")
  }) ++ SourceCode.semicolon
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
final case class JSThrowStmt(arg: JSExpr) extends JSStmt {
  def toSourceCode: SourceCode =
    SourceCode("throw ") ++ arg.toSourceCode.clause ++ SourceCode.semicolon
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
    SourceCode(s"get ${JSField.emitValidFieldName(name)}() ") ++ (body match {
      case Left(expr) => new JSReturnStmt(S(expr)).toSourceCode
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
    SourceCode(JSField.emitValidFieldName(name)) ++ JSExpr.params(params) ++ SourceCode.space ++ (body match {
      case Left(expr) => new JSReturnStmt(S(expr)).toSourceCode
      case Right(stmts) =>
        stmts.foldLeft(SourceCode.empty) { case (x, y) => x + y.toSourceCode }
    }).block
}

final case class JSClassMember(name: Str, body: JSExpr) extends JSClassMemberDecl {
  def toSourceCode: SourceCode =
    SourceCode(name) ++ SourceCode(" = ") ++ body.toSourceCode ++ SourceCode.semicolon
}

final case class JSClassDecl(
    name: Str,
    fields: Ls[Str],
    `extends`: Opt[JSExpr] = N,
    methods: Ls[JSClassMemberDecl] = Nil,
    implements: Ls[Str] = Nil,
) extends JSStmt {
  def toSourceCode: SourceCode = {
    val constructor: SourceCode = {
      val buffer = new ListBuffer[Str]()
      buffer += "  constructor(fields) {"
      if (`extends`.isDefined)
        buffer += "    super(fields);"
      implements.foreach { name =>
        buffer += s"    $name.implement(this);"
      }
      fields.foreach { name =>
        val innerName = if (JSField.isValidIdentifier(name)) s".${name}" else s"[${JSLit.makeStringLiteral(name)}]"
        buffer += s"    this$innerName = fields$innerName;"
      }
      buffer += "  }"
      SourceCode(buffer.toList)
    }
    val methodsSourceCode =
      methods.foldLeft(SourceCode.empty) { case (x, y) =>
        x + y.toSourceCode.indented
      }
    val epilogue = SourceCode("}")
    `extends` match {
      case Some(base) =>
        SourceCode(s"class $name extends ") ++ base.toSourceCode ++
          SourceCode(" {") + constructor + methodsSourceCode + epilogue
      case None =>
        if (fields.isEmpty && methods.isEmpty && implements.isEmpty) {
          SourceCode(s"class $name {}")
        } else {
          SourceCode(
            s"class $name {" :: Nil
          ) + constructor + methodsSourceCode + epilogue
        }
    }
  }

  private val fieldsSet = collection.immutable.HashSet.from(fields)
}

final case class JSClassNewDecl(
    name: Str,
    fields: Ls[Str],
    accessors: Ls[Str],
    privateMems: Ls[Str],
    `extends`: Opt[JSExpr],
    superFields: Ls[JSExpr],
    ctorParams: Ls[Str],
    rest: Opt[Str],
    methods: Ls[JSClassMemberDecl],
    implements: Ls[Str],
    initStmts: Ls[JSStmt],
    nestedTypes: Ls[Str],
    ctorOverridden: Bool,
    staticMethods: Ls[JSClassMemberDecl]
) extends JSStmt {
  def toSourceCode: SourceCode = {
    val constructor: SourceCode = {
      val buffer = new ListBuffer[Str]()
      val params =
        ctorParams.iterator.zipWithIndex.foldRight(rest match {
          case Some(rest) => s"...$rest"
          case _ => ""
        })((p, s) =>
        if (s.isEmpty) s"${p._1}"
        else s"${p._1}, $s")
      nestedTypes.foreach(t => buffer += s"  #$t;")
      privateMems.distinct.foreach(f => {
        buffer += s"  #${f};"
      })
      accessors.distinct.foreach(f => {
        if (!privateMems.contains(f)) buffer += s"  #${f};"
        buffer += s"  get ${f}() { return this.#${f}; }"
      })
      buffer += s"  constructor($params) {"
      if (`extends`.isDefined) {
        val sf = superFields.iterator.zipWithIndex.foldLeft("")((res, p) =>
          if (p._2 === superFields.length - 1) s"$res${p._1.toSourceCode}"
          else s"$res${p._1.toSourceCode}, "
        )
        buffer += s"    super($sf);"
      }
      implements.foreach { name =>
        buffer += s"    $name.implement(this);"
      }

      // if the default constructor is overridden, we generate the overridden version
      // otherwise, generate based on the class fields
      if (!ctorOverridden) {
        assert(fields.length === ctorParams.length, s"fields and ctorParams have different size in class $name.")
        fields.lazyZip(ctorParams).foreach { (field, param) =>
          buffer += s"    this.#$field = $param;" // TODO: invalid name?
        }
      }

      initStmts.foreach { s =>
        s.toSourceCode.indented.indented.toString.split("\n").foreach {
          line => buffer += line
        }
      }
      buffer += "  }"
      SourceCode(buffer.toList)
    }
    val methodsSourceCode =
      methods.foldLeft(SourceCode.empty) { case (x, y) =>
        x + y.toSourceCode.indented
      }
    val staticMethodsSourceCode =
      staticMethods.foldLeft(SourceCode.empty) { case (x, y) =>
        x + SourceCode("static") + y.toSourceCode.indented
      }
    val epilogue = SourceCode("}")
    `extends` match {
      case Some(base) =>
        SourceCode(s"class $name extends ") ++ base.toSourceCode ++
          SourceCode(" {") + constructor + methodsSourceCode + staticMethodsSourceCode + epilogue
      case None =>
        if (fields.isEmpty && methods.isEmpty && implements.isEmpty && accessors.isEmpty && initStmts.isEmpty && staticMethods.isEmpty) {
          SourceCode(s"class $name {}")
        } else {
          SourceCode(
            s"class $name {" :: Nil
          ) + constructor + methodsSourceCode + staticMethodsSourceCode + epilogue
        }
    }
  }

  private val fieldsSet = collection.immutable.HashSet.from(fields)
}

final case class JSComment(text: Str) extends JSStmt {
  def toSourceCode: SourceCode = SourceCode(s"// $text")
}

final case class JSParenthesis(exp: JSExpr) extends JSExpr {
  implicit def precedence: Int = 0
  def toSourceCode: SourceCode = exp.embed
}

object JSCodeHelpers {
  def id(name: Str): JSIdent = JSIdent(name)
  def lit(value: Int): JSLit = JSLit(value.toString())
  def const(name: Str, init: JSExpr): JSConstDecl = JSConstDecl(name, init)
  def `return`(): JSReturnStmt = JSReturnStmt(N)
  def `return`(expr: JSExpr): JSReturnStmt = expr.`return`
  def `throw`(expr: JSExpr): JSThrowStmt = expr.`throw`
  def forIn(pattern: JSNamePattern, iteratee: JSExpr)(stmts: JSStmt*): JSForInStmt
    = JSForInStmt(pattern, iteratee, stmts.toList)
  def fn(name: Str, params: JSPattern*)(stmts: JSStmt*): JSFuncDecl
    = JSFuncDecl(name, params.toList, stmts.toList)
  def param(name: Str): JSNamePattern = JSNamePattern(name)
}