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

abstract class JSCode {
  def toSourceLines: Ls[Str]
}

abstract class JSExpr extends JSCode {
  // See: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence
  def precedence: Int
}

// IIFE: immediately invoked function expression
final case class Block(
    name: Str,
    body: Either[JSExpr, Ls[JSStmt]],
    argument: JSExpr
) extends JSExpr {
  // Literals has the highest precedence.
  def precedence: Int = 0
  def toSourceLines: Ls[Str] = {
    val bodyLines = body match {
      case Left(expr) => {
        val lines = expr.toSourceLines
        if (lines.length > 1) {
          "(" :: lines.map { "  " + _ } ::: Ls(")")
        } else {
          lines match {
            case head :: next => Ls(head)
            case Nil          => ??? // Should not happen.
          }
        }
      }
      case Right(stmts) => stmts {
        val lines = stmts.flatMap { _.toSourceLines }
        ???
      }
    }
  }
}

final case class Tenary(tst: JSExpr, csq: JSExpr, alt: JSExpr) extends JSExpr {
  def precedence: Int = 4
  def toSourceLines: Ls[Str] = ???
}

final case class Invoke(callee: JSExpr, argument: JSExpr) extends JSExpr {
  def precedence: Int = 20
  def toSourceLines: Ls[Str] = ???
}

final case class Literal(literal: Str) extends JSExpr {
  // Literals has the highest precedence.
  def precedence: Int = 0
  def toSourceLines: Ls[Str] = Ls(literal)
}

abstract class JSStmt extends JSCode

// A single if statement without else clauses
final case class IfStmt(test: JSExpr, body: Ls[JSStmt]) extends JSStmt {
  def toSourceLines: Ls[Str] = {
    val testLines = test.toSourceLines
    // Prologue means `if (...) {`
    val prologue = if (testLines.length > 1) {
      "if (" :: testLines.map { "  " + _ } ::: Ls(") {")
    } else {
      testLines match {
        case head :: next => Ls(s"if ($head) {")
        case Nil          => ??? // Should not happen.
      }
    }
    val epilogue = Ls("}")
    prologue ::: body.flatMap { _.toSourceLines.map { "  " + _ } } ::: epilogue
  }
}

// A single return statement.
final case class ReturnStmt(value: JSExpr) extends JSStmt {
  def toSourceLines: Ls[Str] = {
    val valueLines = value.toSourceLines
    if (valueLines.length > 1) {
      "return (" :: valueLines.map { "  " + _ } ::: Ls(");")
    } else {
      valueLines match {
        case head :: next => Ls(s"return $head")
        case Nil          => Ls("throw new Error(\"nothing was returned\");")
      }
    }
  }
}

// Throw statement currently only used in non-exhaustive pattern matchings.
final case class ThrowStmt() extends JSStmt {
  def toSourceLines: Ls[Str] =
    Ls("throw new Error(\"non-exhaustive case expression\");")
}
