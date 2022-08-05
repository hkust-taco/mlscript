package mlscript.mono.specializer

import mlscript.mono.Expr
import mlscript.mono.MonomorphError

object Builtin:
  private val builtinBinaryOperations = Map[String, (Expr, Expr) => Option[Expr]](
    (">", {
      case (Expr.Literal(lhs: BigInt), Expr.Literal(rhs: BigInt)) =>
        Some(Expr.Literal(lhs > rhs))
      case (Expr.Literal(lhs: BigDecimal), Expr.Literal(rhs: BigDecimal)) =>
        Some(Expr.Literal(lhs > rhs))
      case (_, _) => None
    }),
    ("-", {
      case (Expr.Literal(lhs: BigInt), Expr.Literal(rhs: BigInt)) =>
        Some(Expr.Literal(lhs - rhs))
      case (Expr.Literal(lhs: BigDecimal), Expr.Literal(rhs: BigDecimal)) =>
        Some(Expr.Literal(lhs - rhs))
      case (_, _) => None
    }),
    ("*", {
      case (Expr.Literal(lhs: BigInt), Expr.Literal(rhs: BigInt)) =>
        Some(Expr.Literal(lhs * rhs))
      case (Expr.Literal(lhs: BigDecimal), Expr.Literal(rhs: BigDecimal)) =>
        Some(Expr.Literal(lhs * rhs))
      case (_, _) => None
    })
  )

  def isBinaryOperator(name: String): Boolean =
    builtinBinaryOperations.contains(name)

  def evalulateBinaryOperation(name: String, lhs: Expr, rhs: Expr): Option[Expr] =
    builtinBinaryOperations(name)(lhs, rhs)
