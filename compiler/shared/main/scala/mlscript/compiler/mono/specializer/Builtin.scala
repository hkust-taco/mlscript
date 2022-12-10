package mlscript.compiler.mono.specializer

import mlscript.compiler.Expr
import mlscript.compiler.mono.MonomorphError

object Builtin:
  val builtinRefs = Set(">", "-", "+", "*", "true", "false")

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
    ("+", {
      case (Expr.Literal(lhs: BigInt), Expr.Literal(rhs: BigInt)) =>
        Some(Expr.Literal(lhs + rhs))
      case (Expr.Literal(lhs: BigDecimal), Expr.Literal(rhs: BigDecimal)) =>
        Some(Expr.Literal(lhs + rhs))
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

  private val builtinBinaryOperationsValue = Map[String, (MonoValue, MonoValue) => Option[MonoValue]](
    (">", {
      case (LiteralValue(lhs: BigInt), LiteralValue(rhs: BigInt)) =>
        Some(LiteralValue(lhs > rhs))
      case (LiteralValue(lhs: BigDecimal), LiteralValue(rhs: BigDecimal)) =>
        Some(LiteralValue(lhs > rhs))
      case (_, _) => None
    }),
    ("-", {
      case (LiteralValue(lhs: BigInt), LiteralValue(rhs: BigInt)) =>
        Some(LiteralValue(lhs - rhs))
      case (LiteralValue(lhs: BigDecimal), LiteralValue(rhs: BigDecimal)) =>
        Some(LiteralValue(lhs - rhs))
      case (_, _) => None
    }),
    ("+", {
      case (LiteralValue(lhs: BigInt), LiteralValue(rhs: BigInt)) =>
        Some(LiteralValue(lhs + rhs))
      case (LiteralValue(lhs: BigDecimal), LiteralValue(rhs: BigDecimal)) =>
        Some(LiteralValue(lhs + rhs))
      case (_, _) => None
    }),
    ("*", {
      case (LiteralValue(lhs: BigInt), LiteralValue(rhs: BigInt)) =>
        Some(LiteralValue(lhs * rhs))
      case (LiteralValue(lhs: BigDecimal), LiteralValue(rhs: BigDecimal)) =>
        Some(LiteralValue(lhs * rhs))
      case (_, _) => None
    })
  )

  def isBinaryOperator(name: String): Boolean =
    builtinBinaryOperations.contains(name)

  def evalulateBinaryOperation(name: String, lhs: Expr, rhs: Expr): Option[Expr] =
    builtinBinaryOperations(name)(lhs, rhs)

  def evaluateBinaryOpValue(name: String, lhs: MonoValue, rhs: MonoValue): Option[MonoValue] = 
    builtinBinaryOperationsValue(name)(lhs, rhs)
