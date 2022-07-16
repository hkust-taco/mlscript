package mlscript.mono

enum Expr:
  case Ref(name: String)
  case Lambda(params: List[Ref], body: Expr)
  case Apply(callee: Expr, arguments: List[Expr])
  case Tuple(fields: List[Expr])
  case Record(fields: List[(Ref, Expr)])
  case Select(receiver: Expr, field: Ref)
  case LetIn(isRec: Boolean, name: Ref, rhs: Expr, body: Expr)
  case Assign(assignee: Expr, value: Expr)
  case Subscript(receiver: Expr, index: Expr)
  case Match(scrutinee: Expr, branches: CaseBranch)
  enum Literal:
    case Integer(value: BigInt)
    case Decimal(value: BigDecimal)
    case String(value: Predef.String)
    case Unit(undefinedOrNull: Boolean)
  end Literal
end Expr

enum CaseBranch:
  case Pattern(pattern: Expr.Ref, body: Expr, tail: CaseBranch)
  case Wildcard(body: Expr)
  case Empty
