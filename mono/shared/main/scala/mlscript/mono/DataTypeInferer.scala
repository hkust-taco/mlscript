package mlscript.mono

trait DataTypeInferer:
  import DataType._

  def findClassByName(name: String): Option[Item.TypeDecl]

  def infer(expr: Expr, compatiableType: Option[DataType]): DataType =
    expr match
      case Expr.Tuple(elements) => DataType.Tuple(elements.map(infer(_, None)))
      case lit @ Expr.Literal(value: BigInt) => Singleton(lit, Primitive.Integer)
      case lit @ Expr.Literal(value: BigDecimal) => Singleton(lit, Primitive.Decimal)
      case lit @ Expr.Literal(value: String) => Singleton(lit, Primitive.String)
      case lit @ Expr.Literal(value: Boolean) => Singleton(lit, Primitive.Boolean)
      case Expr.Apply(Expr.Ref(name), args) =>
        findClassByName(name).fold(DataType.Unknown)(DataType.Class(_))
      case _ => throw MonomorphError(s"I can't infer the type of $expr now")