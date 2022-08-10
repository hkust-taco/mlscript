package mlscript.mono

abstract class DataType

object DataType:
  sealed class Singleton(value: Expr.Literal, dataType: DataType) extends DataType:
    override def toString(): String = value.toString()

  enum Primitive(name: String) extends DataType:
    case Integer extends Primitive("int")
    case Decimal extends Primitive("real")
    case Boolean extends Primitive("bool")
    case String extends Primitive("str")
    override def toString(): String = this.name
  end Primitive

  sealed class Tuple(elementTypes: List[DataType]) extends DataType:
    override def toString(): String = elementTypes.mkString("(", ", ", ")")

  sealed class Class(declaration: Item.TypeDecl) extends DataType:
    override def toString(): String = s"class ${declaration.name.name}"

  sealed class Function(parameterTypes: List[DataType], returnType: DataType) extends DataType:
    def this(returnType: DataType, parameterTypes: DataType*) =
      this(parameterTypes.toList, returnType)
    override def toString(): String =
      val parameterList = parameterTypes.mkString("(", ", ", ")")
      s"$parameterList -> $returnType"

  sealed class Record(fields: Map[String, DataType]) extends DataType:
    def this(fields: (String, DataType)*) = this(Map.from(fields))
    override def toString(): String =
      fields.iterator.map { (name, ty) => s"$name: $ty" }.mkString("{", ", ", "}")

  def infer(expr: Expr, compatiableType: Option[DataType]): DataType =
    expr match
      case Expr.Tuple(elements) => DataType.Tuple(elements.map(infer(_, None)))
      case lit @ Expr.Literal(value: BigInt) => Singleton(lit, Primitive.Integer)
      case lit @ Expr.Literal(value: BigDecimal) => Singleton(lit, Primitive.Decimal)
      case lit @ Expr.Literal(value: String) => Singleton(lit, Primitive.String)
      case lit @ Expr.Literal(value: Boolean) => Singleton(lit, Primitive.Boolean)
      case _ => throw MonomorphError(s"I can't infer the type of $expr now")
