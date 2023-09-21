package mlscript.compiler

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

  sealed case class Tuple(elementTypes: List[DataType]) extends DataType:
    override def toString(): String = elementTypes.mkString("(", ", ", ")")

  sealed case class Class(declaration: Item.TypeDecl) extends DataType:
    override def toString(): String = s"class ${declaration.name.name}"

  sealed case class Function(parameterTypes: List[DataType], returnType: DataType) extends DataType:
    def this(returnType: DataType, parameterTypes: DataType*) =
      this(parameterTypes.toList, returnType)
    override def toString(): String =
      val parameterList = parameterTypes.mkString("(", ", ", ")")
      s"$parameterList -> $returnType"

  sealed case class Record(fields: Map[String, DataType]) extends DataType:
    def this(fields: (String, DataType)*) = this(Map.from(fields))
    override def toString(): String =
      fields.iterator.map { (name, ty) => s"$name: $ty" }.mkString("{", ", ", "}")

  case object Unknown extends DataType:
    override def toString(): String = "unknown"
