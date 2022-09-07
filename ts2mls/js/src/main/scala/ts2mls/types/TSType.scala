package ts2mls.types

sealed abstract class TSAccessModifier
case object Public extends TSAccessModifier
case object Private extends TSAccessModifier
case object Protected extends TSAccessModifier

sealed abstract class TSType
case class TSMemberType(val base: TSType, val modifier: TSAccessModifier = Public) extends TSType
case class TSTypeParameter(val name: String, constraint: Option[TSType] = None) extends TSType
case class TSPrimitiveType(typeName: String) extends TSType
case class TSReferenceType(name: String) extends TSType
case object TSEnumType extends TSType
case class TSTupleType(types: List[TSType]) extends TSType
case class TSFunctionType(params: List[TSType], res: TSType, val typeVars: List[TSTypeParameter]) extends TSType
case class TSArrayType(eleType: TSType) extends TSType
case class TSSubstitutionType(base: String, applied: List[TSType]) extends TSType

case class TSClassType(
    name: String,
    members: Map[String, TSMemberType],
    statics: Map[String, TSMemberType],
    typeVars: List[TSTypeParameter],
    parents: List[TSType],
  ) extends TSType

case class TSInterfaceType(
    name: String,
    members: Map[String, TSMemberType],
    typeVars: List[TSTypeParameter],
    parents: List[TSType],
  ) extends TSType

sealed abstract class TSStructuralType(lhs: TSType, rhs: TSType, notion: String) extends TSType
case class TSUnionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "|")
case class TSIntersectionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "&")

case class TSIgnoredOverload(base: TSFunctionType, name: String) extends TSType {
  val warning = s"/* warning: the overload of function $name is not supported yet. */"
}
