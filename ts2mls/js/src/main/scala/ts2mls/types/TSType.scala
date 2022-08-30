package ts2mls.types;

abstract class TSAccessModifier
case object Public extends TSAccessModifier
case object Private extends TSAccessModifier
case object Protected extends TSAccessModifier

abstract class TSType
case class TSMemberType(val base: TSType, val modifier: TSAccessModifier = Public) extends TSType
case class TSTypeParameter(val name: String, val constraint: Option[TSType] = None) extends TSType
case class TSNamedType(typeName: String) extends TSType
case class TSReferenceType(name: String) extends TSType
case object TSEnumType extends TSType
case class TSTupleType(types: List[TSType]) extends TSType
case class TSFunctionType(params: List[TSType], res: TSType, val typeVars: List[TSTypeParameter]) extends TSType
case class TSArrayType(eleType: TSType) extends TSType
case class TSSubstitutionType(base: String, applied: List[TSType]) extends TSType

case class TSClassType(name: String,
                       members: Map[String, TSMemberType],
                       statics: Map[String, TSMemberType],
                       typeVars: List[TSTypeParameter],
                       parents: List[TSType]) extends TSType
case class TSInterfaceType(name: String,
                           members: Map[String, TSMemberType],
                           typeVars: List[TSTypeParameter],
                           parents: List[TSType]) extends TSType

abstract class TSStructuralType(lhs: TSType, rhs: TSType, notion: String) extends TSType
case class TSUnionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "|")
case class TSIntersectionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "&")

object TSIntersectionType {
  // we use an intersection type to indicate overloading functions
  // so if the function has type parameters, use this function to get them
  def getOverloadTypeParameters(inter: TSIntersectionType): List[TSTypeParameter] = inter match {
    case TSIntersectionType(lhs, rhs) =>
      ((lhs match {
        case i: TSIntersectionType => getOverloadTypeParameters(i)
        case TSFunctionType(_, _, v) => v
        case _ => List()
      }) :::
      (rhs match {
        case i: TSIntersectionType => getOverloadTypeParameters(i)
        case TSFunctionType(_, _, v) => v
        case _ => List()
      })).distinct
    case _ => List()
  }
}
