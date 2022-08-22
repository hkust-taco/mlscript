package ts2mls.types;

import scala.collection.mutable.HashMap
import ts2mls.DecWriter
import ts2mls.TSProgram

abstract class TSAccessModifier
case object Public extends TSAccessModifier
case object Private extends TSAccessModifier
case object Protected extends TSAccessModifier

case class TSMemberType(val base: TSType, val modifier: TSAccessModifier = Public) extends TSType

abstract class TSType

case class TSTypeVariable(val name: String, val constraint: Option[TSType]) extends TSType

case class TSNamedType(typeName: String) extends TSType

case class TSEnumType(name: String) extends TSType

case class TSTupleType(types: List[TSType]) extends TSType

case class TSFunctionType(params: List[TSType], res: TSType, val typeVars: List[TSTypeVariable]) extends TSType

case class TSClassType(name: String, members: Map[String, TSMemberType], statics: Map[String, TSMemberType], typeVars: List[TSTypeVariable], parents: List[TSType])
  extends TSType

case class TSInterfaceType(name: String, members: Map[String, TSMemberType], typeVars: List[TSTypeVariable], parents: List[TSType])
  extends TSType

case class TSArrayType(eleType: TSType) extends TSType

abstract class TSStructuralType(lhs: TSType, rhs: TSType, notion: String) extends TSType

case class TSUnionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "|")
case class TSIntersectionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "&")

object TSIntersectionType {
  def getOverloadTypeVariables(inter: TSIntersectionType): List[TSTypeVariable] = inter match {
    case TSIntersectionType(lhs, rhs) => {
      val left = lhs match {
        case i: TSIntersectionType => getOverloadTypeVariables(i)
        case TSFunctionType(_, _, v) => v
      }

      val right = rhs match {
        case i: TSIntersectionType => getOverloadTypeVariables(i)
        case TSFunctionType(_, _, v) => v
      }

      (left ::: right).distinct
    }
    case _ => List()
  }
}

case class TSApplicationType(base: String, applied: List[TSType]) extends TSType