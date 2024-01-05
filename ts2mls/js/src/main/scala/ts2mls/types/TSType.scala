package ts2mls.types

sealed abstract class TSAccessModifier
case object Public extends TSAccessModifier
case object Private extends TSAccessModifier
case object Protected extends TSAccessModifier

sealed abstract class TSType {
  val unsupported = false
}

// Record both parameter's name and parameter's type
case class TSParameterType(name: String, tp: TSType) extends TSType {
  override val unsupported: Boolean = tp.unsupported
}
case class TSMemberType(base: TSType, modifier: TSAccessModifier = Public) extends TSType {
  override val unsupported: Boolean = base.unsupported
}

case class TSTypeParameter(name: String, constraint: Option[TSType] = None) extends TSType {
  override val unsupported: Boolean = constraint.fold(false)(c => c.unsupported)
}

case class TSPrimitiveType(typeName: String) extends TSType
case class TSReferenceType(name: String) extends TSType {
  val nameList = if (name.contains(".")) name.split("\\.").toList else name :: Nil
}
case object TSEnumType extends TSType
case class TSTupleType(types: List[TSType]) extends TSType {
  override val unsupported: Boolean = types.foldLeft(false)((r, t) => r || t.unsupported)
}

case class TSFunctionType(params: List[TSParameterType], res: TSType, typeVars: List[TSTypeParameter]) extends TSType {
  override val unsupported: Boolean =
    res.unsupported || params.foldLeft(false)((r, t) => r || t.unsupported) ||
      typeVars.foldLeft(false)((r, t) => r || t.unsupported)
}

case class TSArrayType(eleType: TSType) extends TSType {
  override val unsupported: Boolean = eleType.unsupported
}
case class TSSubstitutionType(base: TSReferenceType, applied: List[TSType]) extends TSType {
  override val unsupported: Boolean = base.unsupported || applied.foldLeft(false)((r, t) => r || t.unsupported)
}

case class TSClassType(
  name: String,
  members: Map[String, TSMemberType],
  statics: Map[String, TSMemberType],
  typeVars: List[TSTypeParameter],
  parents: List[TSType],
  constructor: List[TSParameterType]
) extends TSType {
  override val unsupported: Boolean =
    typeVars.foldLeft(false)((r, t) => r || t.unsupported) || parents.foldLeft(false)((r, t) => t match {
      case cls: TSClassType => cls.members.values.foldLeft(r || cls.unsupported)((r, t) => r || t.unsupported)
      case itf: TSInterfaceType => itf.members.values.foldLeft(r || itf.unsupported)((r, t) => r || t.unsupported)
      case _ => r || t.unsupported
    })
}

case class TSInterfaceType(
  name: String,
  members: Map[String, TSMemberType],
  typeVars: List[TSTypeParameter],
  parents: List[TSType],
  callSignature: Option[TSFunctionType]
) extends TSType {
    override val unsupported: Boolean =
    typeVars.foldLeft(callSignature.fold(false)(cs => cs.unsupported))((r, t) => r || t.unsupported) ||
      parents.foldLeft(false)((r, t) => t match {
        case cls: TSClassType => cls.members.values.foldLeft(r || cls.unsupported)((r, t) => r || t.unsupported)
        case itf: TSInterfaceType => itf.members.values.foldLeft(r || itf.unsupported)((r, t) => r || t.unsupported)
        case _ => r || t.unsupported
      })
}

sealed abstract class TSStructuralType(lhs: TSType, rhs: TSType, notion: String) extends TSType {
  override val unsupported: Boolean = lhs.unsupported || rhs.unsupported
}
case class TSUnionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "|")
case class TSIntersectionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "&")

// `ts2mls` doesn't support overloading functions with type parameters.
// TSIgnoredOverload is used to store these functions and raise a warning later.
// Only the most general overloading form would be stored
case class TSIgnoredOverload(base: TSFunctionType, name: String) extends TSType {
  val warning = s"/* warning: the overload of function $name is not supported yet. */"
  override val unsupported: Boolean = base.unsupported
}

// Generate type name = ... in mlscript
case class TSTypeAlias(name: String, original: TSType, tp: List[TSType]) extends TSType {
  override val unsupported: Boolean =
    original.unsupported || tp.foldLeft(false)((r, t) => r || t.unsupported)
}
// Generate val name = ... in mlscript
case class TSRenamedType(name: String, original: TSType) extends TSType {
  override val unsupported: Boolean = original.unsupported
}
case class TSLiteralType(value: String, isString: Boolean) extends TSType
case class TSUnsupportedType(code: String, filename: String, line: String, column: String) extends TSType {
  override val unsupported: Boolean = true
}
object TSNoInfoUnsupported extends TSType { // Unsupported type without code and location information
  override val unsupported: Boolean = true
}
