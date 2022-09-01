package ts2mls.types

object Converter {
  private val primitiveName = Map[String, String](
    "boolean" -> "bool",
    "number" -> "number",
    "string" -> "string",
    "any" -> "anything",
    "unknown" -> "anything",
    "void" -> "unit",
    "null" -> "null",
    "undefined" -> "undefined",
    "never" -> "nothing",
    "object" -> "{}",
    "true" -> "true",
    "false" -> "false"
  )

  def convert(tsType: TSType): String = tsType match {
    case TSPrimitiveType(typeName) => primitiveName(typeName)
    case TSReferenceType(name) => name
    case TSFunctionType(params, res, _) =>
      // since functions can be defined by both `def` and `method`, it only returns the type of functions
      if (params.length == 0) s"${primitiveName("void")} -> (${convert(res)})"
      else params.foldRight(convert(res))((tst, mlst) => s"(${convert(tst)}) -> (${mlst})")
    case TSUnionType(lhs, rhs) => s"(${convert(lhs)}) | (${convert(rhs)})"
    case TSIntersectionType(lhs, rhs) => s"(${convert(lhs)}) & (${convert(rhs)})"
    case TSTypeParameter(name, _) => name // TODO: add constraints
    case TSTupleType(lst) => s"(${lst.foldLeft("")((p, t) => s"$p${convert(t)}, ")})"
    case TSArrayType(element) => s"MutArray[${convert(element)}]"
    case TSEnumType => "int"
    case TSMemberType(base, modifier) => convert(base)
    case TSInterfaceType(name, members, typeVars, parents) => convertRecord(s"trait $name", members, typeVars, parents)
    case TSClassType(name, members, _, typeVars, parents) => convertRecord(s"class $name", members, typeVars, parents) // TODO: deal with static members
    case TSSubstitutionType(base, applied) => s"${base}[${applied.map((app) => convert(app)).reduceLeft((res, s) => s"$res, $s")}]"
  }

  private def convertRecord(typeName: String, members: Map[String, TSMemberType],
    typeVars: List[TSTypeParameter], parents: List[TSType]) = {
    val allRecs = members.toList.map((m) => m._2.modifier match {
      case Public => {
        m._2.base match {
          case f @ TSFunctionType(_, _, typeVars) if (!typeVars.isEmpty) =>
            s"  method ${m._1}[${typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}]: ${convert(f)}" // TODO: add constraints
          case inter: TSIntersectionType => {
            val lst = TSIntersectionType.getOverloadTypeParameters(inter)
            if (lst.isEmpty) s"${m._1}: ${convert(inter)}"
            else
              s"  method ${m._1}[${lst.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s") }]: ${convert(inter)}" // TODO: add constraints
          }
          case _ => s"${m._1}: ${convert(m._2)}"
        }
      }
      case _ => "" // TODO: deal with private/protected members
    })

    val body = { // members without independent type parameters
      val lst = allRecs.filter((s) => !s.startsWith("  ") && !s.isEmpty())
      if (lst.isEmpty) "{}"
      else s"{ ${lst.reduceLeft((bd, m) => s"$bd; $m")} }"
    }
    val methods = { // members with independent type parameters, use methods instead
      val lst = allRecs.filter(_.startsWith("  "))
      if (lst.isEmpty) ""
      else "\n" + lst.reduceLeft((bd, m) => s"$bd\n$m")
    }
    
    if (typeName.equals("trait ")) body // anonymous interfaces
    else {
      val bodyWithParents = parents.foldLeft(body)((b, p) => s"$b & ${convert(p)}")
      if (typeVars.isEmpty) s"$typeName: $bodyWithParents$methods"
      else
        s"$typeName[${typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}]: $bodyWithParents$methods" // TODO: add constraints
    }
  }
}