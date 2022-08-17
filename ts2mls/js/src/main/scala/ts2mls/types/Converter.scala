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
    "object" -> "{}"
  )

  def convert(tsType: TSType): String = tsType match {
    case TSNamedType(typeName) => primitiveName.getOrElse(typeName, typeName)
    case TSFunctionType(params, res, constraint) => {
      val func = 
        if (params.length == 0) s"${primitiveName("void")} -> (${convert(res)})"
        else params.foldRight(convert(res))((tst, mlst) => s"(${convert(tst)}) -> (${mlst})")
      func
    }
    case TSUnionType(lhs, rhs) => s"(${convert(lhs)}) | (${convert(rhs)})"
    case TSIntersectionType(lhs, rhs) => s"(${convert(lhs)}) & (${convert(rhs)})"
    case TSTypeVariable(name, _) => name
    case TSTupleType(lst) => s"(${convertTuple(lst)})"
    case TSArrayType(element) => s"MutArray[${convert(element)}]"
    case TSEnumType(_) => "int"
    case TSMemberType(base, modifier) => convert(base)
    case TSInterfaceType(name, members, typeVars, parents) => convertRecord(s"trait $name", members, typeVars, parents)
    case TSClassType(name, members, _, typeVars, parents) => convertRecord(s"class $name", members, typeVars, parents)
    case TSApplicationType(base, applied) => s"${base}[${convertApply(applied)}]"
    case _ => throw new java.lang.Exception("Unknown TypeScript Type")
  }

  private def convertTuple(types: List[TSType]): String =
    types.foldLeft("")((p, t) => s"$p${convert(t)}, ")
    

  private def convertApply(applied: List[TSType]): String = {
    if (applied.length == 0) throw new java.lang.Exception("empty applied list.")

    val res = applied.foldLeft("")((p, t) => s"$p${convert(t)}, ")
    res.substring(0, res.length() - 2)
  }

  private def convertRecord(typeName: String, members: Map[String, TSMemberType], typeVars: List[TSTypeVariable], parents: List[TSType]) = {
    val rec = members.toList.foldLeft(" ")((p, m) => m._2.modifier match {
      case Public => {
        m._2.base match {
          case TSFunctionType(_, _, typeVars) if (typeVars.length > 0) => p
          case inter: TSIntersectionType => {
            val lst = TSIntersectionType.getOverloadTypeVariables(inter)
            if (lst.isEmpty) s"$p${m._1}: ${convert(m._2)}; "
            else p
          }
          case _ => s"$p${m._1}: ${convert(m._2)}; "
        }
      }
      case _ => p
    })
    
    val body = if (members.isEmpty) "{}"
      else s"{${rec.substring(0, rec.length() - 2)} }"
    
    val res =
      if (typeName.equals("trait ")) body
      else {
        val extBody = parents.foldLeft(body)((b, p) => s"$b & ${convert(p)}")
        val params = typeVars.foldLeft("")((p, t) => s"$p${t.name}, ") // TODO: add constraints
        if (params.length == 0)
          s"$typeName: $extBody"
        else
          s"$typeName[${params.substring(0, params.length() - 2)}]: $extBody"
      }

    val methods = members.toList.foldLeft("")((p, m) => m._2.modifier match {
      case Public => {
        m._2.base match {
          case TSFunctionType(_, _, typeVars) if (typeVars.length > 0) => {
            val params = typeVars.foldLeft("")((p, t) => s"$p${t.name}, ") // TODO: add constraints
            s"$p\n  method ${m._1}[${params.substring(0, params.length - 2)}]: ${convert(m._2)}"
          }
          case inter: TSIntersectionType => {
            val lst = TSIntersectionType.getOverloadTypeVariables(inter)
            if (lst.isEmpty) p
            else {
              val params = lst.foldLeft("")((p, t) => s"$p${t.name}, ") // TODO: add constraints
              s"$p\n  method ${m._1}[${params.substring(0, params.length - 2)}]: ${convert(m._2)}"
            }
          }
          case _ => p
        }
      }
      case _ => p
    })

    if (methods.isEmpty()) res
    else res + methods
  }
}