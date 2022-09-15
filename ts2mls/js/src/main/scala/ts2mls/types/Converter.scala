package ts2mls.types

import mlscript.utils._

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
    "object" -> "object",
    "true" -> "bool", // will not appear individually
    "false" -> "" // will not appear individually
  )

  def convert(tsType: TSType)(implicit indent: String = ""): String = tsType match {
    case TSPrimitiveType(typeName) => primitiveName(typeName)
    case TSReferenceType(name) => name
    case TSFunctionType(params, res, _) =>
      // since functions can be defined by both `def` and `method`, it only returns the type of functions
      if (params.length == 0) s"${primitiveName("void")} => ${convert(res)}"
      else
        params.foldRight(convert(res))((p, f) => p match {
          case _: TSFunctionType => s"(${convert(p)}) => $f"
          case _ => s"${convert(p)} => $f"
        })
    case TSUnionType(lhs, rhs) => {
      val lres = convert(lhs)
      val rres = convert(rhs)

      if (lres.isEmpty()) rres
      else if (rres.isEmpty()) lres
      else s"($lres) | ($rres)"
    }
    case TSIntersectionType(lhs, rhs) => s"(${convert(lhs)}) & (${convert(rhs)})"
    case TSTypeParameter(name, _) => name // constraints should be translated where the type parameters were created rather than be used
    case TSTupleType(lst) => s"(${lst.foldLeft("")((p, t) => s"$p${convert(t)}, ")})"
    case TSArrayType(element) => s"MutArray<${convert(element)}>"
    case TSEnumType => "int"
    case TSMemberType(base, _) => convert(base) // TODO: support private/protected members
    case TSInterfaceType(name, members, typeVars, parents) => convertRecord(s"trait $name", members, typeVars, parents)(indent)
    case TSClassType(name, members, _, typeVars, parents) => convertRecord(s"class $name", members, typeVars, parents)(indent) // TODO: support static members
    case TSSubstitutionType(base, applied) => s"${base}<${applied.map((app) => convert(app)).reduceLeft((res, s) => s"$res, $s")}>"
    case overload @ TSIgnoredOverload(base, _) => s"${convert(base)} ${overload.warning}"
  }

  private def convertRecord(typeName: String, members: Map[String, TSMemberType],
    typeVars: List[TSTypeParameter], parents: List[TSType])(implicit indent: String) = {
    val allRecs = members.toList.map((m) => m._2.modifier match {
      case Public =>
        if (typeName === "trait ") s"${m._1}: ${convert(m._2)},"
        else m._2.base match {
          case _: TSFunctionType => s"${indent}  fun ${m._1}: ${convert(m._2)}\n"
          case _: TSIgnoredOverload => s"${indent}  fun ${m._1}: ${convert(m._2)}\n"
          case _ => s"${indent}  let ${m._1}: ${convert(m._2)}\n"
        }
      // case Public => {
      //   m._2.base match { // methods
      //     case f @ TSFunctionType(_, _, typeVars) if (!typeVars.isEmpty) =>
      //       s"  method ${m._1}[${typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}]: ${convert(f)}" // TODO: add constraints
      //     case overload @ TSIgnoredOverload(base, _) =>
      //       if (!base.typeVars.isEmpty)
      //         s"  method ${m._1}[${base.typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}]: ${convert(overload)}" // TODO: add constraints
      //       else s"${m._1}: ${convert(overload)}"
      //     case _ => s"${m._1}: ${convert(m._2)}" // other type members
      //   }
      // }
      case _ => "" // TODO: deal with private/protected members
    })

    val body = { // members without independent type parameters, translate them directly
      val lst = allRecs.filter((s) => !s.isEmpty())
      if (lst.isEmpty) "{}"
      else if (typeName === "trait ") s"(${lst.reduceLeft((bd, m) => s"$bd$m")})"
      else s"{\n${lst.reduceLeft((bd, m) => s"$bd$m")}$indent}"
    }
    // val methods = { // members with independent type parameters, use methods instead
    //   val lst = allRecs.filter(_.startsWith("  "))
    //   if (lst.isEmpty) ""
    //   else "\n" + lst.reduceLeft((bd, m) => s"$bd\n$m")
    // }
    
    if (typeName === "trait ") body // anonymous interfaces
    else { // named interfaces and classes
      val inheritance =
        if (parents.isEmpty) ""
        else parents.foldLeft("(): ")((b, p) => s"$b${convert(p)}, ").dropRight(2)
      if (typeVars.isEmpty) s"$typeName$inheritance $body"
      else
        s"$typeName<${typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}>$inheritance $body" // TODO: add constraints
    }
  }
}
