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
    "true" -> "true",
    "false" -> "false"
  )

  def generateFunDeclaration(tsType: TSType, name: String)(implicit indent: String = ""): String = tsType match {
    case TSFunctionType(params, res, typeVars) => {
      val pList = if (params.isEmpty) "" else params.map(p => s"${convert(p)("")}").reduceLeft((r, p) => s"$r, $p")
      val tpList = if (typeVars.isEmpty) "" else s"<${typeVars.map(p => convert(p)("")).reduceLeft((r, p) => s"$r, $p")}>"
      s"${indent}fun $name$tpList($pList): ${convert(res)("")}"
    }
    case overload @ TSIgnoredOverload(base, _) => s"${generateFunDeclaration(base, name)} ${overload.warning}"
    case inter: TSIntersectionType => s"${indent}fun ${name}: ${Converter.convert(inter)}"
    case _ => throw new AssertionError("non-function type is not allowed.")
  }

  def convert(tsType: TSType)(implicit indent: String = ""): String = tsType match {
    case TSPrimitiveType(typeName) => primitiveName(typeName)
    case TSReferenceType(name) => name
    case TSFunctionType(params, res, _) =>
      if (params.length == 0) s"${primitiveName("void")} => ${convert(res)}"
      else
        params.foldRight(convert(res))((p, f) => s"(${convert(p.tp)}) => $f")
    case TSUnionType(lhs, rhs) => s"(${convert(lhs)}) | (${convert(rhs)})"
    case TSIntersectionType(lhs, rhs) => s"(${convert(lhs)}) & (${convert(rhs)})"
    case TSTypeParameter(name, _) => name // constraints should be translated where the type parameters were created rather than be used
    case TSTupleType(lst) => s"(${lst.foldLeft("")((p, t) => s"$p${convert(t)}, ")})"
    case TSArrayType(element) => s"MutArray<${convert(element)}>"
    case TSEnumType => "int"
    case TSMemberType(base, _) => convert(base) // TODO: support private/protected members
    case TSInterfaceType(name, members, typeVars, parents) =>
      convertRecord(s"trait $name", members, typeVars, parents, Map(), List())(indent)
    case TSClassType(name, members, statics, typeVars, parents, cons) =>
      convertRecord(s"class $name", members, typeVars, parents, statics, cons)(indent)
    case TSSubstitutionType(base, applied) => s"${base}<${applied.map((app) => convert(app)).reduceLeft((res, s) => s"$res, $s")}>"
    case overload @ TSIgnoredOverload(base, _) => s"${convert(base)} ${overload.warning}"
    case TSParameterType(name, tp) => s"${name}: ${convert(tp)}"
    case TSTypeAlias(name, ori, tp) =>
      if (tp.isEmpty) s"${indent}type $name = ${convert(ori)}"
      else s"${indent}type $name<${tp.map(t => convert(t)).reduceLeft((s, t) => s"$s, $t")}> = ${convert(ori)}"
    case TSLiteralType(value, isString) => if (isString) s"\"$value\"" else value
  }

  private def convertRecord(typeName: String, members: Map[String, TSMemberType], typeVars: List[TSTypeParameter],
    parents: List[TSType], statics: Map[String, TSMemberType], constructorList: List[TSType])(implicit indent: String) = {
    val allRecs = members.toList.map((m) => m._2.modifier match {
      case Public =>
        if (typeName === "trait ") s"${m._1}: ${convert(m._2)},"
        else m._2.base match {
          case _: TSFunctionType => s"${generateFunDeclaration(m._2.base, m._1)(indent + "  ")}\n"
          case _: TSIgnoredOverload => s"${generateFunDeclaration(m._2.base, m._1)(indent + "  ")}\n"
          case _ => s"${indent}  let ${m._1}: ${convert(m._2)}\n"
        }
      case _ => "" // TODO: deal with private/protected members
    }) :::
      statics.toList.map((s) => s._2.modifier match {
        case Public => s._2.base match {
          case _: TSClassType => convert(s._2)(indent + "  ") + "\n"
          case _ => "" // TODO: deal with other static type
        }
        case _ => "" // TODO: deal with private/protected static members
      })

    val body = { // members without independent type parameters, translate them directly
      val lst = allRecs.filter((s) => !s.isEmpty())
      if (lst.isEmpty) "{}"
      else if (typeName === "trait ") s"{${lst.reduceLeft((bd, m) => s"$bd$m")}}"
      else s"{\n${lst.reduceLeft((bd, m) => s"$bd$m")}$indent}"
    }
    
    if (typeName === "trait ") body // anonymous interfaces
    else { // named interfaces and classes
      val constructor =
        if (constructorList.isEmpty) "()"
        else s"(${constructorList.map(p => s"${convert(p)("")}").reduceLeft((res, p) => s"$res, $p")})"

      val inheritance =
        if (parents.isEmpty) constructor
        else parents.foldLeft(s"$constructor: ")((b, p) => s"$b${convert(p)}, ").dropRight(2)
      if (typeVars.isEmpty) s"${indent}$typeName$inheritance $body"
      else
        s"${indent}$typeName<${typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}>$inheritance $body" // TODO: add constraints
    }
  }
}
