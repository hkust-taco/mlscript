package ts2mls.types

import mlscript.utils._

object Converter {
  private val primitiveName = Map[String, String](
    "boolean" -> "Bool",
    "number" -> "Num",
    "string" -> "Str",
    "any" -> "anything",
    "unknown" -> "anything",
    "void" -> "unit",
    "null" -> "null",
    "undefined" -> "undefined",
    "never" -> "nothing",
    "object" -> "Object",
    "true" -> "true",
    "false" -> "false",
    "symbol" -> "Symbol",
    "error" -> "error",
    "bigint" -> "Num"
  )

  def escapeIdent(name: String) = {
    import mlscript.NewLexer
    if (NewLexer.keywords(name) || NewLexer.alpahOp(name) || name.contains("$") ||
      (!name.isEmpty() && name(0) >= '0' && name(0) <= '9'))
      s"""id"$name""""
    else name
  }
  
  def genExport(exported: Boolean) = if (exported) "export " else ""

  private def generateFunParamsList(params: List[TSParameterType]) =
    if (params.isEmpty) ""
    else params.iterator.zipWithIndex.map{ 
      case (tp, i) => convert(tp)("")
    }.reduceLeft((r, p) => s"$r, $p")

  def generateFunDeclaration(tsType: TSType, name: String, exported: Boolean)(implicit indent: String = ""): String = tsType match {
    case TSFunctionType(params, res, typeVars) => {
      val pList = generateFunParamsList(params)
      val tpList = if (typeVars.isEmpty) "" else s"[${typeVars.map(p => convert(p)("")).reduceLeft((r, p) => s"$r, $p")}]"
      s"${indent}${genExport(exported)}declare fun ${escapeIdent(name)}$tpList($pList): ${convert(res)("")}"
    }
    case overload @ TSIgnoredOverload(base, _) => s"${generateFunDeclaration(base, name, exported)} ${overload.warning}"
    case _ => throw new AssertionError("non-function type is not allowed.")
  }

  def convert(tsType: TSType, exported: Boolean = false)(implicit indent: String = ""): String = tsType match {
    case TSPrimitiveType(typeName) => primitiveName(typeName)
    case TSReferenceType(name) => name
    case TSFunctionType(params, res, typeVars) =>
      val tpNames = typeVars.map(_.name)
      val tpList = tpNames.foldLeft("")((res, tp) => s"${res}forall '$tp; ")
      val pList = generateFunParamsList(params)
      s"$tpList($pList) => ${convert(res)}"
    case TSUnionType(lhs, rhs) => s"(${convert(lhs)}) | (${convert(rhs)})"
    case TSIntersectionType(lhs, rhs) => s"(${convert(lhs)}) & (${convert(rhs)})"
    case TSTypeParameter(name, _) => s"'$name" // Constraints should be translated where the type parameters were created rather than be used
    case TSTupleType(lst) => s"(${lst.foldLeft("")((p, t) => s"$p${convert(t)}, ")})"
    case TSArrayType(element) => s"MutArray[${convert(element)}]"
    case TSEnumType => "Int"
    case TSMemberType(base, _) => convert(base) // TODO: support private/protected members
    case itf: TSInterfaceType =>
      if (itf.name.isEmpty()) convertRecord(itf.members, Nil, Nil, Map(), Nil, true) // Anonymous interfaces
      else convertClassOrInterface(Right(itf), exported)
    case cls: TSClassType =>
      convertClassOrInterface(Left(cls), exported)
    case TSSubstitutionType(TSReferenceType(base), applied) => s"${base}[${applied.map((app) => convert(app)).reduceLeft((res, s) => s"$res, $s")}]"
    case overload @ TSIgnoredOverload(base, _) => s"${convert(base)} ${overload.warning}"
    case TSParameterType(name, tp) => s"${escapeIdent(name)}: ${convert(tp)}"
    case TSTypeAlias(name, ori, tp) => {
      if (tp.isEmpty) s"${indent}${genExport(exported)}type ${escapeIdent(name)} = ${convert(ori)}"
      else s"${indent}${genExport(exported)}type ${escapeIdent(name)}[${tp.map(t => convert(t)).reduceLeft((s, t) => s"$s, $t")}] = ${convert(ori)}"
    }
    case TSLiteralType(value, isString) => if (isString) s"\"$value\"" else value
    case TSUnsupportedType(code, filename, line, column) =>
      s"""unsupported["$code", "$filename", $line, $column]"""
    case tp => throw new AssertionError(s"unexpected type $tp.")
  }

  private def convertClassOrInterface(tp: Either[TSClassType, TSInterfaceType], exported: Boolean)(implicit indent: String) = {
    val exp = genExport(exported)
    def convertParents(parents: List[TSType]) =
      if (parents.isEmpty) ""
      else parents.foldLeft(s" extends ")((b, p) => s"$b${convert(p)}, ").dropRight(2)
    def combineWithTypeVars(body: String, parents: List[TSType], typeName: String, typeVars: List[TSTypeParameter]) = {
      val inheritance = convertParents(parents)
      if (typeVars.isEmpty) s"${indent}${exp}declare $typeName$inheritance $body"
      else
        s"${indent}${exp}declare $typeName[${typeVars.map(convert(_)).reduceLeft((p, s) => s"$p, $s")}]$inheritance $body" // TODO: add constraints
    }
    tp match {
      case Left(TSClassType(name, members, statics, typeVars, parents, cons)) =>
        val body = convertRecord(members, typeVars, parents, statics, cons, false)
        val typeName = s"class ${escapeIdent(name)}"
        combineWithTypeVars(body, parents, typeName, typeVars)
      case Right(TSInterfaceType(name, members, typeVars, parents, callSignature)) =>
        callSignature match {
          case Some(cs) =>
            val prefix = s"${indent}${exp}declare "
            val inheritance = convertParents(parents)
            val tp = if (typeVars.isEmpty) "" else s"[${typeVars.map((tv) => tv.name).reduceLeft((p, s) => s"$p, $s")}]"
            s"${prefix}trait ${escapeIdent(name)}$tp: ${convert(cs)}$inheritance ${convertRecord(members, Nil, Nil, Map(), List(), false)}"
          case _ =>
            val body = convertRecord(members, typeVars, parents, Map(), List(), false)
            val typeName = s"trait ${escapeIdent(name)}"
            combineWithTypeVars(body, parents, typeName, typeVars)
        }
    }
  }

  private def convertRecord(members: Map[String, TSMemberType], typeVars: List[TSTypeParameter], parents: List[TSType],
    statics: Map[String, TSMemberType], constructorList: List[TSType], anonymous: Boolean)(implicit indent: String) = {
    val allRecs = members.toList.map((m) => m._2.modifier match {
      case Public =>
        if (anonymous) s"${escapeIdent(m._1)}: ${convert(m._2)},"
        else m._2.base match {
          case _: TSFunctionType => s"${generateFunDeclaration(m._2.base, m._1, false)(indent + "  ")}\n"
          case _: TSIgnoredOverload => s"${generateFunDeclaration(m._2.base, m._1, false)(indent + "  ")}\n"
          case _ => s"${indent}  val ${escapeIdent(m._1)}: ${convert(m._2)}\n"
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

    val ctor =
      if (constructorList.isEmpty) ""
      else
        s"${indent}  constructor(${constructorList.map(p => s"${convert(p)("")}").reduceLeft((res, p) => s"$res, $p")})\n"

    val lst = (ctor :: allRecs).filter((s) => !s.isEmpty())
    if (lst.isEmpty) s"{}"
    else if (anonymous) s"{${lst.reduceLeft((bd, m) => s"$bd$m")}}"
    else s"{\n${lst.reduceLeft((bd, m) => s"$bd$m")}$indent}"
  }
}
