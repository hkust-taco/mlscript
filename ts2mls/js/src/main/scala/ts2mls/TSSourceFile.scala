package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import types._
import mlscript.utils._

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) =
    TypeScript.forEachChild(sf, (node: js.Dynamic) => {
      val nodeObject = TSNodeObject(node)
      if (!nodeObject.isToken && !nodeObject.symbol.isUndefined)
        addNodeIntoNamespace(nodeObject, nodeObject.symbol.escapedName)(global)
    })

  private def getSubstitutionArguments[T <: TSAny](args: TSArray[T]): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(token.typeNode)
      case tp: TSTypeObject => lst :+ getObjectType(tp)
    })

  private def getObjectType(obj: TSTypeObject): TSType =
    if (obj.isEnumType) TSEnumType
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration)
    else if (obj.isTupleType) TSTupleType(getTupleElements(obj.typeArguments))
    else if (obj.isUnionType) getStructuralType(obj.types, true)
    else if (obj.isIntersectionType) getStructuralType(obj.types, false)
    else if (obj.isArrayType) TSArrayType(getObjectType(obj.elementTypeOfArray))
    else if (obj.isTypeParameterSubstitution) TSSubstitutionType(obj.symbol.escapedName, getSubstitutionArguments(obj.typeArguments))
    else if (obj.isObject)
      if (obj.isAnonymous) TSInterfaceType("", getAnonymousPropertiesType(obj.properties), List(), List())
      else TSReferenceType(obj.symbol.fullName)
    else if (obj.isTypeParameter) TSTypeParameter(obj.symbol.escapedName)
    else TSPrimitiveType(obj.intrinsicName)

  // get the type of a member in classes/named interfaces/anonymous interfaces
  private def getMemberType(node: TSNodeObject): TSType = {
    val res: TSType =
      if (node.isFunctionLike) getFunctionType(node)
      else getObjectType(node.`type`.typeNode)
    if (node.symbol.isOptionalMember) TSUnionType(res, TSPrimitiveType("undefined"))
    else res
  }

  private def getTypeParametes(node: TSNodeObject): List[TSTypeParameter] =
    node.typeParameters.foldLeft(List[TSTypeParameter]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeParameter(tp.symbol.escapedName, None)
      else lst :+ TSTypeParameter(tp.symbol.escapedName, Some(getObjectType(tp.constraint.typeNode)))
    )

  private def getFunctionType(node: TSNodeObject): TSFunctionType = {
    val pList = node.parameters.foldLeft(List[TSType]())((lst, p) => lst :+ (
      // in typescript, you can use `this` to explicitly specifies the callee
      // but it never appears in the final javascript file
      if (p.symbol.escapedName === "this") TSPrimitiveType("void")
      else if (p.isOptionalParameter) TSUnionType(getObjectType(p.symbolType), TSPrimitiveType("undefined"))
      else getObjectType(p.symbolType))
    )
    TSFunctionType(pList, getObjectType(node.returnType), getTypeParametes(node))
  }

  private def getStructuralType(types: TSTypeArray, isUnion: Boolean): TSType =
    types.foldLeft[Option[TSType]](None)((prev, cur) => prev match {
      case None => Some(getObjectType(cur))
      case Some(p) =>
        if (isUnion) Some(TSUnionType(p, getObjectType(cur))) else Some(TSIntersectionType(p, getObjectType(cur)))
    }).get

  private def getTupleElements(elements: TSTypeArray): List[TSType] =
    elements.foldLeft(List[TSType]())((lst, ele) => lst :+ getObjectType(ele))

  private def getHeritageList(node: TSNodeObject): List[TSType] =
    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) =>
      lst :+ getObjectType(h.types.get(index).typeNode)
    )

  private def getClassMembersType(list: TSNodeArray, requireStatic: Boolean): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      val name = p.symbol.escapedName

      // TODO: support `__constructor`
      if (name =/= "__constructor" && p.isStatic == requireStatic) {
        val mem =
          if (!p.isStatic) getMemberType(p)
          else parseMembers(name, p.initializer, true)

        mem match {
          case func: TSFunctionType => {
            if (!mp.contains(name)) mp ++ Map(name -> TSMemberType(func, p.modifier))
            else { // deal with functions overloading
              val old = mp(name)
              val res = old.base match {
                case f @ TSFunctionType(_, _, tv) =>
                  if (!tv.isEmpty || !func.typeVars.isEmpty) TSIgnoredOverload(func, name)
                  else if (!p.isImplementationOfOverload) TSIntersectionType(f, func)
                  else f
                case int: TSIntersectionType =>
                  if (!func.typeVars.isEmpty) TSIgnoredOverload(func, name)
                  else if (!p.isImplementationOfOverload) TSIntersectionType(int, func)
                  else int
                case TSIgnoredOverload(_, name) => TSIgnoredOverload(func, name) // the implementation is always after declarations
                case _ => old.base
              }

              mp.removed(name) ++ Map(name -> TSMemberType(res, p.modifier))
            }
          }
          case _ => mp ++ Map(name -> TSMemberType(mem, p.modifier))
        }
      }
      else mp
    })

  private def getInterfacePropertiesType(list: TSNodeArray): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => mp ++ Map(p.symbol.escapedName -> TSMemberType(getMemberType(p))))

  private def getAnonymousPropertiesType(list: TSSymbolArray): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) =>
      mp ++ Map(p.escapedName -> TSMemberType(if (p.`type`.isUndefined) getMemberType(p.declaration) else getObjectType(p.`type`))))

  private def parseMembers(name: String, node: TSNodeObject, isClass: Boolean): TSType =
    if (isClass)
      TSClassType(name, getClassMembersType(node.members, false), getClassMembersType(node.members, true), getTypeParametes(node), getHeritageList(node))
    else TSInterfaceType(name, getInterfacePropertiesType(node.members), getTypeParametes(node), getHeritageList(node))

  private def parseNamespaceLocals(map: TSSymbolMap)(implicit ns: TSNamespace) =
    map.foreach((sym) => {
      val node = sym.declaration
      if (!node.isToken)
        addNodeIntoNamespace(node, sym.escapedName, if (node.isFunctionLike) Some(sym.declarations) else None)
    })

  private def addFunctionIntoNamespace(fun: TSFunctionType, node: TSNodeObject, name: String)(implicit ns: TSNamespace) =
    if (!ns.containsMember(name, false)) ns.put(name, fun)
    else {
      val old = ns.get(name)
      val res = old match {
        case f @ TSFunctionType(_, _, tv) =>
          if (!tv.isEmpty || !fun.typeVars.isEmpty) TSIgnoredOverload(fun, name)
          else if (!node.isImplementationOfOverload) TSIntersectionType(f, fun)
          else f
        case int: TSIntersectionType =>
          if (!fun.typeVars.isEmpty) TSIgnoredOverload(fun, name)
          else if (!node.isImplementationOfOverload) TSIntersectionType(int, fun)
          else old
        case TSIgnoredOverload(_, name) => TSIgnoredOverload(fun, name) // the implementation is always after declarations
        case _ => old
      }
      
      ns.put(name, res)
    } 

  // overload functions in a sub-namespace need to provide an overload array
  // because the namespace merely exports symbols rather than node objects themselves
  private def addNodeIntoNamespace(node: TSNodeObject, name: String, overload: Option[TSNodeArray] = None)(implicit ns: TSNamespace) =
    if (node.isFunctionLike) overload match {
      case None =>
        addFunctionIntoNamespace(getFunctionType(node), node, name)
      case Some(decs) => {
        decs.foreach((d) =>
          addFunctionIntoNamespace(getFunctionType(d), d, name)
        )
      }
    }
    else if (node.isClassDeclaration)
      ns.put(name, parseMembers(ns.getFullPath(name), node, true))
    else if (node.isInterfaceDeclaration)
      ns.put(name, parseMembers(ns.getFullPath(name), node, false))
    else if (node.isNamespace)
      parseNamespace(node)

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit =
    parseNamespaceLocals(node.locals)(ns.derive(node.symbol.escapedName))
}
