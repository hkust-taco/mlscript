package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import types._

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace) = {
    def generate(node: js.Dynamic): Unit = {
      val nodeObject = TSNodeObject(node)
      if (!nodeObject.isToken && !nodeObject.symbol.isUndefined)
        addNodeIntoNamespace(nodeObject, nodeObject.symbol.escapedName)(global)
    }

    TypeScript.forEachChild(sf, generate)
  }

  private def getSubstitutionArguments[T <: TSAny](args: TSArray[T]): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(token.typeNode)
      case tp: TSTypeObject => lst :+ getObjectType(tp)
    })

  private def getObjectType(obj: TSTypeObject): TSType =
    if (obj.isEnumType) TSEnumType()
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration)
    else if (obj.isTupleType) TSTupleType(getTupleElements(obj.resolvedTypeArguments))
    else if (obj.isUnionType) getStructuralType(obj.types, true)
    else if (obj.isIntersectionType) getStructuralType(obj.types, false)
    else if (obj.isArrayType) TSArrayType(getObjectType(obj.resolvedTypeArguments.get(0)))
    else if (obj.isTypeParameterSubstitution) TSSubstitutionType(obj.symbol.escapedName, getSubstitutionArguments(obj.resolvedTypeArguments))
    else if (obj.isNamedObject) TSReferenceType(obj.symbol.fullName)
    else if (obj.isObject) TSInterfaceType("", getInterfacePropertiesType(obj.declarationMembers), List(), List())
    else if (obj.isTypeParameter) TSTypeParameter(obj.symbol.escapedName)
    else TSNamedType(obj.intrinsicName)

  private def getDeclarationType(node: TSNodeObject): TSType = {
    val res: TSType =
      if (node.isFunctionLike) getFunctionType(node)
      else if (node.hasTypeNode) getObjectType(node.`type`.typeNode) // if the node has a `type` field, it can contain other type information
      else if (node.isDotsArray) TSArrayType(TSNamedType("any")) // variable parameter without type annotation
      else TSNamedType(node.symbol.symbolType) // built-in type
    if (node.isOptional) TSUnionType(res, TSNamedType("undefined"))
    else res
  }

  private def getTypeConstraints(node: TSNodeObject): List[TSTypeParameter] =
    node.typeParameters.foldLeft(List[TSTypeParameter]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeParameter(tp.symbol.escapedName, None)
      else lst :+ TSTypeParameter(tp.symbol.escapedName, Some(getObjectType(tp.constraint.typeNode)))
    )

  private def getFunctionType(node: TSNodeObject): TSFunctionType = {
    val constraints = getTypeConstraints(node)
    // in typescript, you can use `this` to explicitly specifies the callee
    // but it never appears in the final javascript file
    val pList = node.parameters.foldLeft(List[TSType]())((lst, p) => lst :+
      (if (p.symbol.escapedName.equals("this")) TSNamedType("void") else getDeclarationType(p)))
    TSFunctionType(pList, getObjectType(node.returnType), constraints)
  }

  private def getStructuralType(types: TSTypeArray, isUnion: Boolean): TSStructuralType = 
    types.foldLeft[Option[TSType]](None)((prev, cur) => prev match {
      case None => Some(getObjectType(cur))
      case Some(p) =>
        if (isUnion) Some(TSUnionType(p, getObjectType(cur))) else Some(TSIntersectionType(p, getObjectType(cur)))
    }).get.asInstanceOf[TSStructuralType]

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
      if (!name.equals("__constructor") && p.isStatic == requireStatic) {
        val mem =
          if (!p.isStatic) getDeclarationType(p)
          else parseMembers(name, p.initializer, true)

        mem match {
          case func: TSFunctionType => {
            if (!mp.contains(name)) mp ++ Map(name -> TSMemberType(func, p.modifier))
            else mp(name).base match {
              case old: TSFunctionType if (!p.hasImplementation) =>
                mp.removed(name) ++ Map(name -> TSMemberType(TSIntersectionType(old, func), p.modifier))
              case old: TSIntersectionType if (!p.hasImplementation) =>
                mp.removed(name) ++ Map(name -> TSMemberType(TSIntersectionType(old, func), p.modifier))
              case _ => mp
            }
          }
          case _ => mp ++ Map(name -> TSMemberType(mem, p.modifier))
        }
      }
      else mp
    })

  private def getInterfacePropertiesType(list: TSNodeArray): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => mp ++ Map(p.symbol.escapedName -> TSMemberType(getDeclarationType(p))))

  private def parseMembers(name: String, node: TSNodeObject, isClass: Boolean): TSType = {
    val members = node.members
    val constraints = getTypeConstraints(node)

    if (isClass)
      TSClassType(name, getClassMembersType(members, false), getClassMembersType(members, true), constraints, getHeritageList(node))
    else TSInterfaceType(name, getInterfacePropertiesType(members), constraints, getHeritageList(node))
  }

  private def parseNamespaceLocals(map: TSSymbolMap)(implicit ns: TSNamespace) =
    map.foreach((sym) => {
      val name = sym.escapedName
      val node = sym.declaration
      if (!node.isToken)
        addNodeIntoNamespace(node, name, if (node.isFunctionLike) Some(sym.declarations) else None)
    })

  private def addFunctionIntoNamespace(fun: TSFunctionType, node: TSNodeObject, name: String)(implicit ns: TSNamespace) =
    if (!ns.containsMember(name, false)) ns.put(name, fun)
    else ns.get(name) match {
      case old: TSFunctionType if (!node.hasImplementation) => // the signature of overload function
        ns.put(name, TSIntersectionType(old, fun))
      case old: TSIntersectionType if (!node.hasImplementation) => // the signature of overload function
        ns.put(name, TSIntersectionType(old, fun))
      case _ => {} // the implementation of the overload function. the type of this function may be wider, so just ignore it
    }

  // overload functions in a sub-namespace need to provide an overload array
  // because the namespace merely exports symbols rather than node objects themselves
  private def addNodeIntoNamespace(node: TSNodeObject, name: String, overload: Option[TSNodeArray] = None)(implicit ns: TSNamespace) =
    if (node.isFunctionLike) overload match {
      case None => {
        val typeInfo = getFunctionType(node)
        addFunctionIntoNamespace(typeInfo, node, name)
      }
      case Some(decs) => {
        decs.foreach((d) => {
          val func = getFunctionType(d)
          addFunctionIntoNamespace(func, d, name)
        })
      }
    }
    else if (node.isClassDeclaration) {
      val fullName = ns.getFullPath(name)
      ns.put(name, TSNamedType(name)) // placeholder for self-reference
      val typeInfo = parseMembers(fullName, node, true)
      ns.put(name, typeInfo)
    }
    else if (node.isInterfaceDeclaration) {
      val fullName = ns.getFullPath(name)
      ns.put(name, TSNamedType(name)) // placeholder for self-reference
      val typeInfo = parseMembers(fullName, node, false)
      ns.put(name, typeInfo)
    }
    else if (node.isNamespace) {
      parseNamespace(node)(ns)
    }

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit =
    parseNamespaceLocals(node.locals)(ns.derive(node.symbol.escapedName))
}