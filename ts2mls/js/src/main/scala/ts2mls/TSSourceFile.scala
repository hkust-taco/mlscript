package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import types._

class TSSourceFile(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) extends Module {
  override def >(name: String): TSType = global.>(name)
  override def >>(name: String): TSNamespace = global.>>(name)

  private def visit(node: js.Dynamic): Unit = {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isToken) return

    if (nodeObject.isFunctionDeclaration) {
      val funcName = nodeObject.symbol.escapedName
      val typeInfo = getFunctionType(nodeObject)(Map())
      if (!global.containsMember(funcName)) global.put(funcName, typeInfo)
      else global.>(funcName) match {
        case old: TSFunctionType if (nodeObject.body.isUndefined) =>
          global.put(funcName, TSIntersectionType(old, typeInfo))
        case old: TSIntersectionType if (nodeObject.body.isUndefined) =>
          global.put(funcName, TSIntersectionType(old, typeInfo))
        case _ => {}
      }
    }
    else if (nodeObject.isClassDeclaration) {
      val className = nodeObject.symbol.escapedName
      val typeInfo = parseMembers(nodeObject, true)(global)
      global.put(className, typeInfo)
    }
    else if (nodeObject.isInterfaceDeclaration) {
      val iName = nodeObject.symbol.escapedName
      val typeInfo = parseMembers(nodeObject, false)(global)
      global.put(iName, typeInfo)
    }
    else if (nodeObject.isNamespace) {
      val nsName = nodeObject.symbol.escapedName
      parseNamespace(nodeObject)(global)
    }
  }

  TypeScript.forEachChild(sf, visit)

  private def getApplicationArguments(args: TSTokenArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): List[TSType] = {
    val tail = args.get(args.length - index - 1)
    if (tail.isUndefined) List()
    else getApplicationArguments(args, index + 1) :+ getObjectType(tail.getTypeFromTypeNode())
  }

  private def getApplicationArguments(args: TSTypeArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): List[TSType] = {
    val tail = args.get(args.length - index - 1)
    if (tail.isUndefined) List()
    else getApplicationArguments(args, index + 1) :+ getObjectType(tail)
  }

  private def getObjectType(node: TSTypeSource)(implicit tv: Map[String, TSTypeVariable]): TSType = node match {
    case node: TSNodeObject => {
      val res = {
        val typeNode = node.`type`
        if (typeNode.hasTypeName) {
          val name = typeNode.typeName.escapedText
          if (!typeNode.typeArguments.isUndefined)
            TSApplicationType(TSNamedType(name), getApplicationArguments(typeNode.typeArguments, 0))
          else if (tv.contains(name)) tv(name)
          else TSNamedType(name)
        }
        else if (typeNode.isFunctionTypeNode) getFunctionType(typeNode)
        else if (node.isFunctionLike) getFunctionType(node)
        else if (typeNode.isTupleTypeNode) TSTupleType(getTupleElements(typeNode.elements, 0))
        else if (typeNode.isUnionTypeNode) getUnionType(typeNode.typesToken, None, 0)
        else if (typeNode.isIntersectionTypeNode) getIntersectionType(typeNode.types, None, 0)
        else if (typeNode.isArrayTypeNode) TSArrayType(getObjectType(typeNode.elementType.getTypeFromTypeNode))
        else if (!node.typeName.isUndefined)
          tv.getOrElse(node.typeName.escapedText, TSNamedType(node.typeName.escapedText))
        else if (!typeNode.isUndefined && !typeNode.members.isUndefined)
          TSInterfaceType("", getInterfacePropertiesType(typeNode.members, 0), List(), List())
        else {
          val name = node.symbol.getType()
          if (tv.contains(name)) tv(name)
          else TSNamedType(name)
        }
      }
      
      if (node.questionToken.isUndefined && node.initializer.isUndefined) res
      else res match {
        case TSNamedType(name) if (name.equals("undefined")) => res
        case _ => TSUnionType(res, TSNamedType("undefined"))
      }
    }
    case obj: TSTypeObject => {
      val dec = obj.declaration
      val args = obj.resolvedTypeArguments
      if (obj.isEnumType) TSNamedType(obj.aliasSymbol.escapedName)
      else if (dec.isFunctionLike) getFunctionType(dec)
      else if (obj.isTupleType) TSTupleType(getTupleElements(args, 0))
      else if (obj.isUnionType) getStructuralType(obj.types, None, true, 0)
      else if (obj.isIntersectionType) getStructuralType(obj.types, None, false, 0)
      else if (obj.isArrayType) TSArrayType(getObjectType(args.get(0)))
      else if (!args.isUndefined) TSApplicationType(TSNamedType(obj.symbol.escapedName), getApplicationArguments(args, 0))
      else if (!obj.symbol.isUndefined) {
          val symDec = obj.symbol.valueDeclaration
          if (!symDec.isUndefined && !symDec.properties.isUndefined)
            TSInterfaceType("", getInterfacePropertiesType(symDec.properties, 0), List(), List())
          else if (!dec.isUndefined && !dec.members.isUndefined)
            TSInterfaceType("", getInterfacePropertiesType(dec.members, 0), List(), List())
          else tv.getOrElse(obj.symbol.escapedName, TSNamedType(obj.symbol.escapedName)) 
      }
      else {
        if (tv.contains(obj.intrinsicName)) tv(obj.intrinsicName)
        else TSNamedType(obj.intrinsicName)
      }
    }
  }

  private def getTypeConstraints(list: TSNodeArray, prev: List[TSTypeVariable], index: Int)(implicit tv: Map[String, TSTypeVariable]): List[TSTypeVariable] = {
    val tail = list.get(list.length - index - 1)
    if (tail.isUndefined) prev
    else if (tail.constraint.isUndefined)
      getTypeConstraints(list, prev, index + 1) :+ TSTypeVariable(tail.symbol.escapedName, None)
    else
      getTypeConstraints(list, prev, index + 1) :+ TSTypeVariable(tail.symbol.escapedName, Some(getObjectType(tail.constraint.getTypeFromTypeNode)))
  }

  private def getTypeConstraints(node: TSNodeObject)(implicit tv: Map[String, TSTypeVariable]): List[TSTypeVariable] = {
    if (node.typeParameters.isUndefined) List()
    else getTypeConstraints(node.typeParameters, List(), 0)
  }

  private def getFunctionParametersType(list: TSNodeArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): List[TSType] = {
    val tail = list.get(list.length - index - 1)
    if (tail.isUndefined) List() else getFunctionParametersType(list, index + 1) :+ getObjectType(tail)
  }

  private def constaintsListToMap(constraints: List[TSTypeVariable]) =
    constraints.foldLeft(Map[String, TSTypeVariable]())((m, v) => 
      m ++ Map(v.name -> TSTypeVariable(v.name, None)) // we will apply the constraints in the record declarations.
    )

  private def getFunctionType(node: TSNodeObject)(implicit tv: Map[String, TSTypeVariable]): TSFunctionType = {
    val params = node.parameters
    val constraints = getTypeConstraints(node)
    val ntv = constaintsListToMap(constraints) ++ tv
    val pList = if (params.isUndefined) List() else getFunctionParametersType(params, 0)(ntv)
    val res = node.getReturnTypeOfSignature()
    TSFunctionType(pList, getObjectType(res)(ntv), constraints)
  }

  private def getUnionType(types: TSTokenArray, prev: Option[TSUnionType], index: Int)(implicit tv: Map[String, TSTypeVariable]): TSUnionType = prev match {
    case None => {
      val fst = types.get(index)
      val snd = types.get(index + 1)
      getUnionType(types, Some(TSUnionType(getObjectType(fst.getTypeFromTypeNode), getObjectType(snd.getTypeFromTypeNode))), index + 2)
    }
    case _ => {
      val t = types.get(index)
      if (t.isUndefined) prev.get
      else getUnionType(types, Some(TSUnionType(prev.get, getObjectType(t.getTypeFromTypeNode))), index + 1)
    }
  }

  private def getIntersectionType(types: TSNodeArray, prev: Option[TSIntersectionType], index: Int)(implicit tv: Map[String, TSTypeVariable]): TSIntersectionType = prev match {
    case None => {
      val fst = types.get(index)
      val snd = types.get(index + 1)
      getIntersectionType(types, Some(TSIntersectionType(getObjectType(fst), getObjectType(snd))), index + 2)
    }
    case _ => {
      val t = types.get(index)
      if (t.isUndefined) prev.get
      else getIntersectionType(types, Some(TSIntersectionType(prev.get, getObjectType(t))), index + 1)
    }
  }

  private def getStructuralType(types: TSTypeArray, prev: Option[TSStructuralType], isUnion: Boolean, index: Int)(implicit tv: Map[String, TSTypeVariable]): TSStructuralType = prev match {
    case None => {
      val fst = types.get(index)
      val snd = types.get(index + 1)
      if (isUnion)
        getStructuralType(types, Some(TSUnionType(getObjectType(fst), getObjectType(snd))), isUnion, index + 2)
      else
        getStructuralType(types, Some(TSIntersectionType(getObjectType(fst), getObjectType(snd))), isUnion, index + 2)
    }
    case _ => {
      val t = types.get(index)
      if (t.isUndefined) prev.get
      else 
        if (isUnion)
          getStructuralType(types, Some(TSUnionType(prev.get, getObjectType(t))), isUnion, index + 1)
        else
          getStructuralType(types, Some(TSIntersectionType(prev.get, getObjectType(t))), isUnion, index + 1)
    }
  }

  private def getTupleElements(elements: TSTokenArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): List[TSType] = {
    val tail = elements.get(elements.length - index - 1)
    if (tail.isUndefined) List()
    else getTupleElements(elements, index + 1) :+ getObjectType(tail.getTypeFromTypeNode)
  }

  private def getTupleElements(elements: TSTypeArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): List[TSType] = {
    val tail = elements.get(elements.length - index - 1)
    if (tail.isUndefined) List()
    else getTupleElements(elements, index + 1) :+ getObjectType(tail)
  }

  private def getInheritList(list: TSNodeArray, index: Int)(implicit ns: TSNamespace): List[TSType] = {
    val tail = list.get(list.length - index - 1)
    if (tail.isUndefined) List()
    else {
      val parent = tail.types.get(index)
      val name = parent.expression.escapedText
      if (parent.typeArguments.isUndefined)
        getInheritList(list, index + 1) :+ ns.>(name)
      else {
        val app = getApplicationArguments(parent.typeArguments, 0)(Map())
        getInheritList(list, index + 1) :+ TSApplicationType(ns.>(name), app)
      }
    }
  }

  private def getInheritList(node: TSNodeObject)(implicit ns: TSNamespace): List[TSType] = {
    if (node.heritageClauses.isUndefined) List()
    else getInheritList(node.heritageClauses, 0)
  }

  private def getClassMembersType(list: TSNodeArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): Map[String, TSMemberType] = {
    val tail = list.get(list.length - index - 1)
    if (tail.isUndefined) Map()
    else {
      val name = tail.symbol.escapedName
      if (!name.equals("__constructor")) {
        val other = getClassMembersType(list, index + 1)
        val mem = getObjectType(tail)

        val modifier = if (tail.modifiers.isUndefined) Public
          else tail.modifiers.foldLeft[TSAccessModifier](Public)((m, t) =>
            if (t.isPrivate) Private
            else if (t.isProtected) Protected
            else m
          )

        mem match {
          case func: TSFunctionType => {
            if (!other.contains(name)) other ++ Map(name -> TSMemberType(func, modifier))
            else other(name).base match {
              case old: TSFunctionType if (tail.body.isUndefined) =>
                other.removed(name) ++ Map(name -> TSMemberType(TSIntersectionType(old, func), modifier))
              case old: TSIntersectionType if (tail.body.isUndefined) =>
                other.removed(name) ++ Map(name -> TSMemberType(TSIntersectionType(old, func), modifier))
              case _ => other
            }
          }
          case _ => other ++ Map(name -> TSMemberType(mem, modifier))
        }
      }
      else getClassMembersType(list, index + 1)
    }
  }

  private def getInterfacePropertiesType(list: TSNodeArray, index: Int)(implicit tv: Map[String, TSTypeVariable]): Map[String, TSMemberType] = {
    val tail = list.get(list.length - index - 1)
    if (tail.isUndefined) Map()
    else {
      val name = tail.symbol.escapedName
      getInterfacePropertiesType(list, index + 1) ++ Map(name -> TSMemberType(getObjectType(tail)))
    }
  }

  private def parseMembers(node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace): TSFieldType = {
    val name = node.symbol.escapedName
    val members = node.members
    val constraints = getTypeConstraints(node)(Map())
    val tvMap = constaintsListToMap(constraints)

    if (isClass) TSClassType(name, getClassMembersType(members, 0)(tvMap), constraints, getInheritList(node))
    else TSInterfaceType(name, getInterfacePropertiesType(members, 0)(tvMap), constraints, getInheritList(node))
  }

  private def parseNamespaceExports(it: TSSymbolIter)(implicit ns: TSNamespace): Unit = {
    it.next()
    if (!it.done) {
      val data = it.value()
      val name = data._1
      val node = data._2.getFirstDeclaration()

      if (!node.isToken && node.isFunctionDeclaration) {
        val func = getFunctionType(node)(Map())
        if (!ns.containsMember(name)) ns.put(name, func)
        else ns.>(name) match {
          case old: TSFunctionType if (node.body.isUndefined) =>
            ns.put(name, TSIntersectionType(old, func))
          case old: TSIntersectionType if (node.body.isUndefined) =>
            ns.put(name, TSIntersectionType(old, func))
        }

        parseNamespaceExports(it)
      }
      else if (!node.isToken && node.isClassDeclaration) {
        ns.put(name, parseMembers(node, true))
        parseNamespaceExports(it)
      }
      else if (!node.isToken && node.isInterfaceDeclaration) {
        ns.put(name, parseMembers(node, false))
        parseNamespaceExports(it)
      }
      else if (!node.isToken && node.isNamespace) {
        parseNamespace(node)
        parseNamespaceExports(it)
      }
      else parseNamespaceExports(it)
    }
  }

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit = {
    val name = node.symbol.escapedName
    val iterator = node.symbol.exports
    val sub = ns.derive(name)
    parseNamespaceExports(iterator)(sub)
  }
}

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) = new TSSourceFile(sf, global)
}