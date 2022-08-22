package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import types._

class TSSourceFile(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) {
  private def visit(node: js.Dynamic): Unit = {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isToken || nodeObject.symbol.isUndefined) return

    val name = nodeObject.symbol.escapedName
    addNodeIntoNamespace(nodeObject, name)(global)
  }

  TypeScript.forEachChild(sf, visit)

  private def getApplicationArguments[T <: TSAny](args: TSArray[T])(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(token.getTypeFromTypeNode)
      case tp: TSTypeObject => lst :+ getObjectType(tp)
    })

  private def getObjectType(node: TSTypeSource)(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): TSType = node match {
    case node: TSNodeObject => {
      val res = {
        val typeNode = node.`type`
        if (typeNode.isFunctionLike) getFunctionType(typeNode)
        else if (node.isFunctionLike) getFunctionType(node)
        else if (typeNode.hasTypeName) {
          val name = typeNode.typeName.escapedText
          if (!typeNode.typeArguments.isUndefined)
            TSApplicationType(name, getApplicationArguments(typeNode.typeArguments))
          else if (tv.contains(name)) tv(name)
          else if (ns.containsMember(name.split("'").toList)) TSNamedType(name)
          else TSEnumType(name)
        }
        else if (typeNode.isTupleTypeNode) TSTupleType(getTupleElements(typeNode.elements))
        else if (node.isTupleTypeNode) TSTupleType(getTupleElements(node.elements))
        else if (typeNode.isUnionTypeNode) getStructuralType(typeNode.typesToken, true)
        else if (typeNode.isIntersectionTypeNode) getStructuralType(typeNode.types,false)
        else if (typeNode.isArrayTypeNode) TSArrayType(getObjectType(typeNode.elementType.getTypeFromTypeNode))
        else if (node.isArrayTypeNode) TSArrayType(getObjectType(node.elementType.getTypeFromTypeNode))
        else if (node.hasTypeName)
          tv.getOrElse(node.typeName.escapedText, TSNamedType(node.typeName.escapedText))
        else if (!typeNode.isUndefined && !typeNode.members.isUndefined)
          TSInterfaceType("", getInterfacePropertiesType(typeNode.members, 0), List(), List())
        else if (!node.dotDotDot.isUndefined) TSArrayType(TSNamedType("any"))
        else {
          val name = node.symbol.getType
          tv.getOrElse(name, TSNamedType(name))
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
      if (obj.isEnumType) TSEnumType(obj.aliasSymbol.escapedName)
      else if (dec.isFunctionLike) getFunctionType(dec)
      else if (obj.isTupleType) TSTupleType(getTupleElements(args))
      else if (obj.isUnionType) getStructuralType(obj.types, true)
      else if (obj.isIntersectionType) getStructuralType(obj.types, false)
      else if (obj.isArrayType) TSArrayType(getObjectType(args.get(0)))
      else if (!args.isUndefined) TSApplicationType(obj.symbol.escapedName, getApplicationArguments(args))
      else if (!obj.symbol.isUndefined) {
          val symDec = obj.symbol.valueDeclaration
          val name = obj.symbol.getFullName
          if (ns.containsMember(name.split("'").toList)) TSNamedType(name)
          else if (!symDec.isUndefined && !symDec.properties.isUndefined)
            TSInterfaceType("", getInterfacePropertiesType(symDec.properties, 0), List(), List())
          else if (!dec.isUndefined && !dec.members.isUndefined)
            TSInterfaceType("", getInterfacePropertiesType(dec.members, 0), List(), List())
          else tv.getOrElse(obj.symbol.escapedName, TSNamedType(obj.symbol.getFullName)) 
      }
      else tv.getOrElse(obj.intrinsicName, TSNamedType(obj.intrinsicName))
    }
  }

  private def getTypeConstraints(node: TSNodeObject)(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): List[TSTypeVariable] = {
    node.typeParameters.foldLeft(List[TSTypeVariable]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeVariable(tp.symbol.escapedName, None)
      else lst :+ TSTypeVariable(tp.symbol.escapedName, Some(getObjectType(tp.constraint.getTypeFromTypeNode)))
    )
  }

  private def constaintsListToMap(constraints: List[TSTypeVariable]) =
    constraints.foldLeft(Map[String, TSTypeVariable]())((m, v) => 
      m ++ Map(v.name -> TSTypeVariable(v.name, None)) // we will apply the constraints in the record declarations.
    )

  private def getFunctionType(node: TSNodeObject)(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): TSFunctionType = {
    val params = node.parameters
    val constraints = getTypeConstraints(node)
    val ntv = constaintsListToMap(constraints) ++ tv
    val pList = params.foldLeft(List[TSType]())((lst, p) => lst :+ getObjectType(p)(ns, ntv))
    val res = node.getReturnTypeOfSignature()
    TSFunctionType(pList, getObjectType(res)(ns, ntv), constraints)
  }

  private def getStructuralType[T <: TSAny](types: TSArray[T], isUnion: Boolean)(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): TSStructuralType = 
    types.foldLeft[Option[TSType]](None)((prev, cur) => prev match {
      case None => cur match {
        case token: TSTokenObject => Some(getObjectType(token.getTypeFromTypeNode))
        case tp: TSTypeObject => Some(getObjectType(tp))
        case node: TSNodeObject => Some(getObjectType(node))
      }
      case Some(p) => cur match {
        case token: TSTokenObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(token.getTypeFromTypeNode))) else Some(TSIntersectionType(p, getObjectType(token.getTypeFromTypeNode)))
        case tp: TSTypeObject => Some()
          if (isUnion) Some(TSUnionType(p, getObjectType(tp))) else Some(TSIntersectionType(p, getObjectType(tp)))
        case node: TSNodeObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(node))) else Some(TSIntersectionType(p, getObjectType(node)))
      }
    }).get.asInstanceOf[TSStructuralType]

  private def getTupleElements[T <: TSAny](elements: TSArray[T])(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): List[TSType] =
    elements.foldLeft(List[TSType]())((lst, ele) => ele match {
      case token: TSTokenObject => lst :+ getObjectType(token.getTypeFromTypeNode)
      case tp: TSTypeObject => lst :+ getObjectType(tp)
    })

  private def getInheritList(node: TSNodeObject)(implicit ns: TSNamespace): List[TSType] = {
    def getFullName(name: String, exp: Either[TSNodeObject, TSIdentifierObject]): String =
      exp match {
        case Left(node) =>
          if (name.equals("")) getFullName(node.name.escapedText, node.expression)
          else getFullName(s"${node.name.escapedText}'$name", node.expression)
        case Right(id) =>
          if (name.equals("")) id.escapedText
          else s"${id.escapedText}'$name"
      }

    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) => {
      val parent = h.types.get(index)
      val name = getFullName("", parent.expression)
      if (parent.typeArguments.isUndefined) lst :+ TSNamedType(name)
      else lst :+ TSApplicationType(name, getApplicationArguments(parent.typeArguments)(ns, Map()))
    })
  }

  private def getClassMembersType(list: TSNodeArray, index: Int, requireStatic: Boolean)(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      val name = p.symbol.escapedName
      val isStatic = if (p.modifiers.isUndefined) false
                     else p.modifiers.foldLeft(false)((s, t) => t.isStatic)

      if (!name.equals("__constructor") && isStatic == requireStatic) {
        val initializer = p.initializerNode
        val mem =
          if (initializer.isUndefined || initializer.members.isUndefined) getObjectType(p)
          else parseMembers(initializer, true)
        val modifier = if (p.modifiers.isUndefined) Public
          else p.modifiers.foldLeft[TSAccessModifier](Public)((m, t) =>
            if (t.isPrivate) Private else if (t.isProtected) Protected else m
          )

        mem match {
          case func: TSFunctionType => {
            if (!mp.contains(name)) mp ++ Map(name -> TSMemberType(func, modifier))
            else mp(name).base match {
              case old: TSFunctionType if (p.body.isUndefined) =>
                mp.removed(name) ++ Map(name -> TSMemberType(TSIntersectionType(old, func), modifier))
              case old: TSIntersectionType if (p.body.isUndefined) =>
                mp.removed(name) ++ Map(name -> TSMemberType(TSIntersectionType(old, func), modifier))
              case _ => mp
            }
          }
          case _ => mp ++ Map(name -> TSMemberType(mem, modifier))
        }
      }
      else mp
    })

  private def getInterfacePropertiesType(list: TSNodeArray, index: Int)(implicit ns: TSNamespace, tv: Map[String, TSTypeVariable]): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => mp ++ Map(p.symbol.escapedName -> TSMemberType(getObjectType(p))))

  private def parseMembers(node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace): TSType = {
    val name = node.symbol.escapedName
    val members = node.members
    val constraints = getTypeConstraints(node)(ns, Map())
    val tvMap = constaintsListToMap(constraints)

    val nsName = ns.getFullName
    val fullName = if (nsName.equals("")) name else s"$nsName'$name"    

    if (isClass)
      TSClassType(fullName, getClassMembersType(members, 0, false)(ns, tvMap), getClassMembersType(members, 0, true)(ns, tvMap), constraints, getInheritList(node))
    else TSInterfaceType(fullName, getInterfacePropertiesType(members, 0)(ns, tvMap), constraints, getInheritList(node))
  }

  private def parseNamespaceLocals(map: TSSymbolMap)(implicit ns: TSNamespace) =
    map.foreach((sym) => {
      val name = sym.escapedName
      val node = sym.declaration
      if (!node.isToken)
        addNodeIntoNamespace(node, name, if (node.isFunctionDeclaration) Some(sym.declarations) else None)
    })

  private def addFunctionIntoNamespace(fun: TSFunctionType, node: TSNodeObject, name: String)(implicit ns: TSNamespace) =
    if (!ns.containsMember(name, false)) ns.put(name, fun)
    else ns.get(name) match {
      case old: TSFunctionType if (node.body.isUndefined) =>
        ns.put(name, TSIntersectionType(old, fun))
      case old: TSIntersectionType if (node.body.isUndefined) =>
        ns.put(name, TSIntersectionType(old, fun))
      case _ => {}
    }

  private def addNodeIntoNamespace(node: TSNodeObject, name: String, overload: Option[TSNodeArray] = None)(implicit ns: TSNamespace) =
    if (node.isFunctionDeclaration) overload match {
      case None => {
        val typeInfo = getFunctionType(node)(ns, Map())
        addFunctionIntoNamespace(typeInfo, node, name)
      }
      case Some(decs) => {
        decs.foreach((d) => {
          val func = getFunctionType(d)(ns, Map())
          addFunctionIntoNamespace(func, d, name)
        })
      }
    }
    else if (node.isClassDeclaration) {
      ns.put(name, TSNamedType(name)) // placeholder for self reference
      val typeInfo = parseMembers(node, true)(ns)
      ns.put(name, typeInfo)
    }
    else if (node.isInterfaceDeclaration) {
      ns.put(name, TSNamedType(name)) // placeholder for self reference
      val typeInfo = parseMembers(node, false)(ns)
      ns.put(name, typeInfo)
    }
    else if (node.isNamespace) {
      parseNamespace(node)(ns)
    }

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit = {
    val name = node.symbol.escapedName
    val locals = node.locals
    val sub = ns.derive(name)
    parseNamespaceLocals(locals)(sub)
  }
}

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) = new TSSourceFile(sf, global)
}