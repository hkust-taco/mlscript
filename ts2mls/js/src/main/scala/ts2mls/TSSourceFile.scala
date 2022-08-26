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

  private def getSubstitutionArguments[T <: TSAny](args: TSArray[T])(implicit ns: TSNamespace, tv: Set[String]): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(Right(token.typeNode))
      case tp: TSTypeObject => lst :+ getObjectType(Right(tp))
    })

  private def getObjectType(node: Either[TSNodeObject, TSTypeObject])(implicit ns: TSNamespace, tv: Set[String]): TSType = node match {
    case Left(node) => {
      val res: TSType =
        if (node.isFunctionLike) getFunctionType(node)
        else if (node.isTypeParameterSubstitution) TSSubstitutionType(node.typeName.escapedText, getSubstitutionArguments(node.typeArguments))
        else if (node.isTypeParameter()) TSTypeParameter(node.typeName.escapedText)
        else if (node.isSymbolName()) TSNamedType(ns.getParentPath(node.typeName.escapedText))
        else if (node.isEnum) TSEnumType()
        else if (node.isTupleTypeNode) TSTupleType(getTupleElements(node.elements))
        else if (node.isUnionTypeNode) getStructuralType(node.typesToken, true)
        else if (node.isIntersectionTypeNode) getStructuralType(node.types,false)
        else if (node.isArrayTypeNode) TSArrayType(getObjectType(Right(node.elementType.typeNode)))
        else if (node.isAnonymousInterface) TSInterfaceType("", getInterfacePropertiesType(node.members), List(), List())
        else if (node.hasTypeNode) getObjectType(node.`type`) // if the node has a `type` field, it can contain other type information
        else if (node.isDotsArray) TSArrayType(TSNamedType("any")) // variable parameter without type annotation
        else TSNamedType(node.symbol.symbolType) // built-in type
      
      if (node.isOptional) TSUnionType(res, TSNamedType("undefined"))
      else res
    }
    case Right(obj) =>
      if (obj.isEnumType) TSEnumType()
      else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration)
      else if (obj.isTupleType) TSTupleType(getTupleElements(obj.resolvedTypeArguments))
      else if (obj.isUnionType) getStructuralType(obj.types, true)
      else if (obj.isIntersectionType) getStructuralType(obj.types, false)
      else if (obj.isArrayType) TSArrayType(getObjectType(Right(obj.resolvedTypeArguments.get(0))))
      else if (obj.isTypeParameterSubstitution) TSSubstitutionType(obj.symbol.escapedName, getSubstitutionArguments(obj.resolvedTypeArguments))
      else if (obj.isSymbolName()) TSNamedType(ns.getParentPath(obj.symbol.fullName))
      else if (obj.isAnonymousInterface) TSInterfaceType("", getInterfacePropertiesType(obj.declarationMembers), List(), List())
      else if (obj.isTypeParameter()) TSTypeParameter(obj.symbol.escapedName)
      else TSNamedType(obj.intrinsicName)
  }

  private def getTypeConstraints(node: TSNodeObject)(implicit ns: TSNamespace, tv: Set[String]): List[TSTypeParameter] =
    node.typeParameters.foldLeft(List[TSTypeParameter]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeParameter(tp.symbol.escapedName, None)
      else lst :+ TSTypeParameter(tp.symbol.escapedName, Some(getObjectType(Right(tp.constraint.typeNode))))
    )

  private def constaintsListToSet(constraints: List[TSTypeParameter]) =
    constraints.map((c) => c.name).toSet

  private def getFunctionType(node: TSNodeObject)(implicit ns: TSNamespace, tv: Set[String]): TSFunctionType = {
    val constraints = getTypeConstraints(node)
    val ntv = constaintsListToSet(constraints) ++ tv
    // in typescript, you can use `this` to explicitly specifies the callee
    // but it never appears in the final javascript file
    val pList = node.parameters.foldLeft(List[TSType]())((lst, p) => lst :+
      (if (p.symbol.escapedName.equals("this")) TSNamedType("void") else getObjectType(Left(p))(ns, ntv)))
    TSFunctionType(pList, getObjectType(Right(node.returnType))(ns, ntv), constraints)
  }

  private def getStructuralType[T <: TSAny](types: TSArray[T], isUnion: Boolean)(implicit ns: TSNamespace, tv: Set[String]): TSStructuralType = 
    types.foldLeft[Option[TSType]](None)((prev, cur) => prev match {
      case None => cur match {
        case token: TSTokenObject => Some(getObjectType(Right(token.typeNode)))
        case tp: TSTypeObject => Some(getObjectType(Right(tp)))
        case node: TSNodeObject => Some(getObjectType(Left(node)))
      }
      case Some(p) => cur match {
        case token: TSTokenObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(Right(token.typeNode)))) else Some(TSIntersectionType(p, getObjectType(Right(token.typeNode))))
        case tp: TSTypeObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(Right(tp)))) else Some(TSIntersectionType(p, getObjectType(Right(tp))))
        case node: TSNodeObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(Left(node)))) else Some(TSIntersectionType(p, getObjectType(Left(node))))
      }
    }).get.asInstanceOf[TSStructuralType]

  private def getTupleElements[T <: TSAny](elements: TSArray[T])(implicit ns: TSNamespace, tv: Set[String]): List[TSType] =
    elements.foldLeft(List[TSType]())((lst, ele) => ele match {
      case token: TSTokenObject => lst :+ getObjectType(Right(token.typeNode))
      case tp: TSTypeObject => lst :+ getObjectType(Right(tp))
    })

  private def getHeritageList(node: TSNodeObject)(implicit ns: TSNamespace, tv: Set[String]): List[TSType] = {
    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) => {
      val parent = h.types.get(index)
      val name = ns.getParentPath(parent.fullName)
      if (parent.typeArguments.isUndefined) lst :+ TSNamedType(name)
      else lst :+ TSSubstitutionType(name, getSubstitutionArguments(parent.typeArguments))
    })
  }

  private def getClassMembersType(list: TSNodeArray, requireStatic: Boolean)(implicit ns: TSNamespace, tv: Set[String]): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      val name = p.symbol.escapedName

      // TODO: support `__constructor`
      if (!name.equals("__constructor") && p.isStatic == requireStatic) {
        val mem =
          if (!p.isStatic) getObjectType(Left(p))
          else parseMembers(p.initializer, true)

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

  private def getInterfacePropertiesType(list: TSNodeArray)(implicit ns: TSNamespace, tv: Set[String]): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => mp ++ Map(p.symbol.escapedName -> TSMemberType(getObjectType(Left(p)))))

  private def parseMembers(node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace, tv: Set[String]): TSType = {
    val name = node.symbol.escapedName
    val members = node.members
    val constraints = getTypeConstraints(node)(ns, Set())
    val tvMap = tv ++ constaintsListToSet(constraints)

    val fullName = ns.getFullPath(name)
    if (isClass)
      TSClassType(fullName, getClassMembersType(members, false)(ns, tvMap), getClassMembersType(members, true)(ns, tvMap), constraints, getHeritageList(node)(ns, tvMap))
    else TSInterfaceType(fullName, getInterfacePropertiesType(members)(ns, tvMap), constraints, getHeritageList(node)(ns, tvMap))
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
        val typeInfo = getFunctionType(node)(ns, Set())
        addFunctionIntoNamespace(typeInfo, node, name)
      }
      case Some(decs) => {
        decs.foreach((d) => {
          val func = getFunctionType(d)(ns, Set())
          addFunctionIntoNamespace(func, d, name)
        })
      }
    }
    else if (node.isClassDeclaration) {
      ns.put(name, TSNamedType(name)) // placeholder for self-reference
      val typeInfo = parseMembers(node, true)(ns, Set())
      ns.put(name, typeInfo)
    }
    else if (node.isInterfaceDeclaration) {
      ns.put(name, TSNamedType(name)) // placeholder for self-reference
      val typeInfo = parseMembers(node, false)(ns, Set())
      ns.put(name, typeInfo)
    }
    else if (node.isNamespace) {
      parseNamespace(node)(ns)
    }

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit =
    parseNamespaceLocals(node.locals)(ns.derive(node.symbol.escapedName))
}