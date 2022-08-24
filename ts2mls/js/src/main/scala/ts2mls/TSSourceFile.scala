package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
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

  private def getApplicationArguments[T <: TSAny](args: TSArray[T])(implicit ns: TSNamespace, tv: Set[String]): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(Right(token.getTypeFromTypeNode()))
      case tp: TSTypeObject => lst :+ getObjectType(Right(tp))
    })

  // due to the tsc's code, the type information can be stored everywhere
  // all these branches are required. removing one of them would lead to errors
  private def getObjectType(node: Either[TSNodeObject, TSTypeObject])(implicit ns: TSNamespace, tv: Set[String]): TSType = node match {
    case Left(node) => {
      val res: TSType =
        if (node.isFunctionLike) getFunctionType(node)
        else if (node.hasTypeName) { // `typeName` may contain the name of class/interface/type variable/ enum
          val name = node.typeName.escapedText()
          if (!node.typeArguments.isUndefined && node.typeArguments.length > 0)
            TSApplicationType(name, getApplicationArguments(node.typeArguments))
          else if (tv(name)) TSTypeVariable(name)
          else if (ns.containsMember(name.split("'").toList)) TSNamedType(name)
          else TSEnumType(name)
        }
        else if (node.isTupleTypeNode) TSTupleType(getTupleElements(node.elements))
        else if (node.isUnionTypeNode) getStructuralType(node.typesToken, true)
        else if (node.isIntersectionTypeNode) getStructuralType(node.types,false)
        else if (node.isArrayTypeNode) TSArrayType(getObjectType(Right(node.elementType.getTypeFromTypeNode())))
        else if (!node.members.isUndefined) // anonymous interface 
          TSInterfaceType("", getInterfacePropertiesType(node.members, 0), List(), List())
        else if (!node.`type`.isUndefined) // if the node has a `type` field, it can contain other type information
          if (!node.`type`.isToken) getObjectType(Left(node.`type`))
          else getObjectType(Right(node.`type`.token.getTypeFromTypeNode()))
        else if (!node.dotDotDot.isUndefined) TSArrayType(TSNamedType("any")) // variable parameter without type annotation
        else {
          val name = node.symbol.getType()
          if (tv(name)) TSTypeVariable(name) else TSNamedType(name)
        }
      
      // if this parameter is optional (with question mark or has an initial value)
      if (node.questionToken.isUndefined && node.initializer.isUndefined) res
      else res match {
        case TSNamedType(name) if (name.equals("undefined")) => res
        case _ => TSUnionType(res, TSNamedType("undefined"))
      }
    }
    case Right(obj) => {
      val sym = obj.symbol
      val dec = sym.declaration
      val args = obj.resolvedTypeArguments
      if (obj.isEnumType) TSEnumType(obj.aliasSymbol.escapedName)
      else if (dec.isFunctionLike) getFunctionType(dec)
      else if (obj.isTupleType) TSTupleType(getTupleElements(args))
      else if (obj.isUnionType) getStructuralType(obj.types, true)
      else if (obj.isIntersectionType) getStructuralType(obj.types, false)
      else if (obj.isArrayType) TSArrayType(getObjectType(Right(args.get(0))))
      else if (!args.isUndefined && args.length > 0) TSApplicationType(sym.escapedName, getApplicationArguments(args))
      else if (!sym.isUndefined) {
          val symDec = sym.valueDeclaration
          val name = sym.getFullName()
          if (ns.containsMember(name.split("'").toList)) TSNamedType(name)
          // there are two ways to store anonymous interface in TypeObject
          else if (!symDec.isUndefined && !symDec.properties.isUndefined)
            TSInterfaceType("", getInterfacePropertiesType(symDec.properties, 0), List(), List())
          else if (!dec.isUndefined && !dec.members.isUndefined)
            TSInterfaceType("", getInterfacePropertiesType(dec.members, 0), List(), List())
          else if (tv(sym.escapedName)) TSTypeVariable(sym.escapedName)
          else TSNamedType(name)
      }
      else if(tv(obj.intrinsicName)) TSTypeVariable(obj.intrinsicName)
      else TSNamedType(obj.intrinsicName)
    }
  }

  private def getTypeConstraints(node: TSNodeObject)(implicit ns: TSNamespace, tv: Set[String]): List[TSTypeVariable] =
    node.typeParameters.foldLeft(List[TSTypeVariable]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeVariable(tp.symbol.escapedName, None)
      else lst :+ TSTypeVariable(tp.symbol.escapedName, Some(getObjectType(Right(tp.constraint.getTypeFromTypeNode()))))
    )

  private def constaintsListToSet(constraints: List[TSTypeVariable]) =
    constraints.map((c) => c.name).toSet

  private def getFunctionType(node: TSNodeObject)(implicit ns: TSNamespace, tv: Set[String]): TSFunctionType = {
    val constraints = getTypeConstraints(node)
    val ntv = constaintsListToSet(constraints) ++ tv
    // in typescript, you can use `this` to explicitly specifies the callee
    // but it never appears in the final javascript file
    val pList = node.parameters.foldLeft(List[TSType]())((lst, p) => lst :+
      (if (p.symbol.escapedName.equals("this")) TSNamedType("void") else getObjectType(Left(p))(ns, ntv)))
    val res = node.getReturnTypeOfSignature()
    TSFunctionType(pList, getObjectType(Right(res))(ns, ntv), constraints)
  }

  private def getStructuralType[T <: TSAny](types: TSArray[T], isUnion: Boolean)(implicit ns: TSNamespace, tv: Set[String]): TSStructuralType = 
    types.foldLeft[Option[TSType]](None)((prev, cur) => prev match {
      case None => cur match {
        case token: TSTokenObject => Some(getObjectType(Right(token.getTypeFromTypeNode())))
        case tp: TSTypeObject => Some(getObjectType(Right(tp)))
        case node: TSNodeObject => Some(getObjectType(Left(node)))
      }
      case Some(p) => cur match {
        case token: TSTokenObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(Right(token.getTypeFromTypeNode())))) else Some(TSIntersectionType(p, getObjectType(Right(token.getTypeFromTypeNode()))))
        case tp: TSTypeObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(Right(tp)))) else Some(TSIntersectionType(p, getObjectType(Right(tp))))
        case node: TSNodeObject =>
          if (isUnion) Some(TSUnionType(p, getObjectType(Left(node)))) else Some(TSIntersectionType(p, getObjectType(Left(node))))
      }
    }).get.asInstanceOf[TSStructuralType]

  private def getTupleElements[T <: TSAny](elements: TSArray[T])(implicit ns: TSNamespace, tv: Set[String]): List[TSType] =
    elements.foldLeft(List[TSType]())((lst, ele) => ele match {
      case token: TSTokenObject => lst :+ getObjectType(Right(token.getTypeFromTypeNode()))
      case tp: TSTypeObject => lst :+ getObjectType(Right(tp))
    })

  private def getInheritList(node: TSNodeObject)(implicit ns: TSNamespace, tv: Set[String]): List[TSType] = {
    // get parent's full name with namespaces
    def getFullName(name: String, exp: Either[TSNodeObject, TSIdentifierObject]): String =
      exp match {
        case Left(node) =>
          if (name.equals("")) getFullName(node.name.escapedText(), node.expression)
          else getFullName(s"${node.name.escapedText()}'$name", node.expression)
        case Right(id) =>
          if (name.equals("")) id.escapedText()
          else s"${id.escapedText()}'$name"
      }

    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) => {
      val parent = h.types.get(index)
      val name = getFullName("", parent.expression)
      if (parent.typeArguments.isUndefined) lst :+ TSNamedType(name)
      else lst :+ TSApplicationType(name, getApplicationArguments(parent.typeArguments))
    })
  }

  private def getClassMembersType(list: TSNodeArray, index: Int, requireStatic: Boolean)(implicit ns: TSNamespace, tv: Set[String]): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      val name = p.symbol.escapedName
      val isStatic = if (p.modifiers.isUndefined) false
                     else p.modifiers.foldLeft(false)((s, t) => t.isStatic)

      // TODO: support `__constructor`
      if (!name.equals("__constructor") && isStatic == requireStatic) {
        val initializer = p.initializerNode
        val mem =
          if (initializer.isUndefined || initializer.members.isUndefined) getObjectType(Left(p)) // non-static members
          else parseMembers(initializer, true) // static members
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

  private def getInterfacePropertiesType(list: TSNodeArray, index: Int)(implicit ns: TSNamespace, tv: Set[String]): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => mp ++ Map(p.symbol.escapedName -> TSMemberType(getObjectType(Left(p)))))

  private def parseMembers(node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace, tv: Set[String]): TSType = {
    val name = node.symbol.escapedName
    val members = node.members
    val constraints = getTypeConstraints(node)(ns, Set())
    val tvMap = tv ++ constaintsListToSet(constraints)

    val fullName = ns.getFullPath(name)
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
      case old: TSFunctionType if (node.body.isUndefined) => // the signature of overload function
        ns.put(name, TSIntersectionType(old, fun))
      case old: TSIntersectionType if (node.body.isUndefined) => // the signature of overload function
        ns.put(name, TSIntersectionType(old, fun))
      case _ => {} // the implementation of the overload function. the type of this function may be wider, so just ignore it
    }

  // overload functions in a sub-namespace need to provide an overload array
  // because the namespace merely exports symbols rather than node objects themselves
  private def addNodeIntoNamespace(node: TSNodeObject, name: String, overload: Option[TSNodeArray] = None)(implicit ns: TSNamespace) =
    if (node.isFunctionDeclaration) overload match {
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