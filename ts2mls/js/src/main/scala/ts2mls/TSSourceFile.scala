package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import types._
import mlscript.utils._
import scala.collection.mutable.{ListBuffer, HashMap}

class TSSourceFile(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) {
  private val lineHelper = new TSLineStartsHelper(sf.getLineStarts())
  private val importList = TSImportList()
  private val resolvedPath = sf.resolvedPath.toString()
  private val originalFileName = sf.originalFileName.toString()
  private val rootPath =
    resolvedPath.substring(0, resolvedPath.length() - originalFileName.length()) +
    originalFileName.substring(0, originalFileName.lastIndexOf("/") + 1)

  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isImportDeclaration)
      parseImportDeclaration(nodeObject.importClause, nodeObject.moduleSpecifier, false)
  })

  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (!nodeObject.isToken) {
      if (!nodeObject.symbol.isUndefined) // for functions/classes/interfaces
        addNodeIntoNamespace(nodeObject, nodeObject.symbol.escapedName, nodeObject.isExported)(global)
      else if (!nodeObject.declarationList.isUndefined) { // for variables
        val decNode = nodeObject.declarationList.declaration
        addNodeIntoNamespace(decNode, decNode.symbol.escapedName, decNode.isExported)(global)
      }
    }
  })

  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isExportDeclaration) {
      if (!nodeObject.moduleSpecifier.isUndefined) // re-export
        parseImportDeclaration(nodeObject.exportClause, nodeObject.moduleSpecifier, true)
      else
        parseExportDeclaration(nodeObject.exportClause.elements)
    }
  })

  def getImportList: List[String] = importList.getFilelist

  private def parseExportDeclaration(elements: TSNodeArray): Unit = {
    def getReferedType(name: String): TSType = global.get(name) match {
      case cls: TSClassType => TSReferenceType(cls.name)
      case TSEnumType => TSEnumType
      case itf: TSInterfaceType => TSReferenceType(itf.name)
      case ref: TSReferenceType => ref
      case _ => throw new AssertionError(s"unsupported export type $name.") // FIXME: functions and variables?
    }
    elements.foreach(ele =>
      if (ele.propertyName.isUndefined)
        global.export(ele.symbol.escapedName)
      else {
        val alias = ele.symbol.escapedName
        global.put(alias, TSTypeAlias(alias, getReferedType(ele.propertyName.escapedText), Nil), true)
      }
    )
  }

  private def parseImportDeclaration(clause: TSNodeObject, moduleSpecifier: TSTokenObject, exported: Boolean): Unit = {
    // ignore `import "filename.ts"`
    if (!clause.isUndefined) {
      val bindings = clause.namedBindings
      val absPath =
        if (moduleSpecifier.text.startsWith("./"))
          rootPath + moduleSpecifier.text.substring(2)
        else moduleSpecifier.text // TODO: node_module?
      def run(node: TSNodeObject): Unit =
        if (!node.elements.isUndefined) {
          val list = node.elements.mapToList(ele =>
            if (ele.propertyName.isUndefined) 
              (ele.symbol.escapedName, None)
            else
              (ele.propertyName.escapedText, Some(ele.symbol.escapedName))
          )
          val imp = TSSingleImport(absPath, list)
          if (exported) imp.createAlias.foreach { // FIXME: functions and variables?
            case alias @ TSTypeAlias(name, _, _) => global.put(name, alias, true)
          }
          importList += imp
        }
        else if (!node.name.isUndefined) {
          val imp = TSFullImport(absPath, node.name.escapedText)
          if (exported) imp.createAlias.foreach { // FIXME: functions and variables?
            case alias @ TSTypeAlias(name, _, _) => global.put(name, alias, true)
          }
          importList += imp
        }

      if (!bindings.isUndefined) run(bindings)
      else run(clause)
    }
  }

  private def getSubstitutionArguments[T <: TSAny](args: TSArray[T]): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(token.typeNode)
      case tp: TSTypeObject => lst :+ getObjectType(tp)
    })

  private def getSymbolFullname(sym: TSSymbolObject): String =
    if (!sym.parent.isUndefined && sym.parent.declaration.isSourceFile)
      importList.resolveTypeAlias(sym.parent.declaration.symbol.escapedName.replaceAll("\"", ""), sym.escapedName)
    else if (sym.parent.isUndefined || !sym.parent.declaration.isNamespace) sym.escapedName
    else s"${getSymbolFullname(sym.parent)}.${sym.escapedName}"

  private def getObjectType(obj: TSTypeObject): TSType =
    if (obj.isMapped) lineHelper.getPos(obj.pos) match {
        case (line, column) => TSUnsupportedType(obj.toString(), obj.filename, line, column)
      }
    else if (obj.isEnumType) TSEnumType
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration)
    else if (obj.isTupleType) TSTupleType(getTupleElements(obj.typeArguments))
    else if (obj.isUnionType) getStructuralType(obj.types, true)
    else if (obj.isIntersectionType) getStructuralType(obj.types, false)
    else if (obj.isArrayType) TSArrayType(getObjectType(obj.elementTypeOfArray))
    else if (obj.isTypeParameterSubstitution) TSSubstitutionType(obj.symbol.escapedName, getSubstitutionArguments(obj.typeArguments))
    else if (obj.isObject)
      if (obj.isAnonymous) TSInterfaceType("", getAnonymousPropertiesType(obj.properties), List(), List())
      else TSReferenceType(getSymbolFullname(obj.symbol))
    else if (obj.isTypeParameter) TSTypeParameter(obj.symbol.escapedName)
    else if (obj.isConditionalType || obj.isIndexType || obj.isIndexedAccessType) lineHelper.getPos(obj.pos) match {
      case (line, column) => TSUnsupportedType(obj.toString(), obj.filename, line, column)
    }
    else TSPrimitiveType(obj.intrinsicName)

  // the function `getMemberType` can't process function/tuple type alias correctly
  private def getTypeAlias(tn: TSNodeObject): TSType =
    if (tn.isFunctionLike) getFunctionType(tn)
    else if (tn.isTupleTypeNode) TSTupleType(getTupleElements(tn.typeNode.typeArguments))
    else getObjectType(tn.typeNode) match {
      case TSPrimitiveType("intrinsic") => lineHelper.getPos(tn.pos) match {
        case (line, column) => TSUnsupportedType(tn.toString(), tn.filename, line, column)
      }
      case t => t
    }

  // parse string/numeric literal types. we need to add quotes if it is a string literal
  private def getLiteralType(tp: TSNodeObject) =
    TSLiteralType(tp.literal.text, tp.literal.isStringLiteral)

  // parse object literal types
  private def getObjectLiteralMembers(props: TSNodeArray) =
    props.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      mp ++ Map(p.name.escapedText -> TSMemberType(TSLiteralType(p.initToken.text, p.initToken.isStringLiteral)))
    })

  // get the type of variables in classes/named interfaces/anonymous interfaces
  private def getMemberType(node: TSNodeObject): TSType = {
    val res: TSType =
      if (node.isIndexSignature || node.isCallSignature || node.isConstructSignature)
        lineHelper.getPos(node.pos) match {
          case (line, column) => TSUnsupportedType(node.toString(), node.filename, line, column)
        }
      else if (node.isFunctionLike) getFunctionType(node)
      else if (node.`type`.isUndefined) getObjectType(node.typeAtLocation)
      else if (node.`type`.isLiteralTypeNode) getLiteralType(node.`type`)
      else getObjectType(node.`type`.typeNode)
    if (node.symbol.isOptionalMember) TSUnionType(res, TSPrimitiveType("undefined"))
    else res
  }

  private def getTypeParameters(node: TSNodeObject): List[TSTypeParameter] =
    node.typeParameters.foldLeft(List[TSTypeParameter]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeParameter(tp.symbol.escapedName, None)
      else lst :+ TSTypeParameter(tp.symbol.escapedName, Some(getObjectType(tp.constraint.typeNode)))
    )

  private def getFunctionType(node: TSNodeObject): TSFunctionType = {
    val pList = node.parameters.foldLeft(List[TSParameterType]())((lst, p) => (
      // in typescript, you can use `this` to explicitly specifies the callee
      // but it never appears in the final javascript file
      if (p.symbol.escapedName === "this") lst
      else if (p.isOptionalParameter)
        lst :+ TSParameterType(p.symbol.escapedName, TSUnionType(getObjectType(p.symbolType), TSPrimitiveType("undefined")))
      else lst :+ TSParameterType(p.symbol.escapedName, getObjectType(p.symbolType)))
    )
    TSFunctionType(pList, getObjectType(node.returnType), getTypeParameters(node))
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

  private def addMember(mem: TSType, node: TSNodeObject, name: String, others: Map[String, TSMemberType]): Map[String, TSMemberType] = mem match {
    case func: TSFunctionType => {
      if (!others.contains(name)) others ++ Map(name -> TSMemberType(func, node.modifier))
      else { // deal with functions overloading
        val old = others(name)
        val res = old.base match {
          case f @ TSFunctionType(_, _, tv) =>
            if (!tv.isEmpty || !func.typeVars.isEmpty) TSIgnoredOverload(func, name)
            else if (!node.isImplementationOfOverload) TSIntersectionType(f, func)
            else f
          case int: TSIntersectionType =>
            if (!func.typeVars.isEmpty) TSIgnoredOverload(func, name)
            else if (!node.isImplementationOfOverload) TSIntersectionType(int, func)
            else int
          case TSIgnoredOverload(_, name) => TSIgnoredOverload(func, name) // the implementation is always after declarations
          case _ => old.base
        }
        others.removed(name) ++ Map(name -> TSMemberType(res, node.modifier))
      }
    }
    case _ => others ++ Map(name -> TSMemberType(mem, node.modifier))
  }

  private def getClassMembersType(list: TSNodeArray, requireStatic: Boolean): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      val name = p.symbol.escapedName

      if (name =/= "__constructor" && p.isStatic == requireStatic) {
        val mem =
          if (!p.isStatic) getMemberType(p)
          else parseMembers(name, p.initializer, true)
        addMember(mem, p, name, mp)
      }
      else mp
    })

  private def getConstructorList(members: TSNodeArray): List[TSParameterType] =
    members.foldLeft(List[TSParameterType]())((lst, mem) => {
      val name = mem.symbol.escapedName

      if (name =/= "__constructor") lst
      else mem.parameters.foldLeft(List[TSParameterType]())((res, p) =>
        res :+ TSParameterType(p.symbol.escapedName, getMemberType(p)))
    })

  private def getInterfacePropertiesType(list: TSNodeArray): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => addMember(getMemberType(p), p, p.symbol.escapedName, mp))

  private def getAnonymousPropertiesType(list: TSSymbolArray): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) =>
      mp ++ Map(p.escapedName -> TSMemberType(if (p.`type`.isUndefined) getMemberType(p.declaration) else getObjectType(p.`type`))))

  private def parseMembers(name: String, node: TSNodeObject, isClass: Boolean): TSType =
    if (isClass)
      TSClassType(name, getClassMembersType(node.members, false), getClassMembersType(node.members, true),
        getTypeParameters(node), getHeritageList(node), getConstructorList(node.members))
    else TSInterfaceType(name, getInterfacePropertiesType(node.members), getTypeParameters(node), getHeritageList(node))

  private def parseNamespaceLocals(map: TSSymbolMap, exports: TSSymbolMap)(implicit ns: TSNamespace) =
    map.foreach((sym) => {
      val node = sym.declaration
      val name = sym.escapedName
      if (!node.isToken)
        addNodeIntoNamespace(node, name, exports.contains(name), if (node.isFunctionLike) Some(sym.declarations) else None)
    })

  private def addFunctionIntoNamespace(fun: TSFunctionType, node: TSNodeObject, name: String)(implicit ns: TSNamespace) =
    if (!ns.containsMember(name, false)) ns.put(name, fun, node.isExported)
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
      
      ns.put(name, res, node.isExported)
    } 

  // overload functions in a sub-namespace need to provide an overload array
  // because the namespace merely exports symbols rather than node objects themselves
  private def addNodeIntoNamespace(node: TSNodeObject, name: String, exported: Boolean, overload: Option[TSNodeArray] = None)(implicit ns: TSNamespace) =
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
      ns.put(name, parseMembers(name, node, true), exported)
    else if (node.isInterfaceDeclaration)
      ns.put(name, parseMembers(name, node, false), exported)
    else if (node.isTypeAliasDeclaration)
      ns.put(name, TSTypeAlias(name, getTypeAlias(node.`type`), getTypeParameters(node)), exported)
    else if (node.isObjectLiteral)
      ns.put(name, TSInterfaceType("", getObjectLiteralMembers(node.initializer.properties), List(), List()), exported)
    else if (node.isVariableDeclaration) ns.put(name, getMemberType(node), exported)
    else if (node.isNamespace)
      parseNamespace(node)

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit =
    parseNamespaceLocals(node.locals, node.exports)(ns.derive(node.symbol.escapedName, node.isExported))
}

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker) =
    new TSSourceFile(sf, global)
}
