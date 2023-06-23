package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import types._
import mlscript.utils._
import scala.collection.mutable.{ListBuffer, HashMap}
import ts2mls.TSPathResolver

class TSSourceFile(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker, config: js.Dynamic) {
  private val lineHelper = new TSLineStartsHelper(sf.getLineStarts())
  private val importList = TSImportList()
  private val reExportList = new ListBuffer[TSReExport]()
  private val resolvedPath = sf.resolvedPath.toString()

  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isRequire)
      parseRequire(nodeObject)
    else if (nodeObject.isImportDeclaration)
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
    else if (nodeObject.isExportAssignment) {
      val name = nodeObject.idExpression.escapedText
      global.`export`(name)
    }
  })

  def getImportList: List[TSImport] = importList.getFilelist
  def getReExportList: List[TSReExport] = reExportList.toList

  private def parseRequire(req: TSNodeObject): Unit = {
    val localName = req.moduleReference.expression.text
    val fullname = TypeScript.resolveModuleName(localName, resolvedPath, config)
    val moduleName = TSPathResolver.basename(fullname)
    val varName = req.name.escapedText
    val imp = TSSingleImport(localName, List((varName, None)))
    importList.add(fullname, imp)
    global.put(varName, TSRenamedType(varName, TSReferenceType(s"$moduleName.$varName")), false, false)
  }

  private def parseExportDeclaration(elements: TSNodeArray): Unit = {
    elements.foreach(ele =>
      if (ele.propertyName.isUndefined)
        global.`export`(ele.symbol.escapedName)
      else {
        val alias = ele.symbol.escapedName
        global.getTop(ele.propertyName.escapedText).fold(())(tp => global.put(alias, TSRenamedType(alias, tp), true, false))
      }
    )
  }

  private def parseImportDeclaration(clause: TSNodeObject, moduleSpecifier: TSTokenObject, exported: Boolean): Unit = {
    // ignore `import "filename.ts"`
    if (!clause.isUndefined) {
      val bindings = clause.namedBindings
      val importName = moduleSpecifier.text
      val fullPath = TypeScript.resolveModuleName(importName, resolvedPath, config)
      def run(node: TSNodeObject): Unit =
        if (!node.elements.isUndefined) {
          val list = node.elements.mapToList(ele =>
            if (ele.propertyName.isUndefined) 
              (ele.symbol.escapedName, None)
            else
              (ele.propertyName.escapedText, Some(ele.symbol.escapedName))
          )
          val imp = TSSingleImport(importName, list)
          if (exported) imp.createAlias.foreach(re => reExportList += re) // re-export
          importList.add(fullPath, imp)
        }
        else if (!node.name.isUndefined) {
          val imp = TSFullImport(importName, node.name.escapedText)
          if (exported) imp.createAlias.foreach(re => reExportList += re) // re-export
          importList.add(fullPath, imp)
        }

      if (!bindings.isUndefined) run(bindings)
      else run(clause)
    }
  }

  private def getSubstitutionArguments[T <: TSAny](args: TSArray[T])(implicit ns: TSNamespace): List[TSType] =
    args.foldLeft(List[TSType]())((lst, arg) => arg match {
      case token: TSTokenObject => lst :+ getObjectType(token.typeNode)
      case tp: TSTypeObject => lst :+ getObjectType(tp)
    })

  private def getSymbolFullname(sym: TSSymbolObject)(implicit ns: TSNamespace): String =
    if (!sym.parent.isUndefined && sym.parent.declaration.isSourceFile)
      importList.resolveTypeAlias(sym.parent.declaration.resolvedPath, sym.escapedName)
    else if (sym.parent.isUndefined || !sym.parent.declaration.isNamespace)
      sym.escapedName
    else {
      def simplify(symName: String, nsName: String): String =
        if (symName.startsWith(nsName + ".")) symName.substring(nsName.length() + 1)
        else if (nsName.lastIndexOf('.') > -1) simplify(symName, nsName.substring(0, nsName.lastIndexOf('.')))
        else symName
      simplify(s"${getSymbolFullname(sym.parent)}.${sym.escapedName}", ns.toString())
    }

  private def getObjectType(obj: TSTypeObject)(implicit ns: TSNamespace): TSType =
    if (obj.isMapped) lineHelper.getPos(obj.pos) match {
        case (line, column) =>
          TSUnsupportedType(obj.toString(), TSPathResolver.basenameWithExt(obj.filename), line, column)
      }
    else if (obj.isEnumType) TSEnumType
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration, true)
    else if (obj.isTupleType) TSTupleType(getTupleElements(obj.typeArguments))
    else if (obj.isUnionType) getStructuralType(obj.types, true)
    else if (obj.isIntersectionType) getStructuralType(obj.types, false)
    else if (obj.isArrayType) TSArrayType(getObjectType(obj.elementTypeOfArray))
    else if (obj.isTypeParameterSubstitution) TSSubstitutionType(obj.symbol.escapedName, getSubstitutionArguments(obj.typeArguments))
    else if (obj.isObject)
      if (obj.isAnonymous) {
        val props = getAnonymousPropertiesType(obj.properties)
        if (!props.exists{ case (name, _) if (!name.isEmpty()) => Character.isUpperCase(name(0)); case _ => false})
          TSInterfaceType("", props, List(), List())
        else lineHelper.getPos(obj.pos) match {
          case (line, column) =>
            TSUnsupportedType(obj.toString(), TSPathResolver.basenameWithExt(obj.filename), line, column)
        }
      }
      else TSReferenceType(getSymbolFullname(obj.symbol))
    else if (obj.isTypeParameter) TSTypeParameter(obj.symbol.escapedName)
    else if (obj.isConditionalType || obj.isIndexType || obj.isIndexedAccessType) lineHelper.getPos(obj.pos) match {
      case (line, column) =>
        TSUnsupportedType(obj.toString(), TSPathResolver.basenameWithExt(obj.filename), line, column)
    }
    else TSPrimitiveType(obj.intrinsicName)

  // the function `getMemberType` can't process function/tuple type alias correctly
  private def getTypeAlias(tn: TSNodeObject)(implicit ns: TSNamespace): TSType =
    if (tn.isFunctionLike) getFunctionType(tn, true)
    else if (tn.isTupleTypeNode) TSTupleType(getTupleElements(tn.typeNode.typeArguments))
    else getObjectType(tn.typeNode) match {
      case TSPrimitiveType("intrinsic") => lineHelper.getPos(tn.pos) match {
        case (line, column) =>
          TSUnsupportedType(tn.toString(), TSPathResolver.basenameWithExt(tn.filename), line, column)
      }
      case t => t
    }

  // parse string/numeric literal types. we need to add quotes if it is a string literal
  private def getLiteralType(tp: TSNodeObject)(implicit ns: TSNamespace) =
    TSLiteralType(tp.literal.text, tp.literal.isStringLiteral)

  // parse object literal types
  private def getObjectLiteralMembers(props: TSNodeArray)(implicit ns: TSNamespace) =
    props.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      mp ++ Map(p.name.escapedText -> TSMemberType(TSLiteralType(p.initToken.text, p.initToken.isStringLiteral)))
    })

  // get the type of variables in classes/named interfaces/anonymous interfaces
  private def getMemberType(node: TSNodeObject)(implicit ns: TSNamespace): TSType = {
    val res: TSType =
      if (node.isIndexSignature || node.isCallSignature || node.isConstructSignature)
        lineHelper.getPos(node.pos) match {
          case (line, column) =>
            TSUnsupportedType(node.toString(), TSPathResolver.basenameWithExt(node.filename), line, column)
        }
      else if (node.isFunctionLike) getFunctionType(node, false) // erase name to avoid name clash when overriding methods in ts
      else if (node.`type`.isUndefined) getObjectType(node.typeAtLocation)
      else if (node.`type`.isLiteralTypeNode) getLiteralType(node.`type`)
      else getObjectType(node.`type`.typeNode)
    if (node.symbol.isOptionalMember) TSUnionType(res, TSPrimitiveType("undefined"))
    else res
  }

  private def getTypeParameters(node: TSNodeObject)(implicit ns: TSNamespace): List[TSTypeParameter] =
    node.typeParameters.foldLeft(List[TSTypeParameter]())((lst, tp) =>
      if (tp.constraint.isUndefined) lst :+ TSTypeParameter(tp.symbol.escapedName, None)
      else lst :+ TSTypeParameter(tp.symbol.escapedName, Some(getObjectType(tp.constraint.typeNode)))
    )

  private def getFunctionType(node: TSNodeObject, keepNames: Boolean)(implicit ns: TSNamespace): TSFunctionType = {
    def eraseVarParam(tp: TSType, erase: Boolean) = tp match { // TODO: support ... soon
      case arr @ TSArrayType(eleType) if erase => TSUnionType(eleType, arr)
      case _ => tp
    }

    val pList = node.parameters.foldLeft(List[TSParameterType]())((lst, p) => {
      // erase name to avoid name clash when overriding methods in ts
      val name = if (keepNames) p.symbol.escapedName else s"args${lst.length}"
      // in typescript, you can use `this` to explicitly specifies the callee
      // but it never appears in the final javascript file
      if (p.symbol.escapedName === "this") lst
      else if (p.isOptionalParameter) // TODO: support optinal and default value soon
        lst :+ TSParameterType(name, TSUnionType(getObjectType(p.symbolType), TSPrimitiveType("undefined")))
      else lst :+ TSParameterType(name, eraseVarParam(getObjectType(p.symbolType), p.isVarParam))
    })
    TSFunctionType(pList, getObjectType(node.returnType), getTypeParameters(node))
  }
    

  private def getStructuralType(types: TSTypeArray, isUnion: Boolean)(implicit ns: TSNamespace): TSType =
    types.foldLeft[Option[TSType]](None)((prev, cur) => prev match {
      case None => Some(getObjectType(cur))
      case Some(p) =>
        if (isUnion) Some(TSUnionType(p, getObjectType(cur))) else Some(TSIntersectionType(p, getObjectType(cur)))
    }).get

  private def getTupleElements(elements: TSTypeArray)(implicit ns: TSNamespace): List[TSType] =
    elements.foldLeft(List[TSType]())((lst, ele) => lst :+ getObjectType(ele))

  private def getHeritageList(node: TSNodeObject)(implicit ns: TSNamespace): List[TSType] =
    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) =>
      lst :+ getObjectType(h.types.get(index).typeNode)
    )

  private def addMember(mem: TSType, node: TSNodeObject, name: String, others: Map[String, TSMemberType])(implicit ns: TSNamespace): Map[String, TSMemberType] = mem match {
    case func: TSFunctionType => {
      if (!others.contains(name)) others ++ Map(name -> TSMemberType(func, node.modifier))
      else { // TODO: handle functions' overloading
        val res = TSIgnoredOverload(func, name) // the implementation is always after declarations
        others.removed(name) ++ Map(name -> TSMemberType(res, node.modifier))
      }
    }
    case _ => mem match {
      case TSReferenceType(ref) if name === ref => lineHelper.getPos(node.pos) match {
        case (line, column) =>
          others ++ Map(name -> TSMemberType(
            TSUnsupportedType(node.toString(), TSPathResolver.basenameWithExt(node.filename), line, column),
            node.modifier
          ))
      }
      case _ => others ++ Map(name -> TSMemberType(mem, node.modifier))
    }
  }

  private def getClassMembersType(list: TSNodeArray, requireStatic: Boolean)(implicit ns: TSNamespace): Map[String, TSMemberType] =
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

  private def getConstructorList(members: TSNodeArray)(implicit ns: TSNamespace): List[TSParameterType] =
    members.foldLeft(List[TSParameterType]())((lst, mem) => {
      val name = mem.symbol.escapedName

      if (name =/= "__constructor") lst
      else mem.parameters.foldLeft(List[TSParameterType]())((res, p) =>
        res :+ TSParameterType(p.symbol.escapedName, getMemberType(p)))
    })

  private def getInterfacePropertiesType(list: TSNodeArray)(implicit ns: TSNamespace): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => addMember(getMemberType(p), p, p.symbol.escapedName, mp))

  private def getAnonymousPropertiesType(list: TSSymbolArray)(implicit ns: TSNamespace): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) =>
      mp ++ Map(p.escapedName -> TSMemberType(if (p.`type`.isUndefined) getMemberType(p.declaration) else getObjectType(p.`type`))))

  private def parseMembers(name: String, node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace): TSType =
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
    if (!ns.containsMember(name, false)) ns.put(name, fun, node.isExported, false)
    else
      ns.put(name, TSIgnoredOverload(fun, name), node.isExported || ns.exported(name), true) // the implementation is always after declarations

  // overload functions in a sub-namespace need to provide an overload array
  // because the namespace merely exports symbols rather than node objects themselves
  private def addNodeIntoNamespace(node: TSNodeObject, name: String, exported: Boolean, overload: Option[TSNodeArray] = None)(implicit ns: TSNamespace) =
    if (node.isFunctionLike) overload.fold(
      addFunctionIntoNamespace(getFunctionType(node, true), node, name)
    )(decs => decs.foreach(d => addFunctionIntoNamespace(getFunctionType(d, true), d, name)))
    else if (node.isClassDeclaration)
      ns.put(name, parseMembers(name, node, true), exported, false)
    else if (node.isInterfaceDeclaration)
      ns.put(name, parseMembers(name, node, false), exported, false)
    else if (node.isTypeAliasDeclaration)
      ns.put(name, TSTypeAlias(name, getTypeAlias(node.`type`), getTypeParameters(node)), exported, false)
    else if (node.isObjectLiteral)
      ns.put(name, TSInterfaceType("", getObjectLiteralMembers(node.initializer.properties), List(), List()), exported, false)
    else if (node.isVariableDeclaration) ns.put(name, getMemberType(node), exported, false)
    else if (node.isNamespace)
      parseNamespace(node)

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit =
    parseNamespaceLocals(node.locals, node.exports)(ns.derive(node.symbol.escapedName, node.isExported))
}

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker, config: js.Dynamic) =
    new TSSourceFile(sf, global)
}
