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

  // parse import
  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isRequire)
      parseRequire(nodeObject)
    else if (nodeObject.isImportDeclaration)
      parseImportDeclaration(nodeObject.importClause, nodeObject.moduleSpecifier, false)
  })

  // parse main body
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

  // handle parents
  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (!nodeObject.isToken) {
      if (!nodeObject.symbol.isUndefined) // for functions/classes/interfaces
        handleParents(nodeObject, nodeObject.symbol.escapedName)(global)
      else if (!nodeObject.declarationList.isUndefined) { // for variables
        val decNode = nodeObject.declarationList.declaration
        handleParents(decNode, decNode.symbol.escapedName)(global)
      }
    }
  })

  // check export
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

  private def markUnsupported(node: TSNodeObject): TSUnsupportedType =
    lineHelper.getPos(node.pos) match {
      case (line, column) =>
        TSUnsupportedType(node.toString(), TSPathResolver.basenameWithExt(node.filename), line, column)
    }

  private def getObjectType(obj: TSTypeObject)(implicit ns: TSNamespace): TSType =
    if (obj.isMapped) TSPartialUnsupportedType
    else if (obj.isEnumType) TSEnumType
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration, true)
    else if (obj.isTupleType) TSTupleType(getTupleElements(obj.typeArguments))
    else if (obj.isUnionType) getStructuralType(obj.types, true)
    else if (obj.isIntersectionType) getStructuralType(obj.types, false)
    else if (obj.isArrayType) TSArrayType(getObjectType(obj.elementTypeOfArray))
    else if (obj.isTypeParameterSubstitution) TSSubstitutionType(TSReferenceType(obj.symbol.escapedName), getSubstitutionArguments(obj.typeArguments))
    else if (obj.isObject)
      if (obj.isAnonymous) {
        val props = getAnonymousPropertiesType(obj.properties)
        if (!props.exists{ case (name, _) if (!name.isEmpty()) => Character.isUpperCase(name(0)); case _ => false})
          TSInterfaceType("", props, List(), List())
        else TSPartialUnsupportedType
      }
      else TSReferenceType(getSymbolFullname(obj.symbol))
    else if (obj.isTypeParameter) TSTypeParameter(obj.symbol.escapedName)
    else if (obj.isConditionalType || obj.isIndexType || obj.isIndexedAccessType) TSPartialUnsupportedType
    else TSPrimitiveType(obj.intrinsicName)

  // the function `getMemberType` can't process function/tuple type alias correctly
  private def getTypeAlias(tn: TSNodeObject)(implicit ns: TSNamespace): TSType =
    if (tn.isFunctionLike) getFunctionType(tn, true)
    else if (tn.isTupleTypeNode) TSTupleType(getTupleElements(tn.typeNode.typeArguments))
    else getObjectType(tn.typeNode) match {
      case TSPrimitiveType("intrinsic") => markUnsupported(tn)
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
        markUnsupported(node)
      else if (node.isFunctionLike) getFunctionType(node, false) // erase name to avoid name clash when overriding methods in ts
      else if (node.`type`.isUndefined) getObjectType(node.typeAtLocation)
      else if (node.`type`.isLiteralTypeNode) getLiteralType(node.`type`)
      else getObjectType(node.`type`.typeNode)
    if (res.unsupported) markUnsupported(node)
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

  private def getHeritageList(node: TSNodeObject, members: Set[String])(implicit ns: TSNamespace): List[TSType] =
    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) => {
      def run(ref: TSReferenceType) = ns.get(ref.names) match {
        case itf: TSInterfaceType
          if (itf.members.foldLeft(itf.unsupported)((r, t) => r || (t._2.base.unsupported && members(t._1)))) =>
            TSPartialUnsupportedType
        case cls: TSClassType
          if (cls.members.foldLeft(cls.unsupported)((r, t) => r || (t._2.base.unsupported && members(t._1)))) =>
            TSPartialUnsupportedType
        case t if (t.unsupported) => TSPartialUnsupportedType
        case t => ref
      }
      lst :+ (getObjectType(h.types.get(index).typeNode) match {
        case ref: TSReferenceType => run(ref)
        case TSSubstitutionType(base, app) => run(base) match {
          case ref: TSReferenceType => TSSubstitutionType(ref, app)
          case t => t
        }
        case t => t
      })
    })

  private def addMember(mem: TSType, node: TSNodeObject, name: String, others: Map[String, TSMemberType])(implicit ns: TSNamespace): Map[String, TSMemberType] = mem match {
    case func: TSFunctionType => {
      if (!others.contains(name)) others ++ Map(name -> TSMemberType(func, node.modifier))
      else { // TODO: handle functions' overloading
        val res = TSIgnoredOverload(func, name) // the implementation is always after declarations
        others.removed(name) ++ Map(name -> TSMemberType(res, node.modifier))
      }
    }
    case _ => mem match {
      // if the member's name is the same as the type name, we need to mark it unsupported
      case TSReferenceType(ref) if name === ref =>
        others ++ Map(name -> TSMemberType(
          markUnsupported(node),
          node.modifier
        ))
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

  private def parseMembers(name: String, node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace): TSType = {
    val res = // do not handle parents here. we have not had enough information so far.
      if (isClass)
        TSClassType(name, getClassMembersType(node.members, false), getClassMembersType(node.members, true),
          getTypeParameters(node), Nil, getConstructorList(node.members))
      else TSInterfaceType(name, getInterfacePropertiesType(node.members), getTypeParameters(node), Nil)
    if (res.unsupported) markUnsupported(node) else res
  }

  private def parseNamespaceLocals(map: TSSymbolMap, exports: TSSymbolMap)(implicit ns: TSNamespace) =
    map.foreach((sym) => {
      val node = sym.declaration
      val name = sym.escapedName
      if (!node.isToken)
        addNodeIntoNamespace(node, name, exports.contains(name), if (node.isFunctionLike) Some(sym.declarations) else None)
    })

  private def addFunctionIntoNamespace(fun: TSFunctionType, node: TSNodeObject, name: String)(implicit ns: TSNamespace) =
    if (fun.unsupported) ns.put(name, markUnsupported(node), node.isExported, false)
    else if (!ns.containsMember(name, false)) ns.put(name, fun, node.isExported, false)
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
    else if (node.isTypeAliasDeclaration) {
      val alias = TSTypeAlias(name, getTypeAlias(node.`type`), getTypeParameters(node))
      ns.put(name, if (alias.unsupported) TSTypeAlias(name, markUnsupported(node), Nil) else alias, exported, false)
    }
    else if (node.isObjectLiteral) {
      val obj = TSInterfaceType("", getObjectLiteralMembers(node.initializer.properties), List(), List())
      ns.put(name, if (obj.unsupported) markUnsupported(node) else obj, exported, false)
    }
    else if (node.isVariableDeclaration) ns.put(name, getMemberType(node), exported, false)
    else if (node.isNamespace)
      parseNamespace(node)

  private def handleParents(node: TSNodeObject, name: String)(implicit ns: TSNamespace): Unit =
    if (node.isClassDeclaration) ns.get(name) match {
      case TSClassType(name, members, statics, typeVars, _, constructor) =>
        val cls = TSClassType(name, members, statics, typeVars, getHeritageList(node, members.keySet), constructor)
        ns.put(name, if (cls.unsupported) markUnsupported(node) else cls, ns.exported(name), true)
      case _ => throw new AssertionError(s"$name is not a class")
    }
    else if (node.isInterfaceDeclaration) ns.get(name) match {
      case TSInterfaceType(name, members, typeVars, parents) =>
        val itf = TSInterfaceType(name, members, typeVars, getHeritageList(node, members.keySet))
        ns.put(name, if (itf.unsupported) markUnsupported(node) else itf, ns.exported(name), true)
      case _ => throw new AssertionError(s"$name is not an interface")
    }
    else if (node.isNamespace) {
      val sub = ns.derive(node.symbol.escapedName, false)
      node.locals.foreach((sym) => {
        val node = sym.declaration
        val name = sym.escapedName
        if (!node.isToken) handleParents(node, name)(sub)
      })
    }

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit =
    parseNamespaceLocals(node.locals, node.exports)(ns.derive(node.symbol.escapedName, node.isExported))
}

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker, config: js.Dynamic) =
    new TSSourceFile(sf, global)
}
