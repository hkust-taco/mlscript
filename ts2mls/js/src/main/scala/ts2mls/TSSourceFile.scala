package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import types._
import mlscript.utils._
import scala.collection.mutable.ListBuffer

class TSSourceFile(sf: js.Dynamic, val global: TSNamespace, topName: String)(implicit checker: TSTypeChecker, config: js.Dynamic) {
  private val lineHelper = new TSLineStartsHelper(sf.getLineStarts())
  private val importList = TSImportList()
  private val reExportList = new ListBuffer[TSReExport]()
  private val resolvedPath = sf.resolvedPath.toString()
  private var umdModuleName: Option[String] = None // `export as namespace` in ts

  val referencedFiles = sf.referencedFiles.map((x: js.Dynamic) => x.fileName.toString())
  def getUMDModule: Option[TSNamespace] =
    umdModuleName.fold[Option[TSNamespace]](Some(global))(name => Some(global.derive(name, false)))

  // Parse import & re-export first
  TypeScript.forEachChild(sf, (node: js.Dynamic) => {
    val nodeObject = TSNodeObject(node)
    if (nodeObject.isRequire)
      parseRequire(nodeObject)
    else if (nodeObject.isImportDeclaration)
      parseImportDeclaration(nodeObject.importClause, nodeObject.moduleSpecifier, false)
    else if (nodeObject.isExportDeclaration && !nodeObject.moduleSpecifier.isUndefined) // Re-export
      parseImportDeclaration(nodeObject.exportClause, nodeObject.moduleSpecifier, true)
  })

  private var parsed = false
  def parse = if (!parsed) {
    parsed = true
    // Parse main body
    TypeScript.forEachChild(sf, (node: js.Dynamic) => {
      val nodeObject = TSNodeObject(node)
      if (!nodeObject.isToken) {
        if (!nodeObject.symbol.isUndefined) { // For functions
          if (nodeObject.isFunctionLike)
            addFunctionIntoNamespace(nodeObject.symbol, nodeObject, nodeObject.symbol.escapedName)(global)
          else // For classes/interfaces/namespace
            addNodeIntoNamespace(nodeObject, nodeObject.symbol.escapedName, nodeObject.isExported)(global)
        }
        else if (!nodeObject.declarationList.isUndefined) { // For variables
          val decNode = nodeObject.declarationList.declaration
          addNodeIntoNamespace(decNode, decNode.symbol.escapedName, decNode.isExported)(global)
        }
      }
    })

    // Parse export
    TypeScript.forEachChild(sf, (node: js.Dynamic) => {
      val nodeObject = TSNodeObject(node)
      if (nodeObject.isExportDeclaration) {
        if (nodeObject.moduleSpecifier.isUndefined) // ES modules
          parseExportDeclaration(nodeObject.exportClause.elements)
      }
      else if (nodeObject.isExportAssignment) { // CommonJS
        val name = nodeObject.idExpression.escapedText
        if (name === "undefined") { // For exports = { ... }. In this case we still need the top-level module
          val props = nodeObject.nodeExpression.properties
          props.foreach(node => {
            val name = node.initID.escapedText
            if (name === "undefined")
              addNodeIntoNamespace(node.initializer, node.name.escapedText, true)(global)
            else if (node.name.escapedText === name)
              global.`export`(name)
            else global.put(node.name.escapedText, TSRenamedType(node.name.escapedText, TSReferenceType(name)), true, false)
          })
        }
        else global.renameExport(name, topName) // Export the member directly
      }
      else if (nodeObject.exportedAsNamespace) // UMD
        umdModuleName = Some(nodeObject.symbol.escapedName)
    })
  }

  def getImportList: List[TSImport] = importList.getFilelist
  def getReExportList: List[TSReExport] = reExportList.toList

  private def parseRequire(req: TSNodeObject): Unit = {
    val localName = req.moduleReference.expression.text
    val fullname = TypeScript.resolveModuleName(localName, resolvedPath, config)
    val moduleName = TSPathResolver.basename(fullname)
    val varName = req.name.escapedText
    if (req.hasModuleReference) {
      val imp = TSFullImport(localName, varName)
      importList.add(fullname, imp)
      global.put(varName, TSRenamedType(varName, TSReferenceType(s"$moduleName")), false, false)
    }
    else {
      val imp = TSSingleImport(localName, List((varName, None)))
      importList.add(fullname, imp)
      global.put(varName, TSRenamedType(varName, TSReferenceType(s"$moduleName.$varName")), false, false)
    }
  }

  private def parseExportDeclaration(elements: TSNodeArray): Unit = {
    elements.foreach(ele =>
      if (ele.propertyName.isUndefined)
        global.`export`(ele.symbol.escapedName)
      else global.exportWithAlias(ele.propertyName.escapedText, ele.symbol.escapedName)
    )
  }

  private def parseImportDeclaration(clause: TSNodeObject, moduleSpecifier: TSTokenObject, exported: Boolean): Unit = {
    // Ignore `import "filename.ts"`
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
          if (exported) imp.createAlias.foreach(re => reExportList += re) // Re-export
          importList.add(fullPath, imp)
        }
        else if (!node.name.isUndefined) {
          val imp = TSFullImport(importName, node.name.escapedText)
          if (exported) imp.createAlias.foreach(re => reExportList += re) // Re-export
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

  private def getSymbolFullname(sym: TSSymbolObject)(implicit ns: TSNamespace): String = {
    def simplify(symName: String, nsName: String): String = // Remove unnecessary namespaces prefixes
      if (symName.startsWith(nsName + ".")) symName.substring(nsName.length() + 1)
      else if (nsName.lastIndexOf('.') > -1) simplify(symName, nsName.substring(0, nsName.lastIndexOf('.')))
      else symName
    if (!sym.parent.isUndefined && sym.parent.declaration.isSourceFile) // Imported from another file
      importList.resolveTypeAlias(sym.parent.declaration.resolvedPath, sym.escapedName)
    else if (!sym.parent.isUndefined && sym.parent.isMerged) { // Merged with other declarations
      def findDecFile(node: TSNodeObject): String =
        if (node.parent.isUndefined) ""
        else if (node.parent.isSourceFile) {
          if (node.parent.moduleAugmentation.isUndefined)
            node.parent.resolvedPath
          else {
            val base = node.parent.resolvedPath
            val rel = node.parent.moduleAugmentation.text
            if (TSPathResolver.isLocal(rel)) TypeScript.resolveModuleName(rel, base, config)
            else base
          }
        }
        else findDecFile(node.parent)
      val filename = sym.declarations.foldLeft[Option[String]](None)((filename, dec) => filename match {
        case filename: Some[String] => filename
        case _ =>
          val res = findDecFile(dec)
          Option.when((res === resolvedPath) || importList.contains(res))(res)
      })
      filename.fold(sym.escapedName)(filename => // Not found: this file is referenced by `///`. directly use the name is safe
        if (filename === resolvedPath) // In the same file
          simplify(s"${getSymbolFullname(sym.parent)}.${sym.escapedName}", ns.toString())
        else importList.resolveTypeAlias(filename, sym.escapedName) // In an imported file
      )
    }
    else if (sym.parent.isUndefined) { // Already top-level symbol
      val name = sym.escapedName
      if (name.contains("\"")) TSPathResolver.basename(name.substring(1, name.length() - 1))
      else name
    }
    else
      simplify(s"${getSymbolFullname(sym.parent)}.${sym.escapedName}", ns.toString())
  }

  private def markUnsupported(node: TSNodeObject): TSUnsupportedType =
    lineHelper.getPos(node.pos) match {
      case (line, column) =>
        TSUnsupportedType(node.toString(), TSPathResolver.basenameWithExt(node.filename), line, column)
    }

  private def getObjectType(obj: TSTypeObject)(implicit ns: TSNamespace): TSType =
    if (obj.isMapped) TSNoInfoUnsupported
    else if (obj.isEnumType) TSEnumType
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration, true)
    else if (obj.isTupleType) TSTupleType(getTupleElements(obj.typeArguments))
    else if (obj.isUnionType) getStructuralType(obj.types, true)
    else if (obj.isIntersectionType) getStructuralType(obj.types, false)
    else if (obj.isArrayType) TSArrayType(getObjectType(obj.elementTypeOfArray))
    else if (obj.isTypeParameterSubstitution) {
      val baseName = getSymbolFullname(if (obj.symbol.isUndefined) obj.aliasSymbol else obj.symbol)
      if (baseName.contains(".")) TSNoInfoUnsupported // A.B<C> is not supported in mlscript so far
      else TSSubstitutionType(TSReferenceType(baseName), getSubstitutionArguments(obj.typeArguments))
    }
    else if (obj.isObject)
      if (obj.isAnonymous) {
        val props = getAnonymousPropertiesType(obj.properties)
        // Upper case field names are not supported in records in mlscript so far
        if (!props.exists{ case (name, _) if (!name.isEmpty()) => Character.isUpperCase(name(0)); case _ => false})
          TSInterfaceType("", props, List(), List(), None)
        else TSNoInfoUnsupported
      }
      else TSReferenceType(getSymbolFullname(obj.symbol))
    else if (obj.isTypeParameter) TSTypeParameter(obj.symbol.escapedName)
    else if (obj.isConditionalType || obj.isIndexType || obj.isIndexedAccessType) TSNoInfoUnsupported
    else TSPrimitiveType(obj.intrinsicName)

  // The function `getMemberType` can't process function/tuple type alias correctly
  private def getTypeAlias(tn: TSNodeObject)(implicit ns: TSNamespace): TSType =
    if (tn.isFunctionLike)
      getFunctionType(tn, true)
    else if (tn.isTupleTypeNode) TSTupleType(getTupleElements(tn.typeNode.typeArguments))
    else getObjectType(tn.typeNode) match {
      case TSPrimitiveType("intrinsic") => markUnsupported(tn)
      case t => t
    }

  // Parse string/numeric literal types. We need to add quotes if it is a string literal
  private def getLiteralType(tp: TSNodeObject)(implicit ns: TSNamespace) =
    TSLiteralType(tp.literal.text, tp.literal.isStringLiteral)

  // Parse object literal types
  private def getObjectLiteralMembers(props: TSNodeArray)(implicit ns: TSNamespace) =
    props.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      mp.updated(p.name.escapedText, TSMemberType(TSLiteralType(p.initToken.text, p.initToken.isStringLiteral)))
    })

  // Get the type of variables in classes/named interfaces/anonymous interfaces
  private def getMemberType(node: TSNodeObject)(implicit ns: TSNamespace): TSType =
    if (node.isIndexSignature || node.isConstructSignature)
      markUnsupported(node)
    else {
      val res =
        if (node.isFunctionLike) getFunctionType(node, false) // Erase name to avoid name clash when overriding methods in ts
        else if (node.`type`.isUndefined) getObjectType(node.typeAtLocation)
        else if (node.`type`.isLiteralTypeNode) getLiteralType(node.`type`)
        else getObjectType(node.`type`.typeNode)
      if (res.unsupported) markUnsupported(node)
      else if (node.symbol.isOptionalMember) TSUnionType(res, TSPrimitiveType("undefined"))
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
      // Erase name to avoid name clash when overriding methods in ts
      val name = if (keepNames) p.symbol.escapedName else s"args${lst.length}"
      // In typescript, you can use `this` to explicitly specifies the callee.
      // But it never appears in the final javascript file
      if (p.symbol.escapedName === "this") lst
      else if (p.isOptionalParameter) // TODO: support optional and default value soon
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
    node.heritageClauses.foldLeftIndexed(List[TSType]())((lst, h, index) => {
      lst :+ (getObjectType(h.types.get(index).typeNode) match {
        case TSArrayType(ele) => TSSubstitutionType(TSReferenceType("Array"), ele :: Nil)
        case t => t
      })
    })

  private def addMember(
    mem: TSType,
    node: TSNodeObject,
    name: String,
    mod: Option[TSAccessModifier],
    others: Map[String, TSMemberType]
  )(implicit ns: TSNamespace): Map[String, TSMemberType] = mem match {
    case func: TSFunctionType => {
      if (!others.contains(name)) others.updated(name, TSMemberType(func, mod.getOrElse(node.modifier)))
      else { // TODO: handle functions' overloading
        val res = TSIgnoredOverload(func, name) // The implementation is always after declarations
        others.updated(name, TSMemberType(res, mod.getOrElse(node.modifier)))
      }
    }
    case _ => mem match {
      // If the member's name is the same as the type name, we need to mark it unsupported
      case TSReferenceType(ref) if name === ref =>
        others.updated(name, TSMemberType(
          markUnsupported(node),
          mod.getOrElse(node.modifier)
        ))
      case _ => others.updated(name, TSMemberType(mem, mod.getOrElse(node.modifier)))
    }
  }

  private def getClassMembersType(list: TSNodeArray, requireStatic: Boolean)(implicit ns: TSNamespace): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) => {
      // The constructors have no name identifier.
      if (!p.name.isUndefined && p.isStatic == requireStatic) {
        val name = p.name.escapedText
        val mem =
          if (!p.isStatic) getMemberType(p)
          else parseMembers(name, p.initializer, true)
        addMember(mem, p, name, Option.when[TSAccessModifier](name.startsWith("#"))(Private), mp)
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
    list.foldLeft(Map[String, TSMemberType]())((mp, p) =>
      if (p.isCallSignature) mp else addMember(getMemberType(p), p, p.symbol.escapedName, None, mp))

  private def getAnonymousPropertiesType(list: TSSymbolArray)(implicit ns: TSNamespace): Map[String, TSMemberType] =
    list.foldLeft(Map[String, TSMemberType]())((mp, p) =>
      mp.updated(p.escapedName, TSMemberType(if (p.`type`.isUndefined) getMemberType(p.declaration) else getObjectType(p.`type`))))

  private def parseMembers(name: String, node: TSNodeObject, isClass: Boolean)(implicit ns: TSNamespace): TSType = {
    val res = // Do not handle parents here. we have not had enough information so far.
      if (isClass)
        TSClassType(name, getClassMembersType(node.members, false), getClassMembersType(node.members, true),
          getTypeParameters(node), getHeritageList(node), getConstructorList(node.members))
      else
        TSInterfaceType(name, getInterfacePropertiesType(node.members), getTypeParameters(node),
          getHeritageList(node), parseCallSignature(node.members))
    if (res.unsupported) markUnsupported(node) else res
  }

  private def parseCallSignature(list: TSNodeArray)(implicit ns: TSNamespace) =
    list.foldLeft[Option[TSFunctionType]](None)((cs, node) =>
      if (node.isCallSignature) Some(getFunctionType(node, false))
      else cs
    )

  private def parseNamespaceLocals(map: TSSymbolMap, exports: TSSymbolMap)(implicit ns: TSNamespace) =
    map.foreach((sym) => {
      val node = sym.declaration
      val name = sym.escapedName
      if (node.isFunctionLike) addFunctionIntoNamespace(sym, node, name)
      else if (!node.isToken)
        sym.declarations.foreach(dec =>
          addNodeIntoNamespace(dec, name, exports.contains(name))
        )
    })

  private def addFunctionIntoNamespace(sym: TSSymbolObject, node: TSNodeObject, name: String)(implicit ns: TSNamespace) =
    sym.declarations.foreach(d => {
      val fun = getFunctionType(d, true)
      if (fun.unsupported) ns.put(name, markUnsupported(node), node.isExported, false)
      else if (!ns.containsMember(name, false)) ns.put(name, fun, node.isExported, false)
      else
        ns.put(name, TSIgnoredOverload(fun, name), node.isExported || ns.exported(name), true) // The implementation is always after declarations
    })

  // Overload functions in a sub-namespace need to provide an overload array
  // because the namespace merely exports symbols rather than node objects themselves
  private def addNodeIntoNamespace(node: TSNodeObject, name: String, exported: Boolean)(implicit ns: TSNamespace) =
    if (node.isClassDeclaration)
      ns.put(name, parseMembers(name, node, true), exported, false)
    else if (node.isInterfaceDeclaration)
      ns.put(name, parseMembers(name, node, false), exported, false)
    else if (node.isTypeAliasDeclaration) {
      val alias = TSTypeAlias(name, getTypeAlias(node.`type`), getTypeParameters(node))
      ns.put(name, if (alias.unsupported) TSTypeAlias(name, markUnsupported(node), Nil) else alias, exported, false)
    }
    else if (node.isObjectLiteral) {
      val obj = TSInterfaceType("", getObjectLiteralMembers(node.initializer.properties), List(), List(), None)
      ns.put(name, if (obj.unsupported) markUnsupported(node) else obj, exported, false)
    }
    else if (node.isVariableDeclaration) ns.put(name, getMemberType(node), exported, false)
    else if (node.isNamespace)
      parseNamespace(node)

  private def parseNamespace(node: TSNodeObject)(implicit ns: TSNamespace): Unit = {
    val name = node.symbol.escapedName
    if (name.contains("\"")) { // Ambient Modules
      val fullname = TypeScript.resolveModuleName(name.substring(1, name.length() - 1), resolvedPath, config)
      importList.remove(fullname)
      parseNamespaceLocals(node.locals, node.exports)
    }
    else parseNamespaceLocals(node.locals, node.exports)(ns.derive(name, node.isExported))
  }
}

object TSSourceFile {
  def apply(sf: js.Dynamic, global: TSNamespace, topName: String)(implicit checker: TSTypeChecker, config: js.Dynamic) =
    new TSSourceFile(sf, global, topName)
}
