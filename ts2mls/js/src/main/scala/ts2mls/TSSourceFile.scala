package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import types._
import mlscript.utils._
import scala.collection.mutable.{ListBuffer, HashMap}

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
  })

  def getImportList: List[TSImport] = importList.getFilelist
  def getReExportList: List[TSReExport] = reExportList.toList

  private def parseRequire(req: TSNodeObject): Unit = {
    val localName = req.moduleReference.expression.text
    val fullname = TypeScript.resolveModuleName(localName, resolvedPath, config) match {
      case Some(name) => name
      case _ => throw new AssertionError(s"unexpected required module $localName")
    }
    val moduleName = TSImport.getModuleName(fullname, false)
    val varName = req.name.escapedText
    val imp = TSSingleImport(localName, List((varName, None)))
    importList.add(fullname, imp)
    global.put(varName, TSRenamedType(varName, TSReferenceType(s"$moduleName.$varName")), false)
  }

  private def parseExportDeclaration(elements: TSNodeArray): Unit = {
    elements.foreach(ele =>
      if (ele.propertyName.isUndefined)
        global.export(ele.symbol.escapedName)
      else {
        val alias = ele.symbol.escapedName
        global.getTop(ele.propertyName.escapedText).fold(())(tp => global.put(alias, TSRenamedType(alias, tp), true))
      }
    )
  }

  private def parseImportDeclaration(clause: TSNodeObject, moduleSpecifier: TSTokenObject, exported: Boolean): Unit = {
    // ignore `import "filename.ts"`
    if (!clause.isUndefined) {
      val bindings = clause.namedBindings
      val importName = moduleSpecifier.text
      val fullPath = TypeScript.resolveModuleName(importName, resolvedPath, config).getOrElse(
        throw new AssertionError(s"unexpected import $importName.")
      )
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
        case (line, column) => TSUnsupportedType(obj.toString(), obj.filename, line, column)
      }
    else if (obj.isEnumType) TSEnumType
    else if (obj.isFunctionLike) getFunctionType(obj.symbol.declaration) match {
      case head :: Nil => head
      case head :: tail => tail.foldLeft[TSType](head)((res, f) => TSIntersectionType(res, f))
      case Nil => throw new AssertionError("empty function type.")
    }
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
  private def getTypeAlias(tn: TSNodeObject)(implicit ns: TSNamespace): TSType =
    if (tn.isFunctionLike) getFunctionType(tn) match {
      case head :: Nil => head
      case head :: tail => tail.foldLeft[TSType](head)((res, f) => TSIntersectionType(res, f))
      case Nil => throw new AssertionError("empty function type.")
    }
    else if (tn.isTupleTypeNode) TSTupleType(getTupleElements(tn.typeNode.typeArguments))
    else getObjectType(tn.typeNode) match {
      case TSPrimitiveType("intrinsic") => lineHelper.getPos(tn.pos) match {
        case (line, column) => TSUnsupportedType(tn.toString(), tn.filename, line, column)
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
          case (line, column) => TSUnsupportedType(node.toString(), node.filename, line, column)
        }
      else if (node.isFunctionLike) getFunctionType(node) match {
        case head :: Nil => head
        case head :: tail => tail.foldLeft[TSType](head)((res, f) => TSIntersectionType(res, f))
        case Nil => throw new AssertionError("empty function type.")
      }
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

  private def getFunctionType(node: TSNodeObject)(implicit ns: TSNamespace): List[TSFunctionType] = {
    val res = getObjectType(node.returnType)
    val tv = getTypeParameters(node)
    node.parameters.foldLeft(TSFunctionType(Nil, res, tv) :: Nil)((funs, p) => (
      // in typescript, you can use `this` to explicitly specifies the callee
      // but it never appears in the final javascript file
      if (p.symbol.escapedName === "this") funs
      else if (p.isOptionalParameter) funs.lastOption match {
        case Some(TSFunctionType(params, res, tv)) =>
          funs :+ TSFunctionType(params :+ TSParameterType(p.symbol.escapedName, getObjectType(p.symbolType)), res, tv)
        case _ => throw new AssertionError("empty function type.")
      }
      else funs.headOption match {
        case Some(TSFunctionType(params, res, tv)) =>
          TSFunctionType(params :+ TSParameterType(p.symbol.escapedName, getObjectType(p.symbolType)), res, tv) :: Nil
        case _ => throw new AssertionError("empty function type.")
      })
    )
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
        getFunctionType(node).foreach(addFunctionIntoNamespace(_, node, name))
      case Some(decs) => {
        decs.foreach((d) =>
          getFunctionType(d).foreach(addFunctionIntoNamespace(_, d, name))
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
  def apply(sf: js.Dynamic, global: TSNamespace)(implicit checker: TSTypeChecker, config: js.Dynamic) =
    new TSSourceFile(sf, global)
}
