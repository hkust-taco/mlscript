package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import ts2mls.types._

object TypeScript {
  private def load(moduleName: String) = try g.require(moduleName) catch {
    case _ : Throwable => {
      System.err.println(s"Cannot find $moduleName in the current directory. Please install by running \"npm install\".")
      val process = g.require("process")
      process.exit(-1)
    }
  }

  private val ts: js.Dynamic = load("typescript")
  private val json: js.Dynamic = load("json5")

  private val resolver = g.require.resolve

  def parseOption(basePath: String, filename: Option[String]): js.Dynamic = {
    val config = filename.fold[js.Any](js.Dictionary())(filename => {
      val content = JSFileSystem.readFile(TSModuleResolver.normalize(s"$basePath/$filename")).getOrElse("")
      json.parse(content)
    })
    val name = filename.getOrElse("tsconfig.json")
    ts.parseJsonConfigFileContent(config, ts.sys, basePath, null, name)
  }

  def resolveModuleName(importName: String, containingName: String, config: js.Dynamic): Option[String] = {
    val res = ts.resolveModuleName(importName, containingName, config, ts.sys)
    if (!IsUndefined(res.resolvedModule) && !IsUndefined(res.resolvedModule.resolvedFileName))
      Some(res.resolvedModule.resolvedFileName.toString())
    else None
  }

  val typeFlagsEnumLike = ts.TypeFlags.EnumLike
  val typeFlagsObject = ts.TypeFlags.Object
  val typeFlagsTypeParameter = ts.TypeFlags.TypeParameter
  val syntaxKindPrivate = ts.SyntaxKind.PrivateKeyword
  val syntaxKindProtected = ts.SyntaxKind.ProtectedKeyword
  val syntaxKindStatic = ts.SyntaxKind.StaticKeyword
  val syntaxKindExport = ts.SyntaxKind.ExportKeyword
  val objectFlagsAnonymous = ts.ObjectFlags.Anonymous
  val objectFlagsMapped = ts.ObjectFlags.Mapped
  val symbolFlagsOptional = ts.SymbolFlags.Optional // this flag is only for checking optional members of interfaces
  val typeFlagsConditional = ts.TypeFlags.Conditional // T extends U ? X : Y
  val typeFlagsIndex = ts.TypeFlags.Index // keyof T
  val typeFlagsIndexedAccess = ts.TypeFlags.IndexedAccess // T[K]

  def isToken(node: js.Dynamic) = ts.isToken(node)
  def isClassDeclaration(node: js.Dynamic) = ts.isClassDeclaration(node)
  def isInterfaceDeclaration(node: js.Dynamic) = ts.isInterfaceDeclaration(node)
  def isFunctionLike(node: js.Dynamic) = ts.isFunctionLike(node)
  def isModuleDeclaration(node: js.Dynamic) = ts.isModuleDeclaration(node)
  def isImportDeclaration(node: js.Dynamic) = ts.isImportDeclaration(node)
  def isSourceFile(node: js.Dynamic) = ts.isSourceFile(node)
  def isExportDeclaration(node: js.Dynamic) = ts.isExportDeclaration(node)

  def isArrayTypeNode(node: js.Dynamic) = ts.isArrayTypeNode(node)
  def isTupleTypeNode(node: js.Dynamic) = ts.isTupleTypeNode(node)
  def isTypeAliasDeclaration(node: js.Dynamic) = ts.isTypeAliasDeclaration(node)
  def isObjectLiteralExpression(node: js.Dynamic) = ts.isObjectLiteralExpression(node)
  def isLiteralTypeNode(node: js.Dynamic) = ts.isLiteralTypeNode(node)
  def isStringLiteral(node: js.Dynamic) = ts.isStringLiteral(node)
  def isVariableDeclaration(node: js.Dynamic) = ts.isVariableDeclaration(node)
  def isIndexSignatureDeclaration(node: js.Dynamic) = ts.isIndexSignatureDeclaration(node)
  def isConstructSignatureDeclaration(node: js.Dynamic) = ts.isConstructSignatureDeclaration(node)
  def isCallSignatureDeclaration(node: js.Dynamic) = ts.isCallSignatureDeclaration(node)

  def forEachChild(root: js.Dynamic, func: js.Dynamic => Unit) = ts.forEachChild(root, func)
  def createProgram(filenames: Seq[String]) =
    ts.createProgram(filenames.toJSArray, js.Dictionary("maxNodeModuleJsDepth" -> 0, "target" -> ts.ScriptTarget.ES5, "module" -> ts.ModuleKind.CommonJS))

  def resolveNodeModulePath(path: String): String = resolver(path).toString()
}

class TSTypeChecker(checker: js.Dynamic) {
  def getReturnTypeOfSignature(node: js.Dynamic) = checker.getReturnTypeOfSignature(checker.getSignatureFromDeclaration(node))
  def getTypeFromTypeNode(node: js.Dynamic) = checker.getTypeFromTypeNode(node)
  def getTypeOfSymbolAtLocation(sym: js.Dynamic, node: js.Dynamic) = checker.getTypeOfSymbolAtLocation(sym, node)
  def getPropertiesOfType(tp: js.Dynamic) = checker.getPropertiesOfType(tp)

  def isImplementationOfOverload(node: js.Dynamic) = checker.isImplementationOfOverload(node)
  def typeToTypeNode(tp: js.Dynamic) = checker.typeToTypeNode(tp)
  def getTypeArguments(tp: js.Dynamic) = checker.getTypeArguments(tp)
  def getElementTypeOfArrayType(tp: js.Dynamic) = checker.getElementTypeOfArrayType(tp)
  def isOptionalParameter(node: js.Dynamic) = checker.isOptionalParameter(node)
  def getTypeAtLocation(node: js.Dynamic) = checker.getTypeAtLocation(node)
  def getBaseType(tp: js.Dynamic) = checker.getBaseTypeOfLiteralType(tp)
}

object TSTypeChecker {
  def apply(checker: js.Dynamic) = new TSTypeChecker(checker)
}

class TSSymbolObject(sym: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(sym) {
  private lazy val flags = sym.flags
  lazy val parent = TSSymbolObject(sym.parent)

  // the first declaration of this symbol
  // if there is no overloading, there is only one declaration
  lazy val declaration =
    if (declarations.isUndefined) TSNodeObject(g.undefined)
    else declarations.get(0)
  lazy val escapedName: String = sym.escapedName.toString
  lazy val declarations = TSNodeArray(sym.declarations)
  lazy val `type` = TSTypeObject(sym.selectDynamic("type"))

  lazy val isOptionalMember = (flags & TypeScript.symbolFlagsOptional) > 0
}

object TSSymbolObject {
  def apply(node: js.Dynamic)(implicit checker: TSTypeChecker) = new TSSymbolObject(node)
}

class TSNodeObject(node: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(node) {
  private lazy val modifiers = TSTokenArray(node.modifiers)
  private lazy val parent = TSNodeObject(node.parent)

  lazy val isToken = TypeScript.isToken(node)
  lazy val isClassDeclaration = TypeScript.isClassDeclaration(node)
  lazy val isInterfaceDeclaration = TypeScript.isInterfaceDeclaration(node)
  lazy val isFunctionLike = TypeScript.isFunctionLike(node)
  lazy val isTypeAliasDeclaration = TypeScript.isTypeAliasDeclaration(node)
  lazy val isLiteralTypeNode = TypeScript.isLiteralTypeNode(node)
  lazy val isVariableDeclaration = TypeScript.isVariableDeclaration(node)
  lazy val isIndexSignature = TypeScript.isIndexSignatureDeclaration(node)
  lazy val isCallSignature = TypeScript.isCallSignatureDeclaration(node)
  lazy val isConstructSignature = TypeScript.isConstructSignatureDeclaration(node)
  lazy val isObjectLiteral = !initializer.isUndefined && !initializer.isToken &&
                             TypeScript.isObjectLiteralExpression(node.initializer)

  // `TypeScript.isModuleDeclaration` works on both namespaces and modules
  // but namespaces are more recommended, so we merely use `isNamespace` here
  lazy val isNamespace = TypeScript.isModuleDeclaration(node)
  lazy val isArrayTypeNode = TypeScript.isArrayTypeNode(node)
  lazy val isTupleTypeNode = TypeScript.isTupleTypeNode(node)
  lazy val isImplementationOfOverload = checker.isImplementationOfOverload(node)
  lazy val isImportDeclaration = TypeScript.isImportDeclaration(node)
  lazy val isSourceFile = TypeScript.isSourceFile(node)
  lazy val isExportDeclaration = TypeScript.isExportDeclaration(node)

  // if a node has an initializer or is marked by a question notation it is optional
  // e.g. `function f(x?: int) {}`, we can use it directly: `f()`.
  // in this case, there would be a question token.
  // e.g. `function f(x: int = 42) {}`, we can use it directly: `f()`.
  // in this case, the initializer would store the default value and be non-empty.
  lazy val isOptionalParameter = checker.isOptionalParameter(node)
  lazy val isStatic = if (modifiers.isUndefined) false
                     else modifiers.foldLeft(false)((s, t) => t.isStatic)
  lazy val isExported = if (modifiers.isUndefined) false
                     else modifiers.foldLeft(false)((s, t) => t.isExported)

  lazy val typeNode = TSTypeObject(checker.getTypeFromTypeNode(node))
  lazy val typeAtLocation = TSTypeObject(checker.getTypeAtLocation(node))
  lazy val symbol = TSSymbolObject(node.symbol)
  lazy val parameters = TSNodeArray(node.parameters)
  lazy val typeParameters = TSNodeArray(node.typeParameters)
  lazy val constraint = TSTokenObject(node.constraint)
  lazy val members = TSNodeArray(node.members)
  lazy val properties = TSNodeArray(node.properties)
  lazy val types = TSNodeArray(node.types)
  lazy val heritageClauses = TSNodeArray(node.heritageClauses)
  lazy val initializer = TSNodeObject(node.initializer)
  lazy val initToken = TSTokenObject(node.initializer) // for object literal, the initializer is a token.
  lazy val modifier =
    if (modifiers.isUndefined) Public
    else modifiers.foldLeft[TSAccessModifier](Public)(
      (m, t) => if (t.isPrivate) Private else if (t.isProtected) Protected else m)

  lazy val declarationList = TSNodeObject(node.declarationList)
  lazy val declarations = TSNodeArray(node.declarations)
  lazy val declaration =
    if (declarations.isUndefined) TSNodeObject(g.undefined)
    else declarations.get(0)

  lazy val locals = TSSymbolMap(node.locals)
  lazy val exports = TSSymbolMap(node.symbol.exports)
  lazy val returnType = TSTypeObject(checker.getReturnTypeOfSignature(node))
  lazy val `type` = TSNodeObject(node.selectDynamic("type"))

  lazy val symbolType = TSTypeObject(checker.getTypeOfSymbolAtLocation(node.symbol, node))
  lazy val literal = TSTokenObject(node.literal)
  lazy val name = TSIdentifierObject(node.name)

  // TODO: multiline string support
  override def toString(): String = node.getText().toString().replaceAll("\n", " ")
  lazy val filename: String =
    if (parent.isUndefined) node.fileName.toString()
    else parent.filename
  lazy val pos = node.pos

  lazy val moduleSpecifier = TSTokenObject(node.moduleSpecifier)
  lazy val importClause = TSNodeObject(node.importClause)
  lazy val namedBindings = TSNodeObject(node.namedBindings)
  lazy val elements = TSNodeArray(node.elements)
  lazy val propertyName = TSIdentifierObject(node.propertyName)
  lazy val exportClause = TSNodeObject(node.exportClause)
  lazy val resolvedPath: String = node.resolvedPath.toString()
}

object TSNodeObject {
  def apply(node: js.Dynamic)(implicit checker: TSTypeChecker) = new TSNodeObject(node)
}

class TSTokenObject(token: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(token) {
  private lazy val kind = token.kind

  lazy val isPrivate = kind == TypeScript.syntaxKindPrivate
  lazy val isProtected = kind == TypeScript.syntaxKindProtected
  lazy val isStatic = kind == TypeScript.syntaxKindStatic
  lazy val isExported = kind == TypeScript.syntaxKindExport

  lazy val typeNode = TSTypeObject(checker.getTypeFromTypeNode(token))
  lazy val text = token.text.toString()
  lazy val isStringLiteral = TypeScript.isStringLiteral(token)
}

object TSTokenObject {
  def apply(token: js.Dynamic)(implicit checker: TSTypeChecker) = new TSTokenObject(token)
}

class TSTypeObject(obj: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(obj) {
  private lazy val flags = obj.flags
  private lazy val objectFlags = if (IsUndefined(obj.objectFlags)) 0 else obj.objectFlags
  private lazy val baseType = TSTypeObject(checker.getBaseType(obj))
  private lazy val root =
    if (!IsUndefined(obj.root)) TSNodeObject(obj.root.node)
    else if (!`type`.isUndefined && !`type`.symbol.isUndefined && !`type`.symbol.declaration.isUndefined)
      `type`.symbol.declaration
    else TSNodeObject(obj.declaration)

  lazy val symbol = TSSymbolObject(obj.symbol)
  lazy val typeArguments = TSTypeArray(checker.getTypeArguments(obj))
  lazy val intrinsicName: String =
    if (!IsUndefined(obj.intrinsicName)) obj.intrinsicName.toString
    else baseType.intrinsicName

  lazy val `type` = TSTypeObject(obj.selectDynamic("type"))
  lazy val types = TSTypeArray(obj.types)
  lazy val properties = TSSymbolArray(checker.getPropertiesOfType(obj))
  lazy val node = TSNodeObject(checker.typeToTypeNode(obj))
  lazy val elementTypeOfArray = TSTypeObject(checker.getElementTypeOfArrayType(obj))

  lazy val isTupleType = node.isTupleTypeNode
  lazy val isArrayType = node.isArrayTypeNode
  lazy val isEnumType = (flags & TypeScript.typeFlagsEnumLike) > 0
  lazy val isUnionType = obj.isUnion()
  lazy val isIntersectionType = obj.isIntersection()
  lazy val isFunctionLike = node.isFunctionLike
  lazy val isAnonymous = objectFlags == TypeScript.objectFlagsAnonymous
  lazy val isMapped = objectFlags == TypeScript.objectFlagsMapped // mapping a type to another by using `keyof` and so on
  lazy val isTypeParameter = flags == TypeScript.typeFlagsTypeParameter
  lazy val isObject = flags == TypeScript.typeFlagsObject
  lazy val isTypeParameterSubstitution = isObject && typeArguments.length > 0
  lazy val isConditionalType = flags == TypeScript.typeFlagsConditional
  lazy val isIndexType = flags == TypeScript.typeFlagsIndex
  lazy val isIndexedAccessType = flags == TypeScript.typeFlagsIndexedAccess

  override def toString(): String = root.toString()
  lazy val filename = root.filename
  lazy val pos = root.pos
}

object TSTypeObject {
  def apply(obj: js.Dynamic)(implicit checker: TSTypeChecker) = new TSTypeObject(obj)
}

class TSIdentifierObject(id: js.Dynamic) extends TSAny(id) {
  lazy val escapedText: String = id.escapedText.toString()
}

object TSIdentifierObject {
  def apply(id: js.Dynamic) = new TSIdentifierObject(id)
}
