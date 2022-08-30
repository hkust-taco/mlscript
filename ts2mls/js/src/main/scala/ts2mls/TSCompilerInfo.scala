package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import ts2mls.types._

object TypeScript {
  private val ts = g.require("typescript")

  val typeFlagsEnumLike = ts.TypeFlags.EnumLike.asInstanceOf[Int]
  val typeFlagsObject = ts.TypeFlags.Object.asInstanceOf[Int]
  val typeFlagsTypeParameter = ts.TypeFlags.TypeParameter.asInstanceOf[Int]
  val syntaxKindPrivate = ts.SyntaxKind.PrivateKeyword.asInstanceOf[Int]
  val syntaxKindProtected = ts.SyntaxKind.ProtectedKeyword.asInstanceOf[Int]
  val syntaxKindStatic = ts.SyntaxKind.StaticKeyword.asInstanceOf[Int]
  val objectFlagsAnonymous = ts.ObjectFlags.Anonymous.asInstanceOf[Int]

  def isToken(node: js.Dynamic) = ts.isToken(node)
  def isClassDeclaration(node: js.Dynamic) = ts.isClassDeclaration(node)
  def isInterfaceDeclaration(node: js.Dynamic) = ts.isInterfaceDeclaration(node)
  def isFunctionLike(node: js.Dynamic) = ts.isFunctionLike(node)
  def isNamespaceDeclaration(node: js.Dynamic) = ts.isModuleDeclaration(node)
  def isArrayTypeNode(node: js.Dynamic) = ts.isArrayTypeNode(node)
  def isTupleTypeNode(node: js.Dynamic) = ts.isTupleTypeNode(node)

  def forEachChild(root: js.Dynamic, func: js.Dynamic => Unit) = ts.forEachChild(root, func)
  def createProgram(filenames: Seq[String]) = 
    ts.createProgram(filenames.toJSArray, js.Dictionary("maxNodeModuleJsDepth" -> 0, "target" -> ts.ScriptTarget.ES5, "module" -> ts.ModuleKind.CommonJS))
}

class TSTypeChecker(checker: js.Dynamic) {
  def getTypeStringOfSymbol(sym: js.Dynamic): String =
    checker.typeToString(getTypeOfSymbolAtLocation(sym, sym.valueDeclaration)).toString

  def getReturnTypeOfSignature(node: js.Dynamic) = checker.getReturnTypeOfSignature(checker.getSignatureFromDeclaration(node))
  def getTypeFromTypeNode(node: js.Dynamic) = checker.getTypeFromTypeNode(node)
  def getTypeOfSymbolAtLocation(sym: js.Dynamic, node: js.Dynamic) = checker.getTypeOfSymbolAtLocation(sym, node)
  def getPropertiesOfType(tp: js.Dynamic) = checker.getPropertiesOfType(tp)

  def isImplementationOfOverload(node: js.Dynamic) = checker.isImplementationOfOverload(node)
  def typeToTypeNode(tp: js.Dynamic) = checker.typeToTypeNode(tp)
  def getTypeArguments(tp: js.Dynamic) = checker.getTypeArguments(tp)
  def getElementTypeOfArrayType(tp: js.Dynamic) = checker.getElementTypeOfArrayType(tp)
}

object TSTypeChecker {
  def apply(checker: js.Dynamic) = new TSTypeChecker(checker)
}

class TSSymbolObject(sym: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(sym) {
  private lazy val parent = TSSymbolObject(sym.parent)

  // the first declaration of this symbol
  // if there is no overloading, there is only one declaration
  lazy val declaration =
    if (declarations.isUndefined) TSNodeObject(g.undefined)
    else declarations.get(0)
  lazy val escapedName: String = sym.escapedName.toString
  lazy val declarations = TSNodeArray(sym.declarations)

  lazy val symbolType: String = checker.getTypeStringOfSymbol(sym)

  // get the full name of the symbol that is declared in namespaces
  lazy val fullName: String =
    if (parent.isUndefined || !parent.declaration.isNamespace) escapedName
    else s"${parent.fullName}'$escapedName"
}

object TSSymbolObject {
  def apply(node: js.Dynamic)(implicit checker: TSTypeChecker) = new TSSymbolObject(node)
}

class TSNodeObject(node: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(node) {
  private lazy val modifiers = TSTokenArray(node.modifiers)

  lazy val isToken = TypeScript.isToken(node)
  lazy val isClassDeclaration = TypeScript.isClassDeclaration(node)
  lazy val isInterfaceDeclaration = TypeScript.isInterfaceDeclaration(node)
  lazy val isFunctionLike = TypeScript.isFunctionLike(node)
  lazy val isNamespace = TypeScript.isNamespaceDeclaration(node)
  lazy val hasTypeNode = !`type`.isUndefined
  lazy val isArrayTypeNode = TypeScript.isArrayTypeNode(node)
  lazy val isTupleTypeNode = TypeScript.isTupleTypeNode(node)
  lazy val isImplementationOfOverload = checker.isImplementationOfOverload(node)
  lazy val isOptional = !initializer.isUndefined || !IsUndefined(node.questionToken)
  lazy val isStatic = if (modifiers.isUndefined) false
                     else modifiers.foldLeft(false)((s, t) => t.isStatic)

  lazy val typeNode = TSTypeObject(checker.getTypeFromTypeNode(node))
  lazy val symbol = TSSymbolObject(node.symbol)
  lazy val parameters = TSNodeArray(node.parameters)
  lazy val typeParameters = TSNodeArray(node.typeParameters)
  lazy val constraint = TSTokenObject(node.constraint)
  lazy val members = TSNodeArray(node.members)
  lazy val types = TSNodeArray(node.types)
  lazy val heritageClauses = TSNodeArray(node.heritageClauses)
  lazy val initializer = TSNodeObject(node.initializer)
  lazy val modifier =
    if (modifiers.isUndefined) Public
    else modifiers.foldLeft[TSAccessModifier](Public)(
      (m, t) => if (t.isPrivate) Private else if (t.isProtected) Protected else m)

  lazy val locals = TSSymbolMap(node.locals)
  lazy val returnType = TSTypeObject(checker.getReturnTypeOfSignature(node))
  lazy val `type` = TSNodeObject(node.selectDynamic("type"))

  lazy val symbolType = TSTypeObject(checker.getTypeOfSymbolAtLocation(node.symbol, node))
}

object TSNodeObject {
  def apply(node: js.Dynamic)(implicit checker: TSTypeChecker) = new TSNodeObject(node)
}

class TSTokenObject(token: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(token) {
  private lazy val kind = token.kind.asInstanceOf[Int]

  lazy val isPrivate = kind == TypeScript.syntaxKindPrivate
  lazy val isProtected = kind == TypeScript.syntaxKindProtected
  lazy val isStatic = kind == TypeScript.syntaxKindStatic

  lazy val typeNode = TSTypeObject(checker.getTypeFromTypeNode(token))
}

object TSTokenObject {
  def apply(token: js.Dynamic)(implicit checker: TSTypeChecker) = new TSTokenObject(token)
}

class TSTypeObject(obj: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(obj) {
  private lazy val flags = obj.flags.asInstanceOf[Int]
  private lazy val objectFlags = if (IsUndefined(obj.objectFlags)) 0 else obj.objectFlags.asInstanceOf[Int]

  lazy val symbol = TSSymbolObject(obj.symbol)
  lazy val typeArguments = TSTypeArray(checker.getTypeArguments(obj))
  lazy val intrinsicName = obj.intrinsicName.toString
  lazy val types = TSTypeArray(obj.types)
  lazy val properties = TSSymbolArray(checker.getPropertiesOfType(obj))
  lazy val node = TSNodeObject(checker.typeToTypeNode(obj))
  lazy val elementTypeOfArray = TSTypeObject(checker.getElementTypeOfArrayType(obj))

  lazy val isTupleType = node.isTupleTypeNode
  lazy val isArrayType = node.isArrayTypeNode
  lazy val isEnumType = (flags & TypeScript.typeFlagsEnumLike) > 0
  lazy val isUnionType = obj.isUnion().asInstanceOf[Boolean]
  lazy val isIntersectionType = obj.isIntersection().asInstanceOf[Boolean]
  lazy val isFunctionLike = node.isFunctionLike
  lazy val isAnonymous = objectFlags == TypeScript.objectFlagsAnonymous
  lazy val isTypeParameter = flags == TypeScript.typeFlagsTypeParameter
  lazy val isObject = flags == TypeScript.typeFlagsObject
  lazy val isTypeParameterSubstitution = isObject && typeArguments.length > 0
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