package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

trait TSTypeSource {}

object TypeScript {
  private lazy val ts = g.require("typescript")

  lazy val typeFlagsUnion = ts.TypeFlags.Union.asInstanceOf[Int]
  lazy val typeFlagsInter = ts.TypeFlags.Intersection.asInstanceOf[Int]
  lazy val syntaxKindPrivate = ts.SyntaxKind.PrivateKeyword.asInstanceOf[Int]
  lazy val syntaxKindProtected = ts.SyntaxKind.ProtectedKeyword.asInstanceOf[Int]
  lazy val syntaxKindStatic = ts.SyntaxKind.StaticKeyword.asInstanceOf[Int]

  def isToken(node: js.Dynamic): Boolean = ts.isToken(node)
  def isFunctionDeclaration(node: js.Dynamic): Boolean = ts.isFunctionDeclaration(node)
  def isClassDeclaration(node: js.Dynamic): Boolean = ts.isClassDeclaration(node)
  def isInterfaceDeclaration(node: js.Dynamic): Boolean = ts.isInterfaceDeclaration(node)
  def isFunctionTypeNode(node: js.Dynamic): Boolean = ts.isFunctionTypeNode(node)
  def isFunctionLike(node: js.Dynamic): Boolean = ts.isFunctionLike(node)
  def isArrayTypeNode(node: js.Dynamic): Boolean = ts.isArrayTypeNode(node)
  def isMethodDeclaration(node: js.Dynamic): Boolean = ts.isMethodDeclaration(node)
  def isNamespaceDeclaration(node: js.Dynamic): Boolean = ts.isModuleDeclaration(node)
  def isTupleTypeNode(node: js.Dynamic): Boolean = ts.isTupleTypeNode(node)
  def isUnionTypeNode(node: js.Dynamic): Boolean = ts.isUnionTypeNode(node)
  def isIntersectionTypeNode(node: js.Dynamic): Boolean = ts.isIntersectionTypeNode(node)

  def forEachChild(root: js.Dynamic, func: js.Dynamic => Unit): Unit = ts.forEachChild(root, func)
  def createProgram(filenames: Seq[String]): js.Dynamic = 
    ts.createProgram(filenames.toJSArray, js.Dictionary("maxNodeModuleJsDepth" -> 0, "target" -> ts.ScriptTarget.ES5, "module" -> ts.ModuleKind.CommonJS))

  def getJSDocTags(node: js.Dynamic): js.Dynamic = ts.getJSDocTags(node)
}

class TSTypeChecker(checker: js.Dynamic) {
  def getTypeOfSymbolAtLocation(sym: js.Dynamic): String =
    checker.typeToString(checker.getTypeOfSymbolAtLocation(sym, sym.valueDeclaration)).toString

  def getSignatureFromDeclaration(node: js.Dynamic) = checker.getSignatureFromDeclaration(node)
  def getReturnTypeOfSignature(signature: js.Dynamic) = checker.getReturnTypeOfSignature(signature)
  def getTypeFromTypeNode(token: js.Dynamic) = TSTypeObject(checker.getTypeFromTypeNode(token))
}

object TSTypeChecker {
  def apply(checker: js.Dynamic) = new TSTypeChecker(checker)
}

class TSSymbolObject(sym: js.Dynamic) extends TSAny(sym) {
  lazy val declaration =
    if (js.isUndefined(sym)) TSNodeObject(sym)
    else if (declarations.isUndefined) TSNodeObject(sym.declarations)
    else declarations.get(0)
  lazy val escapedName: String = sym.escapedName.toString
  lazy val valueDeclaration: TSNodeObject = TSNodeObject(sym.valueDeclaration)
  lazy val exports = TSSymbolIter(sym.exports.entries())
  lazy val parent = TSSymbolObject(sym.parent)
  lazy val declarations = TSNodeArray(sym.declarations)

  def getType()(implicit checker: TSTypeChecker): String = checker.getTypeOfSymbolAtLocation(sym)

  def getFullName(): String =
    if (parent.isUndefined ||
        parent.escapedName.equals("undefined") ||
        parent.escapedName.equals("") ||
        !parent.declaration.isNamespace) escapedName
    else s"${parent.getFullName}'$escapedName"
}

object TSSymbolObject {
  def apply(node: js.Dynamic) = new TSSymbolObject(node)
}

case class TSNodeObject(node: js.Dynamic) extends TSAny(node) with TSTypeSource {
  lazy val isToken: Boolean = TypeScript.isToken(node)
  lazy val isFunctionDeclaration: Boolean = !isUndefined && TypeScript.isFunctionDeclaration(node)
  lazy val isClassDeclaration: Boolean = !isUndefined && TypeScript.isClassDeclaration(node)
  lazy val isInterfaceDeclaration: Boolean = !isUndefined && TypeScript.isInterfaceDeclaration(node)
  lazy val isFunctionTypeNode: Boolean = !isUndefined && TypeScript.isFunctionTypeNode(node)
  lazy val isFunctionLike: Boolean = !isUndefined && TypeScript.isFunctionLike(node)
  lazy val isArrayTypeNode: Boolean = !isUndefined && TypeScript.isArrayTypeNode(node)
  lazy val isMethodDeclaration: Boolean = !isUndefined && TypeScript.isMethodDeclaration(node)
  lazy val isNamespace: Boolean = !isUndefined && TypeScript.isNamespaceDeclaration(node)
  lazy val isTupleTypeNode: Boolean = !isUndefined && TypeScript.isTupleTypeNode(node)
  lazy val isUnionTypeNode: Boolean = !isUndefined && TypeScript.isUnionTypeNode(node)
  lazy val isIntersectionTypeNode: Boolean = !isUndefined && TypeScript.isIntersectionTypeNode(node)
  lazy val hasTypeName: Boolean = !isUndefined && !typeName.isUndefined
  lazy val flags: Int = node.flags.asInstanceOf[Int]

  lazy val typeName = TSIdentifierObject(node.typeName)
  lazy val symbol = TSSymbolObject(node.symbol)
  lazy val parameters = TSNodeArray(node.parameters)
  lazy val typeParameters = TSNodeArray(node.typeParameters)
  lazy val constraint: TSTokenObject = TSTokenObject(node.constraint)
  lazy val members = TSNodeArray(node.members)
  lazy val properties =  TSNodeArray(node.properties)
  lazy val types = TSNodeArray(node.types)
  lazy val typesToken = TSTokenArray(node.types) // for inherit and union
  lazy val elementType = TSTokenObject(node.elementType)
  lazy val heritageClauses = TSNodeArray(node.heritageClauses)
  lazy val elements = TSTokenArray(node.elements)
  lazy val typeToken = TSTokenObject(node.selectDynamic("type")) // for interfaces
  lazy val questionToken = TSTokenObject(node.questionToken)
  lazy val initializer = TSTokenObject(node.initializer)
  lazy val initializerNode = TSNodeObject(node.initializer) // for inner class
  lazy val body = TSNodeObject(node.body)
  lazy val typeArguments = TSTokenArray(node.typeArguments)
  lazy val expression: Either[TSNodeObject, TSIdentifierObject] =
    if (js.isUndefined(node.expression.name)) Right(TSIdentifierObject(node.expression))
    else Left(TSNodeObject(node.expression))
  lazy val modifiers = TSTokenArray(node.modifiers)
  lazy val dotDotDot = TSTokenObject(node.dotDotDotToken)
  lazy val name = TSIdentifierObject(node.name)
  lazy val locals = TSSymbolIter(node.locals.entries())

  private lazy val tagName =
    if (isUndefined) TSIdentifierObject(node) else TSIdentifierObject(node.tagName)

  def getReturnTypeOfSignature()(implicit checker: TSTypeChecker): TSTypeObject = {
    val signature = checker.getSignatureFromDeclaration(node)
    TSTypeObject(checker.getReturnTypeOfSignature(signature))
  }

  private def getTypeField(t: TSNodeObject): TSNodeObject =
    if (t.isUndefined || !t.parameters.isUndefined || t.`type`.isUndefined || t.`type`.isToken) t else t.`type`

  def `type`(): TSNodeObject = getTypeField(TSNodeObject(node.selectDynamic("type")))

  def isDebugging(): Boolean = {
    val tags = TSNodeArray(TypeScript.getJSDocTags(node))
    if (!tags.isUndefined) {
      val tag = tags.get(0).tagName
      if (tag.isUndefined) false else tag.escapedText.equals("debug")
    }
    else false
  }
}

object TSNodeObject {
  def apply(node: js.Dynamic) = new TSNodeObject(node)
}

class TSTokenObject(token: js.Dynamic) extends TSAny(token) {
  private lazy val kind = token.kind.asInstanceOf[Int]
  lazy val expression = TSIdentifierObject(token.expression)
  lazy val isPrivate = kind == TypeScript.syntaxKindPrivate
  lazy val isProtected = kind == TypeScript.syntaxKindProtected
  lazy val isStatic = kind == TypeScript.syntaxKindStatic

  def getTypeFromTypeNode()(implicit checker: TSTypeChecker): TSTypeObject = checker.getTypeFromTypeNode(token)
}

object TSTokenObject {
  def apply(token: js.Dynamic) = new TSTokenObject(token)
}

class TSTypeObject(obj: js.Dynamic) extends TSAny(obj) with TSTypeSource {
  lazy val symbol: TSSymbolObject = TSSymbolObject(obj.symbol)
  lazy val resolvedTypeArguments = TSTypeArray(obj.resolvedTypeArguments)
  lazy val intrinsicName: String = if (js.isUndefined(obj.intrinsicName)) null else obj.intrinsicName.toString
  lazy val aliasSymbol: TSSymbolObject = TSSymbolObject(obj.aliasSymbol)
  lazy val types = TSTypeArray(obj.types)

  lazy val flags = obj.flags.asInstanceOf[Int]

  lazy val isTupleType: Boolean = obj.checker.isTupleType(obj)
  lazy val isArrayType: Boolean = obj.checker.isArrayType(obj)
  lazy val isEnumType: Boolean = !aliasSymbol.isUndefined && obj.aliasSymbol.hasOwnProperty("exports")
  lazy val isUnionType: Boolean = flags == TypeScript.typeFlagsUnion
  lazy val isIntersectionType: Boolean = flags == TypeScript.typeFlagsInter
  lazy val declaration: TSNodeObject = if (symbol.isUndefined) TSNodeObject(obj.symbol) else symbol.declaration
}

object TSTypeObject {
  def apply(obj: js.Dynamic) = new TSTypeObject(obj)
}

class TSIdentifierObject(id: js.Dynamic) extends TSAny(id) {
  private lazy val left = TSIdentifierObject(id.left)
  private lazy val right = TSIdentifierObject(id.right)

  def escapedText(): String =
    if (left.isUndefined) id.escapedText.toString
    else s"${left.escapedText}'${right.escapedText}"
}

object TSIdentifierObject {
  def apply(id: js.Dynamic) = new TSIdentifierObject(id)
}