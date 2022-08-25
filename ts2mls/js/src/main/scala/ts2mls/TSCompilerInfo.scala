package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

abstract class TSAny(v: js.Dynamic) {
  val isUndefined: Boolean = js.isUndefined(v)
}

// array for information object in tsc
abstract class TSArray[T <: TSAny](arr: js.Dynamic) extends TSAny(arr) {
  def get(index: Int): T = ???
  lazy val length: Int = arr.length.asInstanceOf[Int]

  def foldLeft[U](init: U, index: Int = 0)(implicit f: (U, T) => U): U =
    if (isUndefined) init
    else if (index < length) foldLeft(f(init, get(index)), index + 1)
    else init

  def foldLeftIndexed[U](init: U, index: Int = 0)(implicit f: (U, T, Int) => U): U =
    if (isUndefined) init
    else if (index < length) foldLeftIndexed(f(init, get(index), index), index + 1)
    else init

  def foreach(f: T => Unit, index: Int = 0): Unit =
    if (!isUndefined)
      if (index < length) {
        f(get(index))
        foreach(f, index + 1)
      }
}

class TSNodeArray(arr: js.Dynamic) extends TSArray[TSNodeObject](arr) {
  override def get(index: Int) = TSNodeObject(arr.selectDynamic(index.toString))
}

object TSNodeArray {
  def apply(arr: js.Dynamic) = new TSNodeArray(arr)
}

class TSTokenArray(arr: js.Dynamic) extends TSArray[TSTokenObject](arr) {
  override def get(index: Int) = TSTokenObject(arr.selectDynamic(index.toString))
}

object TSTokenArray {
  def apply(arr: js.Dynamic) = new TSTokenArray(arr)
}

class TSTypeArray(arr: js.Dynamic) extends TSArray[TSTypeObject](arr) {
  override def get(index: Int) = TSTypeObject(arr.selectDynamic(index.toString))
}

object TSTypeArray {
  def apply(arr: js.Dynamic) = new TSTypeArray(arr)
}

class TSSymbolMap(map: js.Dynamic) extends TSAny(map) {
  def foreach(f: TSSymbolObject => Unit): Unit =
    if (!isUndefined){
      val jsf: js.Function1[js.Dynamic, js.Any] =
        { (s: js.Dynamic) => f(TSSymbolObject(s)) }
      map.forEach(jsf)
    }
}

object TSSymbolMap {
  def apply(map: js.Dynamic) = new TSSymbolMap(map)
}

object TypeScript {
  private val ts = g.require("typescript")

  val typeFlagsUnion = ts.TypeFlags.Union.asInstanceOf[Int]
  val typeFlagsInter = ts.TypeFlags.Intersection.asInstanceOf[Int]
  val syntaxKindPrivate = ts.SyntaxKind.PrivateKeyword.asInstanceOf[Int]
  val syntaxKindProtected = ts.SyntaxKind.ProtectedKeyword.asInstanceOf[Int]
  val syntaxKindStatic = ts.SyntaxKind.StaticKeyword.asInstanceOf[Int]

  def isToken(node: js.Dynamic): Boolean = ts.isToken(node)
  def isFunctionDeclaration(node: js.Dynamic): Boolean = ts.isFunctionDeclaration(node)
  def isClassDeclaration(node: js.Dynamic): Boolean = ts.isClassDeclaration(node)
  def isInterfaceDeclaration(node: js.Dynamic): Boolean = ts.isInterfaceDeclaration(node)
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
}

object TSTypeChecker {
  private var checker: js.Dynamic = null
  def init(obj: js.Dynamic): Unit = checker = obj

  def getTypeOfSymbolAtLocation(sym: js.Dynamic): String =
    if (js.isUndefined(sym) || js.isUndefined(sym.valueDeclaration)) "null" // only null type has no valueDeclaration
    else checker.typeToString(checker.getTypeOfSymbolAtLocation(sym, sym.valueDeclaration)).toString

  def getSignatureFromDeclaration(node: js.Dynamic) = checker.getSignatureFromDeclaration(node)
  def getReturnTypeOfSignature(signature: js.Dynamic) = checker.getReturnTypeOfSignature(signature)
  def getTypeFromTypeNode(token: js.Dynamic) = TSTypeObject(checker.getTypeFromTypeNode(token))
}

class TSSymbolObject(sym: js.Dynamic) extends TSAny(sym) {
  private lazy val parent = TSSymbolObject(sym.parent)
  
  lazy val declaration =
    if (isUndefined) TSNodeObject(sym)
    else if (declarations.isUndefined) TSNodeObject(sym.declarations)
    else declarations.get(0)
  lazy val escapedName: String = sym.escapedName.toString
  lazy val valueDeclaration = TSNodeObject(sym.valueDeclaration)
  lazy val declarations = TSNodeArray(sym.declarations)

  def getType(): String = TSTypeChecker.getTypeOfSymbolAtLocation(sym)

  def getFullName(): String =
    if (parent.isUndefined ||
        parent.escapedName.equals("undefined") ||
        parent.escapedName.equals("") ||
        !parent.declaration.isNamespace) escapedName
    else s"${parent.getFullName()}'$escapedName"
}

object TSSymbolObject {
  def apply(node: js.Dynamic) = new TSSymbolObject(node)
}

case class TSNodeObject(val node: js.Dynamic) extends TSAny(node) {
  lazy val isToken = TypeScript.isToken(node)
  lazy val token = TSTokenObject(node)
  lazy val isFunctionDeclaration = !isUndefined && TypeScript.isFunctionDeclaration(node)
  lazy val isClassDeclaration = !isUndefined && TypeScript.isClassDeclaration(node)
  lazy val isInterfaceDeclaration = !isUndefined && TypeScript.isInterfaceDeclaration(node)
  lazy val isFunctionLike = !isUndefined && TypeScript.isFunctionLike(node)
  lazy val isArrayTypeNode = !isUndefined && TypeScript.isArrayTypeNode(node)
  lazy val isMethodDeclaration = !isUndefined && TypeScript.isMethodDeclaration(node)
  lazy val isNamespace = !isUndefined && TypeScript.isNamespaceDeclaration(node)
  lazy val isTupleTypeNode = !isUndefined && TypeScript.isTupleTypeNode(node)
  lazy val isUnionTypeNode = !isUndefined && TypeScript.isUnionTypeNode(node)
  lazy val isIntersectionTypeNode = !isUndefined && TypeScript.isIntersectionTypeNode(node)

  lazy val typeName = TSIdentifierObject(node.typeName)
  lazy val symbol = TSSymbolObject(node.symbol)
  lazy val parameters = TSNodeArray(node.parameters)
  lazy val typeParameters = TSNodeArray(node.typeParameters)
  lazy val constraint = TSTokenObject(node.constraint)
  lazy val members = TSNodeArray(node.members)
  lazy val properties =  TSNodeArray(node.properties)
  lazy val types = TSNodeArray(node.types)
  lazy val typesToken = TSTokenArray(node.types) // for inherit and union
  lazy val elementType = TSTokenObject(node.elementType)
  lazy val heritageClauses = TSNodeArray(node.heritageClauses)
  lazy val elements = TSTokenArray(node.elements)
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
  lazy val locals = TSSymbolMap(node.locals)

  def getReturnTypeOfSignature() =
    TSTypeObject(TSTypeChecker.getReturnTypeOfSignature(TSTypeChecker.getSignatureFromDeclaration(node)))

  lazy val `type` = TSNodeObject(node.selectDynamic("type"))
}

object TSNodeObject {
  def apply(node: js.Dynamic) = new TSNodeObject(node)
}

class TSTokenObject(token: js.Dynamic) extends TSAny(token) {
  private lazy val kind = token.kind.asInstanceOf[Int]

  lazy val isPrivate = kind == TypeScript.syntaxKindPrivate
  lazy val isProtected = kind == TypeScript.syntaxKindProtected
  lazy val isStatic = kind == TypeScript.syntaxKindStatic

  def getTypeFromTypeNode() = TSTypeChecker.getTypeFromTypeNode(token)
}

object TSTokenObject {
  def apply(token: js.Dynamic) = new TSTokenObject(token)
}

class TSTypeObject(obj: js.Dynamic) extends TSAny(obj) {
  private lazy val flags = obj.flags.asInstanceOf[Int]

  lazy val symbol = TSSymbolObject(obj.symbol)
  lazy val resolvedTypeArguments = TSTypeArray(obj.resolvedTypeArguments)
  lazy val intrinsicName = if (js.isUndefined(obj.intrinsicName)) null else obj.intrinsicName.toString
  lazy val aliasSymbol = TSSymbolObject(obj.aliasSymbol)
  lazy val types = TSTypeArray(obj.types)

  lazy val isTupleType = obj.checker.isTupleType(obj)
  lazy val isArrayType = obj.checker.isArrayType(obj)
  lazy val isEnumType = !aliasSymbol.isUndefined && obj.aliasSymbol.hasOwnProperty("exports")
  lazy val isUnionType = flags == TypeScript.typeFlagsUnion
  lazy val isIntersectionType = flags == TypeScript.typeFlagsInter
}

object TSTypeObject {
  def apply(obj: js.Dynamic) = new TSTypeObject(obj)
}

class TSIdentifierObject(id: js.Dynamic) extends TSAny(id) {
  private lazy val left = TSIdentifierObject(id.left)
  private lazy val right = TSIdentifierObject(id.right)

  def escapedText(): String =
    if (left.isUndefined) id.escapedText.toString
    else s"${left.escapedText()}'${right.escapedText()}"
}

object TSIdentifierObject {
  def apply(id: js.Dynamic) = new TSIdentifierObject(id)
}