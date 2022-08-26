package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import ts2mls.types._

object TypeScript {
  private val ts = g.require("typescript")

  val typeFlagsUnion = ts.TypeFlags.Union.asInstanceOf[Int]
  val typeFlagsInter = ts.TypeFlags.Intersection.asInstanceOf[Int]
  val typeFlagsEnum = ts.TypeFlags.Enum.asInstanceOf[Int]
  val typeFlagsObject = ts.TypeFlags.Object.asInstanceOf[Int]
  val typeFlagsTypeParameter = ts.TypeFlags.TypeParameter.asInstanceOf[Int]
  val syntaxKindPrivate = ts.SyntaxKind.PrivateKeyword.asInstanceOf[Int]
  val syntaxKindProtected = ts.SyntaxKind.ProtectedKeyword.asInstanceOf[Int]
  val syntaxKindStatic = ts.SyntaxKind.StaticKeyword.asInstanceOf[Int]

  def isToken(node: js.Dynamic): Boolean = ts.isToken(node)
  def isClassDeclaration(node: js.Dynamic): Boolean = ts.isClassDeclaration(node)
  def isInterfaceDeclaration(node: js.Dynamic): Boolean = ts.isInterfaceDeclaration(node)
  def isFunctionLike(node: js.Dynamic): Boolean = ts.isFunctionLike(node)
  def isArrayTypeNode(node: js.Dynamic): Boolean = ts.isArrayTypeNode(node)
  def isNamespaceDeclaration(node: js.Dynamic): Boolean = ts.isModuleDeclaration(node)
  def isTupleTypeNode(node: js.Dynamic): Boolean = ts.isTupleTypeNode(node)
  def isUnionTypeNode(node: js.Dynamic): Boolean = ts.isUnionTypeNode(node)
  def isIntersectionTypeNode(node: js.Dynamic): Boolean = ts.isIntersectionTypeNode(node)
  def isTypeReferenceNode(node: js.Dynamic): Boolean = ts.isTypeReferenceNode(node)

  def forEachChild(root: js.Dynamic, func: js.Dynamic => Unit): Unit = ts.forEachChild(root, func)
  def createProgram(filenames: Seq[String]): js.Dynamic = 
    ts.createProgram(filenames.toJSArray, js.Dictionary("maxNodeModuleJsDepth" -> 0, "target" -> ts.ScriptTarget.ES5, "module" -> ts.ModuleKind.CommonJS))
}

object TSTypeChecker {
  private var checker: js.Dynamic = null
  def init(obj: js.Dynamic): Unit = checker = obj

  def getTypeOfSymbolAtLocation(sym: js.Dynamic): String =
    if (IsUndefined(sym) || IsUndefined(sym.valueDeclaration)) "null" // only null type has no valueDeclaration
    else checker.typeToString(checker.getTypeOfSymbolAtLocation(sym, sym.valueDeclaration)).toString

  def getReturnTypeOfSignature(node: js.Dynamic) = checker.getReturnTypeOfSignature(checker.getSignatureFromDeclaration(node))
  def getTypeFromTypeNode(token: js.Dynamic) = TSTypeObject(checker.getTypeFromTypeNode(token))
}

class TSSymbolObject(sym: js.Dynamic) extends TSAny(sym) {
  private lazy val parent = TSSymbolObject(sym.parent)
  
  lazy val declaration =
    if (isUndefined) TSNodeObject(g.undefined)
    else if (declarations.isUndefined) TSNodeObject(g.undefined)
    else declarations.get(0)
  lazy val escapedName: String = sym.escapedName.toString
  lazy val valueDeclaration = TSNodeObject(sym.valueDeclaration)
  lazy val declarations = TSNodeArray(sym.declarations)

  lazy val symbolType: String = TSTypeChecker.getTypeOfSymbolAtLocation(sym)

  lazy val fullName: String =
    if (!parent.declaration.isNamespace) escapedName
    else s"${parent.fullName}'$escapedName"
}

object TSSymbolObject {
  def apply(node: js.Dynamic) = new TSSymbolObject(node)
}

case class TSNodeObject(node: js.Dynamic) extends TSAny(node) {
  private lazy val modifiers = TSTokenArray(node.modifiers)
  private lazy val name = TSIdentifierObject(node.name)
  private lazy val expression: Either[TSNodeObject, TSIdentifierObject] =
    if (js.isUndefined(node.expression.name)) Right(TSIdentifierObject(node.expression))
    else Left(TSNodeObject(node.expression))

  lazy val isToken = !isUndefined && TypeScript.isToken(node)
  lazy val isClassDeclaration = !isUndefined && TypeScript.isClassDeclaration(node)
  lazy val isInterfaceDeclaration = !isUndefined && TypeScript.isInterfaceDeclaration(node)
  lazy val isFunctionLike = !isUndefined && TypeScript.isFunctionLike(node)
  lazy val isArrayTypeNode = !isUndefined && TypeScript.isArrayTypeNode(node)
  lazy val isNamespace = !isUndefined && TypeScript.isNamespaceDeclaration(node)
  lazy val isTupleTypeNode = !isUndefined && TypeScript.isTupleTypeNode(node)
  lazy val isUnionTypeNode = !isUndefined && TypeScript.isUnionTypeNode(node)
  lazy val isIntersectionTypeNode = !isUndefined && TypeScript.isIntersectionTypeNode(node)
  lazy val isEnum = TypeScript.isTypeReferenceNode(node)
  lazy val isAnonymousInterface = !isUndefined && !symbol.isUndefined && symbol.escapedName.equals("__type")
  lazy val isTypeVariableSubstitution = !isUndefined && !typeArguments.isUndefined
  lazy val isDotsArray = !isUndefined && !hasTypeNode && !IsUndefined(node.dotDotDotToken)
  lazy val hasTypeNode = !isUndefined && (`type` match {
    case Left(node) => !node.isUndefined
    case Right(token) => !token.isUndefined
  })

  lazy val hasImplementation = !IsUndefined(node.body)
  lazy val isOptional = !IsUndefined(node.initializer) || !IsUndefined(node.questionToken)
  lazy val isStatic = if (modifiers.isUndefined) false
                     else modifiers.foldLeft(false)((s, t) => t.isStatic)

  lazy val typeName = TSIdentifierObject(node.typeName)
  lazy val symbol = TSSymbolObject(node.symbol)
  lazy val parameters = TSNodeArray(node.parameters)
  lazy val typeParameters = TSNodeArray(node.typeParameters)
  lazy val constraint = TSTokenObject(node.constraint)
  lazy val members = TSNodeArray(node.members)
  lazy val properties =  TSNodeArray(node.properties)
  lazy val types = TSNodeArray(node.types)
  lazy val typesToken = TSTokenArray(node.types) // for union
  lazy val elementType = TSTokenObject(node.elementType)
  lazy val heritageClauses = TSNodeArray(node.heritageClauses)
  lazy val elements = TSTokenArray(node.elements)
  lazy val initializer = TSNodeObject(node.initializer)
  lazy val typeArguments = TSTokenArray(node.typeArguments)
  lazy val modifier =
    if (modifiers.isUndefined) Public
    else modifiers.foldLeft[TSAccessModifier](Public)(
      (m, t) => if (t.isPrivate) Private else if (t.isProtected) Protected else m)

  lazy val locals = TSSymbolMap(node.locals)
  lazy val returnType = TSTypeObject(TSTypeChecker.getReturnTypeOfSignature(node))
  lazy val `type`: Either[TSNodeObject, TSTypeObject] = {
    val temp = TSNodeObject(node.selectDynamic("type"))
    if (temp.isToken) Right(TSTokenObject(temp.node).typeNode)
    else Left(temp)
  }

  lazy val fullName = {
    def getFullName(name: String, exp: Either[TSNodeObject, TSIdentifierObject]): String =
      exp match {
        case Left(node) =>
          if (name.equals("")) getFullName(node.name.escapedText, node.expression)
          else getFullName(s"${node.name.escapedText}'$name", node.expression)
        case Right(id) =>
          if (name.equals("")) id.escapedText
          else s"${id.escapedText}'$name"
      }

    getFullName("", expression)
  }

  def isTypeVariable()(implicit tv: Set[String]) = 
    !typeName.isUndefined && tv.contains(typeName.escapedText)

  def isSymbolName()(implicit ns: TSNamespace) = 
    !typeName.isUndefined && ns.containsMember(typeName.escapedText.split("'").toList)
}

object TSNodeObject {
  def apply(node: js.Dynamic) = new TSNodeObject(node)
}

class TSTokenObject(token: js.Dynamic) extends TSAny(token) {
  private lazy val kind = token.kind.asInstanceOf[Int]

  lazy val isPrivate = kind == TypeScript.syntaxKindPrivate
  lazy val isProtected = kind == TypeScript.syntaxKindProtected
  lazy val isStatic = kind == TypeScript.syntaxKindStatic

  lazy val typeNode = TSTypeChecker.getTypeFromTypeNode(token)
}

object TSTokenObject {
  def apply(token: js.Dynamic) = new TSTokenObject(token)
}

class TSTypeObject(obj: js.Dynamic) extends TSAny(obj) {
  private lazy val flags = obj.flags.asInstanceOf[Int]

  lazy val symbol = TSSymbolObject(obj.symbol)
  lazy val resolvedTypeArguments = TSTypeArray(obj.resolvedTypeArguments)
  lazy val intrinsicName = if (IsUndefined(obj.intrinsicName)) null else obj.intrinsicName.toString
  lazy val aliasSymbol = TSSymbolObject(obj.aliasSymbol)
  lazy val types = TSTypeArray(obj.types)
  lazy val declarationMembers =
    if (!symbol.declaration.isUndefined && !symbol.declaration.members.isUndefined)
      symbol.declaration.members
    else if (!symbol.valueDeclaration.isUndefined) symbol.valueDeclaration.properties
    else TSNodeArray(g.undefined)

  lazy val isTupleType = obj.checker.isTupleType(obj)
  lazy val isArrayType = obj.checker.isArrayType(obj)
  lazy val isEnumType = !aliasSymbol.isUndefined && obj.aliasSymbol.hasOwnProperty("exports")
  lazy val isUnionType = flags == TypeScript.typeFlagsUnion
  lazy val isIntersectionType = flags == TypeScript.typeFlagsInter
  lazy val isAnonymousInterface = !symbol.isUndefined && !declarationMembers.isUndefined
  lazy val isFunctionLike =
    !symbol.isUndefined && !symbol.declaration.isUndefined && symbol.declaration.isFunctionLike

  lazy val isTypeVariableSubstitution =
    !isUndefined && !resolvedTypeArguments.isUndefined && resolvedTypeArguments.length > 0

  def isSymbolName()(implicit ns: TSNamespace) =
    if (symbol.isUndefined) false
    else ns.containsMember(symbol.fullName.split("'").toList) || ns.containsMember(symbol.escapedName)

  def isTypeVariable()(implicit tv: Set[String]) = !symbol.isUndefined && tv.contains(symbol.escapedName)
}

object TSTypeObject {
  def apply(obj: js.Dynamic) = new TSTypeObject(obj)
}

class TSIdentifierObject(id: js.Dynamic) extends TSAny(id) {
  private lazy val left = TSIdentifierObject(id.left)
  private lazy val right = TSIdentifierObject(id.right)

  lazy val escapedText: String =
    if (left.isUndefined) id.escapedText.toString
    else s"${left.escapedText}'${right.escapedText}"
}

object TSIdentifierObject {
  def apply(id: js.Dynamic) = new TSIdentifierObject(id)
}