package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.Type
import mlscript.JSClassDecl

trait RuntimeSymbol {
  def runtimeName: Str
}

// trait TypeSymbol {
//   def baseType: Ls[Str] -> Type
//   def isParametric: Bool
// }

abstract class LexicalSymbol extends RuntimeSymbol {
  /**
    * The lexical name of the symbol. This is different from the runtime name,
    * the name of the symbol in the generated code. We allow duplicates lexical
    * names in the same scope.
    */
  def lexicalName: Str

  /**
    * A short name for the declaration used in debugging and error messages.
    */
  def shortName: Str

  /**
    * Currently, this is the number of the test block in which it is defined.
    * TODO: use a generic block number when we need to support source maps.
    */
  var location: Int = 0
}

class ValueSymbol(val lexicalName: Str, val runtimeName: Str) extends LexicalSymbol {
  def shortName: Str = s"value $lexicalName"
}

object ValueSymbol {
  def apply(lexicalName: Str, runtimeName: Str): ValueSymbol =
    new ValueSymbol(lexicalName, runtimeName)
}

class TypeSymbol(
    val lexicalName: Str,
    val runtimeName: Str,
    val params: Ls[Str],
    val actualType: Type
) extends LexicalSymbol {
  def shortName: Str = s"type $lexicalName"
}

object TypeSymbol {
  def apply(lexicalName: Str, runtimeName: Str, params: Ls[Str], body: Type): TypeSymbol =
    new TypeSymbol(lexicalName, runtimeName, params, body)
}

/**
  * The not-found symbol.
  */
final case class FreeSymbol(val lexicalName: Str) extends LexicalSymbol {
  override def runtimeName: Str = throw new CodeGenError("free symbol has no runtime name")
  def shortName: Str = s"free $lexicalName"
}

final case class TemporarySymbol(val runtimeName: Str) extends RuntimeSymbol

final case class BuiltinSymbol(override val lexicalName: Str, feature: Str)
    extends ValueSymbol(lexicalName, lexicalName) {
  override def shortName: Str = s"function $lexicalName"
}

final case class StubValueSymbol(override val lexicalName: Str, override val runtimeName: Str)
    extends ValueSymbol(lexicalName, runtimeName) {
  override def shortName: Str = s"value $lexicalName"
}

final case class ClassSymbol(
    override val lexicalName: Str,
    override val runtimeName: Str,
    override val params: Ls[Str],
    val base: Type,
    enclosingScope: Scope
) extends TypeSymbol(lexicalName, runtimeName, params, base) {
  private val scope = enclosingScope.derive(s"class $lexicalName")

  def declareMember(name: Str): ValueSymbol = scope.declareValue(name)

  def declareStubMember(name: Str): StubValueSymbol = scope.declareStubValue(name)

  /**
    * Fill up this field after the class translation.
    */
  var body: Opt[JSClassDecl] = N

  /**
    * Fill up this field after resolving classes.
    */
  var baseClass: Opt[ClassSymbol] = N

  /**
    * Fill up this field after resolving classes.
    */
  var fields: Ls[Str] = Nil

  /**
    * Fill up this field after sorting.
    */
  var order: Int = 0

  override def shortName: Str = s"class $lexicalName"
}

final case class TraitSymbol(
    override val lexicalName: Str,
    override val runtimeName: Str,
    override val params: Ls[Str],
    base: Type
) extends TypeSymbol(lexicalName, runtimeName, params, base) {
  override def shortName: Str = s"trait $lexicalName"
}

final case class ParamSymbol(override val lexicalName: Str, override val runtimeName: Str)
    extends ValueSymbol(lexicalName, runtimeName) {
  override def shortName: Str = s"parameter $lexicalName"
}

object Symbol {
  def isKeyword(name: Str): Bool = keywords contains name

  private val keywords: Set[Str] = Set(
    // Reserved keywords as of ECMAScript 2015
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "export",
    "extends",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    // The following are reserved as future keywords by the ECMAScript specification.
    // They have no special functionality at present, but they might at some future time,
    // so they cannot be used as identifiers. These are always reserved:
    "enum",
    // The following are only reserved when they are found in strict mode code:
    "abstract",
    "boolean",
    "byte",
    "char",
    "double",
    "final",
    "float",
    "goto",
    "int",
    "long",
    "native",
    "short",
    "synchronized",
    "throws",
    "transient",
    "volatile",
  )
}
