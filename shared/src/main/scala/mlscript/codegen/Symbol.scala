package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.Type
import mlscript.JSClassDecl
import mlscript.MethodDef
import mlscript.Term

sealed trait LexicalSymbol {

  /**
    * The lexical name of the symbol. This is different from the runtime name,
    * the name of the symbol in the generated code. We allow duplicates lexical
    * names in the same scope.
    */
  def lexicalName: Str

  /**
    * Currently, this is the number of the test block in which it is defined.
    * TODO: use a generic block number when we need to support source maps.
    */
  var location: Int = 0
}

sealed trait RuntimeSymbol extends LexicalSymbol {
  def runtimeName: Str
}

sealed trait TypeSymbol extends LexicalSymbol {
  val params: Ls[Str]
  val actualType: Type
}

sealed class ValueSymbol(val lexicalName: Str, val runtimeName: Str) extends RuntimeSymbol {
  override def toString: Str = s"value $lexicalName"
}

object ValueSymbol {
  def apply(lexicalName: Str, runtimeName: Str): ValueSymbol =
    new ValueSymbol(lexicalName, runtimeName)
}

sealed case class TypeAliasSymbol(
    val lexicalName: Str,
    val params: Ls[Str],
    val actualType: Type
) extends TypeSymbol
    with LexicalSymbol {
  override def toString: Str = s"type $lexicalName"
}

final case class BuiltinSymbol(val lexicalName: Str, feature: Str) extends RuntimeSymbol {
  val runtimeName = lexicalName

  override def toString: Str = s"function $lexicalName"

  /**
    * `true` if the built-in value had been accessed before.
    * `Scope` will reuse the `lexicalName` if `accessed` is false.
    */
  var accessed: Bool = false
}

final case class StubValueSymbol(
    override val lexicalName: Str,
    override val runtimeName: Str,
    previous: Opt[StubValueSymbol]
)(implicit val accessible: Bool)
    extends RuntimeSymbol {
  override def toString: Str = s"value $lexicalName"
}

final case class ClassSymbol(
    val lexicalName: Str,
    val runtimeName: Str,
    val params: Ls[Str],
    val actualType: Type,
    val fields: Ls[Str],
    val methods: Ls[MethodDef[Left[Term, Type]]],
    enclosingScope: Scope
) extends TypeSymbol
    with RuntimeSymbol {
  private val scope = enclosingScope.derive(s"class $lexicalName")

  def declareMember(name: Str): ValueSymbol = scope.declareValue(name)

  def declareStubMember(name: Str)(implicit accessible: Bool): StubValueSymbol =
    scope.declareStubValue(name)

  def declareStubMember(name: Str, previous: StubValueSymbol)(implicit
      accessible: Bool
  ): StubValueSymbol =
    scope.declareStubValue(name, previous)

  /**
    * Fill up this field after the class translation.
    */
  var body: Opt[JSClassDecl] = N

  /**
    * Fill up this field after resolving classes.
    */
  var baseClass: Opt[ClassSymbol] = N

  override def toString: Str = s"class $lexicalName ($runtimeName)"
}

final case class TraitSymbol(
    val lexicalName: Str,
    val runtimeName: Str,
    val params: Ls[Str],
    val actualType: Type
) extends TypeSymbol
    with RuntimeSymbol {
  override def toString: Str = s"trait $lexicalName"
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
    // "this",
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
