package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.Type
import mlscript.JSClassDecl
import mlscript.MethodDef
import mlscript.Term
import mlscript.TypeName

sealed trait LexicalSymbol {

  /**
    * The lexical name of the symbol. This is different from the runtime name,
    * the name of the symbol in the generated code. We allow duplicates lexical
    * names in the same scope.
    */
  def lexicalName: Str
}

sealed trait RuntimeSymbol extends LexicalSymbol {
  def runtimeName: Str
}

sealed trait TypeSymbol extends LexicalSymbol {
  val params: Ls[Str]
  val body: Type
}

sealed class ValueSymbol(val lexicalName: Str, val runtimeName: Str, val isByvalueRec: Option[Boolean], val isLam: Boolean) extends RuntimeSymbol {
  override def toString: Str = s"value $lexicalName"
}

object ValueSymbol {
  def apply(lexicalName: Str, runtimeName: Str, isByvalueRec: Option[Boolean], isLam: Boolean): ValueSymbol =
    new ValueSymbol(lexicalName, runtimeName, isByvalueRec, isLam)
}

sealed case class TypeAliasSymbol(
    val lexicalName: Str,
    val params: Ls[Str],
    val body: Type
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
    /**
      * Whether this stub is shadowing another symbol.
      */
    val shadowing: Bool,
    previous: Opt[StubValueSymbol]
)(implicit val accessible: Bool)
    extends RuntimeSymbol {
  override def toString: Str = s"value $lexicalName"
}

final case class ClassSymbol(
    lexicalName: Str,
    runtimeName: Str,
    params: Ls[Str],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
) extends TypeSymbol
    with RuntimeSymbol with Ordered[ClassSymbol] {

  import scala.math.Ordered.orderingToOrdered

  override def compare(that: ClassSymbol): Int = lexicalName.compare(that.lexicalName)

  override def toString: Str = s"class $lexicalName ($runtimeName)"
}

final case class TraitSymbol(
    lexicalName: Str,
    runtimeName: Str,
    params: Ls[Str],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
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
