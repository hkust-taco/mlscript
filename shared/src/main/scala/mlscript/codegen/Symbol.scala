package mlscript.codegen

import mlscript.utils.shorthands._
import mlscript.Type
import mlscript.JSClassDecl
import mlscript.MethodDef
import mlscript.{Term, Statement}
import mlscript.TypeName
import mlscript.NuTypeDef

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

sealed trait NuTypeSymbol { sym: TypeSymbol =>
  val isNested: Bool // is nested in another class/mixin/module
  val methods: Ls[MethodDef[Left[Term, Type]]]
  val ctor: Ls[Statement] // statements in the constructor
  val nested: Ls[NuTypeDef] // nested class/mixin/module
  val superParameters: Ls[Term] // parameters that need to be passed to the `super()`
  val isPlainJSClass: Bool // is this a plain class in JS
  val ctorParams: Opt[Ls[Str]] // parameters in the constructor
  val matchingFields: Ls[Str] = sym.body.collectFields
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

final case class NewClassMemberSymbol(
  val lexicalName: Str,
  val isByvalueRec: Option[Boolean],
  val isLam: Boolean,
  val isPrivate: Boolean
) extends RuntimeSymbol {
  override def toString: Str = s"new class member $lexicalName"

  // Class members should have fixed names determined by users
  override def runtimeName: Str = lexicalName
}

final case class NewClassSymbol(
    lexicalName: Str,
    params: Ls[Str],
    ctorParams: Opt[Ls[Str]],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
    ctor: Ls[Statement],
    superParameters: Ls[Term],
    nested: Ls[NuTypeDef],
    isNested: Bool,
    isPlainJSClass: Bool
) extends TypeSymbol
    with RuntimeSymbol with NuTypeSymbol {
  override def toString: Str = s"new class $lexicalName"

  // Classes should have fixed names determined by users
  override def runtimeName: Str = lexicalName
}

final case class MixinSymbol(
    lexicalName: Str,
    params: Ls[Str],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
    ctor: Ls[Statement],
    nested: Ls[NuTypeDef],
    isNested: Bool
) extends TypeSymbol
    with RuntimeSymbol with NuTypeSymbol {
  override def toString: Str = s"mixin $lexicalName"

  // Mixins should have fixed names determined by users
  override def runtimeName: Str = lexicalName

  // Mixins should pass `...rest` to the `super()`
  // But the variable name is not sure when we create the symbol object
  override val superParameters: Ls[Term] = Nil
  val isPlainJSClass: Bool = false
  val ctorParams: Opt[Ls[Str]] = N
}

final case class ModuleSymbol(
    lexicalName: Str,
    params: Ls[Str],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
    ctor: Ls[Statement],
    superParameters: Ls[Term],
    nested: Ls[NuTypeDef],
    isNested: Bool
) extends TypeSymbol
    with RuntimeSymbol with NuTypeSymbol {
  override def toString: Str = s"module $lexicalName"

  // Modules should have fixed names determined by users
  override def runtimeName: Str = lexicalName
  val isPlainJSClass: Bool = false
  val ctorParams: Opt[Ls[Str]] = N
}

// capture runtime symbols in the outside module/class/mixin
final case class CapturedSymbol(
  outsiderSym: RuntimeSymbol,
  actualSym: RuntimeSymbol
) extends RuntimeSymbol {
  override def lexicalName: Str = actualSym.lexicalName
  override def runtimeName: Str = actualSym.runtimeName
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
