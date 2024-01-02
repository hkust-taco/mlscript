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
  var visited: Bool = false
}

sealed trait TypeSymbol extends LexicalSymbol {
  val params: Ls[Str]
  val body: Type
}

sealed trait NuTypeSymbol { sym: TypeSymbol =>
  val name: Str
  val methods: Ls[MethodDef[Left[Term, Type]]] // implemented methods
  val signatures: Ls[MethodDef[Right[Term, Type]]] // methods signatures
  val ctor: Ls[Statement] // statements in the constructor
  val nested: Ls[NuTypeDef] // nested class/mixin/module
  val qualifier: Opt[Str] // if it is inside another NuTypeSymbol, it indicates the runtime alias of parent's `this`
  val superParameters: Ls[Term] // parameters that need to be passed to the `super()`
  val isPlainJSClass: Bool // is this a plain class in JS
  val ctorParams: Opt[Ls[(Str, Bool)]] // parameters in the constructor
  val publicCtors: Ls[Str] // public(i.e., val-) parameters in the ctor
  val matchingFields: Ls[Str] = sym.body.collectFields // matchable fields(i.e., fields in `class ClassName(...)`)
  val unapplyMtd: Opt[MethodDef[Left[Term, Type]]] // unapply method

  def isNested: Bool = qualifier.isDefined // is nested in another class/mixin/module
}

sealed class ValueSymbol(
    val lexicalName: Str,
    val runtimeName: Str,
    val isByvalueRec: Option[Boolean],
    val isLam: Boolean,
    /**
      * Workaround for the first pass traversal with new definition typing.
      * "Dry run" here means that we haven't generated the code for the symbol
      * yet in the new-definition-typing mode, so the symbol is just defined
      * for the sake of code generation of classes/mixins/modules.
      * 
      * This field should be deprecated after the `PreTyper` is done. See [PR
      * #197](https://github.com/hkust-taco/mlscript/pull/197) for more details. 
      */
    val forNewDefsDryRun: Boolean
) extends RuntimeSymbol {
  override def toString: Str = s"value $lexicalName"
}

object ValueSymbol {
  def apply(
      lexicalName: Str,
      runtimeName: Str,
      isByvalueRec: Option[Boolean],
      isLam: Boolean,
      /** Workaround for the first pass traversal with new definition typing. */
      forNewDefsDryRun: Boolean = false
  ): ValueSymbol =
    new ValueSymbol(lexicalName, runtimeName, isByvalueRec, isLam, forNewDefsDryRun)
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
  name: Str,
  isByvalueRec: Option[Boolean],
  isLam: Boolean,
  isPrivate: Boolean,
  qualifier: Option[Str]
) extends RuntimeSymbol {
  override def toString: Str = s"new class member $name"

  // Class members should have fixed names determined by users
  override def lexicalName: Str = name
  override def runtimeName: Str = name
}

final case class NewClassSymbol(
    name: Str,
    params: Ls[Str],
    ctorParams: Opt[Ls[(Str, Bool)]],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
    unapplyMtd: Opt[MethodDef[Left[Term, Type]]],
    signatures: Ls[MethodDef[Right[Term, Type]]],
    ctor: Ls[Statement],
    superParameters: Ls[Term],
    publicCtors: Ls[Str],
    nested: Ls[NuTypeDef],
    qualifier: Opt[Str],
    isPlainJSClass: Bool
) extends TypeSymbol
    with RuntimeSymbol with NuTypeSymbol {
  override def toString: Str = s"new class $name"

  // Classes should have fixed names determined by users
  override def lexicalName: Str = name
  override def runtimeName: Str = name
}

final case class MixinSymbol(
    name: Str,
    params: Ls[Str],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
    signatures: Ls[MethodDef[Right[Term, Type]]],
    ctor: Ls[Statement],
    publicCtors: Ls[Str],
    nested: Ls[NuTypeDef],
    qualifier: Opt[Str]
) extends TypeSymbol
    with RuntimeSymbol with NuTypeSymbol {
  override def toString: Str = s"mixin $name"

  // Mixins should have fixed names determined by users
  override def lexicalName: Str = name
  override def runtimeName: Str = name

  // Mixins should pass `...rest` to the `super()`
  // But the variable name is not sure when we create the symbol object
  override val superParameters: Ls[Term] = Nil
  val isPlainJSClass: Bool = true
  val ctorParams: Opt[Ls[(Str, Bool)]] = N
  val unapplyMtd: Opt[MethodDef[Left[Term, Type]]] = N
}

final case class ModuleSymbol(
    name: Str,
    params: Ls[Str],
    body: Type,
    methods: Ls[MethodDef[Left[Term, Type]]],
    signatures: Ls[MethodDef[Right[Term, Type]]],
    ctor: Ls[Statement],
    superParameters: Ls[Term],
    nested: Ls[NuTypeDef],
    qualifier: Opt[Str]
) extends TypeSymbol
    with RuntimeSymbol with NuTypeSymbol {
  override def toString: Str = s"module $name"

  // Modules should have fixed names determined by users
  override def lexicalName: Str = name
  override def runtimeName: Str = name
  val isPlainJSClass: Bool = false
  val ctorParams: Opt[Ls[(Str, Bool)]] = N
  val publicCtors: Ls[Str] = Nil
  val unapplyMtd: Opt[MethodDef[Left[Term, Type]]] = N
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
