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

trait LexicalSymbol extends RuntimeSymbol {
  def lexicalName: Str

  /**
    * A short name for the declaration used in debugging and error messages.
    */
  def shortName: Str
}


final case class TemporarySymbol(val runtimeName: Str) extends RuntimeSymbol {

}

final case class BuiltinSymbol(val lexicalName: Str, feature: Str) extends LexicalSymbol {
  val runtimeName: Str = lexicalName
  def shortName: Str = s"function $lexicalName"
}

final case class ValueSymbol(val lexicalName: Str, val runtimeName: Str) extends LexicalSymbol {
  def shortName: Str = s"value $lexicalName"
}

final case class StubValueSymbol(val lexicalName: Str, val runtimeName: Str) extends LexicalSymbol {
  def shortName: Str = s"value $lexicalName"
}

final case class ClassSymbol(
    val lexicalName: Str,
    val runtimeName: Str,
    params: Ls[Str],
    base: Type,
    enclosingScope: Scope
) extends LexicalSymbol {
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
  
  def shortName: Str = s"class $lexicalName"
}

final case class TraitSymbol(val lexicalName: Str, val runtimeName: Str, params: Ls[Str], base: Type) extends LexicalSymbol {
  def shortName: Str = s"trait $lexicalName"
}

final case class TypeSymbol(val lexicalName: Str, val runtimeName: Str, params: Ls[Str], body: Type) extends LexicalSymbol {
  def shortName: Str = s"type $lexicalName"
}

final case class ParamSymbol(val lexicalName: Str, val runtimeName: Str) extends LexicalSymbol {
  def shortName: Str = s"parameter $lexicalName"
}

final case class FreeSymbol(val lexicalName: Str) extends LexicalSymbol {
  override def runtimeName: Str = throw new CodeGenError("free symbol has no runtime name")
  def shortName: Str = s"free $lexicalName"
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
