package mlscript.mono

import scala.collection.mutable.ArrayBuffer
import mlscript.{Type, Union, Inter, Function, Record, Tuple, Recursive, AppliedType,
                 Neg, Rem, Bounds, WithExtension, Constrained, Top, Bot, Literal,
                 TypeName, TypeVar, PolyType, NamedType}

enum Expr:
  case Ref(name: String)
  case Lambda(params: List[Ref], body: Expr)
  case Apply(callee: Expr, arguments: List[Expr])
  case Tuple(fields: List[Expr])
  case Record(fields: List[(Ref, Expr)])
  case Select(receiver: Expr, field: Ref)
  case LetIn(isRec: Boolean, name: Ref, rhs: Expr, body: Expr)
  case Block(items: List[Expr | Item.FuncDecl | Item.FuncDefn])
  case As(value: Expr, toType: Type)
  case Assign(assignee: Expr, value: Expr)
  case With(value: Expr, fields: Expr.Record)
  case Subscript(receiver: Expr, index: Expr)
  case Match(scrutinee: Expr, branches: ArrayBuffer[CaseBranch])
  case Literal(value: BigInt | BigDecimal | Boolean | String | UnitValue)
  case New(apply: Option[(TypeName, List[Expr])], body: Isolation)
  case IfThenElse(condition: Expr, consequent: Expr, alternate: Option[Expr])
  case Isolated(isolation: Isolation)

  def asBoolean(): Boolean = this match
    case Literal(value: BigInt) => value != 0
    case Literal(value: BigDecimal) => value != 0
    case Literal(value: Boolean) => value
    case Literal(value: String) => !value.isEmpty()
    case Literal(_) => false
    case _ => false

  override def toString(): String = this match
    case Ref(name) => name
    case Lambda(params, body) => 
      val head = params.mkString("(", ", ", ")")
      s"(fun $head -> $body)"
    case Apply(Apply(Ref("."), lhs :: Nil), rhs :: Nil) =>
      s"$lhs.$rhs"
    case Apply(Apply(Ref(op), lhs :: Nil), rhs :: Nil)
        if !op.headOption.forall(_.isLetter) =>
      s"($lhs $op $rhs)"
    case Apply(callee, arguments) =>
      callee.toString + arguments.mkString("(", ", ", ")")
    case Tuple(fields) => 
      val inner = fields.mkString(", ")
      "(" + (if fields.length == 1 then inner + ", " else inner) + ")"
    case Record(fields) =>
      "{" + fields.iterator.map { (name, value) => s"$name = $value" } + "}"
    case Select(receiver, field) => s"$receiver.$field"
    case LetIn(isRec, name, rhs, body) => s"let $name = $rhs in $body"
    case Block(items) => items.mkString(";")
    case As(value, toType) => s"$value as $toType"
    case Assign(assignee, value) => s"$assignee = $value"
    case With(value, fields) => s"$value with $fields"
    case Subscript(receiver, index) => s"$receiver[$index]"
    case Match(scrutinee, branches) =>
      s"$scrutinee match " + branches.iterator.mkString("{", "; ", "}")
    case Literal(value) => value.toString
    case New(Some((callee, args)), body) =>
      s"new ${callee.name}" + args.mkString(" (", ", ", ") ") + body.toString
    case New(None, body) => "new " + body.toString
    case IfThenElse(condition, consequent, None) =>
      s"if $condition then $consequent"
    case IfThenElse(condition, consequent, Some(alternate)) =>
      s"if $condition then $consequent else $alternate"
    case Isolated(isolation) => s"{\n$isolation\n}"
end Expr

// This corresponds to `mlscript.UnitLit`.
enum UnitValue:
  case Null, Undefined

  override def toString(): String =
    this match
      case Null => "null"
      case Undefined => "()" // `()` is shorter than `undefined`

class CaseBranch(pattern: Option[Expr.Ref | Expr.Literal], body: Expr):
  // Constructor for the last wildcard branch.
  def this(body: Expr) = this(None, body)

  override def toString(): String =
    "case " + pattern.fold("_")(_.toString) + " => " + body.toString

enum TypeDeclKind:
  case Alias, Class, Trait

  override def toString(): String = this match
    case Alias => "alias"
    case Class => "class"
    case Trait => "trait"

/**
 * Function parameters: `(specializable, name)`.
 */
type Parameter = (Boolean, Expr.Ref)

enum Item:
  /**
   * Type declarations: aliases, classes and traits.
   */
  case TypeDecl(val name: Expr.Ref, kind: TypeDeclKind, typeParams: List[TypeName],
                params: List[Parameter], parents: List[NamedType], body: Isolation)
  /**
   * Function declaration (with implementation).
   */
  case FuncDecl(val name: Expr.Ref, params: List[Parameter], body: Expr)
  /**
   * Function definition (with definition)
   */
  case FuncDefn(val name: Expr.Ref, typeParams: List[TypeName], body: PolyType)

  override def toString(): String = this match
    case TypeDecl(Expr.Ref(name), kind, typeParams, params, parents, body) =>
      val typeParamsStr = if typeParams.isEmpty then ""
        else typeParams.iterator.map(_.name).mkString("[", ", ", "]")
      val parentsStr = if parents.isEmpty then ""
        else parents.mkString(" extends ", " with ", " ")
      s"$kind $name$typeParamsStr$parentsStr { $body }"
    case FuncDecl(Expr.Ref(name), params, body) =>
      val parameters = params.iterator.map {
        case (spec, Expr.Ref(name)) =>
          (if spec then "#" else "") + name
      }.mkString("(", ", ", ")")
      s"fun $name$parameters = $body"
    case FuncDefn(Expr.Ref(name), Nil, polyType) =>
      s"fun $name: $polyType"
    case FuncDefn(Expr.Ref(name), typeParams, polyType) =>
      s"fun $name: ${typeParams.mkString("[", ", ", "]")} => $polyType"

object Item:
  /**
   * A shorthand constructor for classes without type parameters and parents.
   */
  def classDecl(name: String, params: List[Parameter], body: Isolation): Item.TypeDecl =
    Item.TypeDecl(Expr.Ref(name), TypeDeclKind.Class, Nil, params, Nil, body)

/**
 * An `Isolation` is like a `TypingUnit` but without nested classes.
 */
class Isolation(val items: List[Expr | Item.FuncDecl | Item.FuncDefn]):
  override def toString(): String = items.mkString("\n")

object Isolation:
  def empty = Isolation(Nil)

/**
 * A `Module` is like a `TypingUnit`.
 * This name conflicts with `java.lang.Module`.
 * TODO: Find a better name.
 */
class Module(val items: List[Expr | Item]):
  override def toString(): String = items.mkString("\n")
