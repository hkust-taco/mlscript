package hkmc2
package syntax

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import hkmc2.Message.MessageContext
import Tree._


sealed trait Literal extends AutoLocated:
  this: Tree =>
  
  def asTree: Tree = this
  
  val idStr: Str = this match
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => value.iterator.map:
        case '\b' => "\\b" case '\t' => "\\t" case '\n' => "\\n" case '\r' => "\\r"
        case '\f' => "\\f" case '"' => "\\\"" case '\\' => "\\\\"
        case c if c.isControl => f"\\u${c.toInt}%04x"
        case c => c.toString
      .mkString("\"", "", "\"")
    case UnitLit(value) => if value then "undefined" else "null"
    case BoolLit(value) => value.toString
  
  def describeLit: Str =
    this.match
      case _: IntLit => "integer"
      case _: DecLit => "decimal"
      case _: StrLit => "string"
      case _: UnitLit => "unit"
      case _: BoolLit => "boolean"
    + " literal"
  
  // def children: List[Located] = Nil


enum Tree extends AutoLocated:
  case Empty()
  case Error()
  case Ident(name: Str)
  case IntLit(value: BigInt)          extends Tree with Literal
  case DecLit(value: BigDecimal)      extends Tree with Literal
  case StrLit(value: Str)             extends Tree with Literal
  case UnitLit(undefinedOrNull: Bool) extends Tree with Literal
  case BoolLit(value: Bool)           extends Tree with Literal
  case Block(stmts: Ls[Tree])
  case OpBlock(items: Ls[Tree -> Tree])
  case Let(lhs: Tree, rhs: Tree, body: Opt[Tree])
  // case TermDef(k: TermDefKind, symName: Opt[Tree], alphaName: Opt[Tree], sign: Opt[Tree], rhs: Opt[Tree])
  case TermDef(k: TermDefKind, symName: Opt[Tree], alphaName: Opt[Tree], rhs: Opt[Tree]) extends Tree with TermDefImpl
  case TypeDef(k: TypeDefKind, symName: Opt[Tree], head: Tree, extension: Opt[Tree], body: Opt[Tree]) extends Tree with TypeDefImpl
  case Modified(modifier: Keyword, body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Tup(fields: Ls[Tree])
  case TyTup(tys: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case Sel(prefix: Tree, name: Ident)
  case InfixApp(lhs: Tree, kw: Keyword.Infix, rhs: Tree)
  case New(body: Tree)
  case If(split: Tree)
  @deprecated("Use If instead", "hkmc2-ucs")
  case IfElse(cond: Tree, alt: Tree)
  @deprecated("Use If instead", "hkmc2-ucs")
  case Case(branches: Tree)
  case Region(name: Tree, body: Tree)
  case RegRef(reg: Tree, value: Tree)
  case Effectful(eff: Tree, body: Tree)

  def children: Ls[Tree] = this match
    case _: Empty | _: Error | _: Ident | _: Literal => Nil
    case Block(stmts) => stmts
    case OpBlock(items) => items.flatMap:
      case (op, body) => op :: body :: Nil
    case Let(lhs, rhs, body) => Ls(lhs, rhs) ++ body
    case TypeDef(k, symName, head, extension, body) =>
      symName.toList ++ Ls(head) ++ extension ++ body
    case Modified(_, body) => Ls(body)
    case Quoted(body) => Ls(body)
    case Unquoted(body) => Ls(body)
    case Tup(fields) => fields
    case App(lhs, rhs) => Ls(lhs, rhs)
    case InfixApp(lhs, _, rhs) => Ls(lhs, rhs)
    case TermDef(k, symName, alphaName, rhs) => symName.toList ++ alphaName ++ rhs
    case New(body) => body :: Nil
    case If(split) => split :: Nil
    case IfElse(cond, alt) => cond :: alt :: Nil
    case Case(bs) => Ls(bs)
    case Region(name, body) => name :: body :: Nil
    case RegRef(reg, value) => reg :: value :: Nil
    case Effectful(eff, body) => eff :: body :: Nil
  
  def describe: Str = this match
    case Empty() => "empty"
    case Error() => "error"
    case Ident(name) => "identifier"
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case UnitLit(value) => if value then "undefined" else "null"
    case BoolLit(value) => s"$value literal"
    case Block(stmts) => "block"
    case OpBlock(_) => "operator block"
    case Let(lhs, rhs, body) => "let"
    case TermDef(k, symName, alphaName, rhs) => "term definition"
    case TypeDef(k, symName, head, extension, body) => "type definition"
    case Modified(modifier, body) => "modified"
    case Quoted(body) => "quoted"
    case Unquoted(body) => "unquoted"
    case Tup(fields) => "tuple"
    case TyTup(tys) => "type tuple"
    case App(lhs, rhs) => "application"
    case Sel(prefix, name) => "selection"
    case InfixApp(lhs, kw, rhs) => "infix application"
    case New(body) => "new"
    case If(split) => "if expression"
    case IfElse(cond, alt) => "if-then-else"
    case Case(branches) => "case"
    case Region(name, body) => "region"
    case RegRef(reg, value) => "region reference"
    case Effectful(eff, body) => "effectful"
  
  def showDbg: Str = toString // TODO

object Tree:
  object Block:
    def mk(stmts: Ls[Tree]): Tree = stmts match
      case Nil => UnitLit(true)
      case e :: Nil => e
      case es => Block(es)
  object TyApp:
    def apply(lhs: Tree, targs: Ls[Tree]): App =
      App(lhs, TyTup(targs))
    def unapply(t: App): Opt[(Tree, Ls[Tree])] = t match
      case App(lhs, TyTup(targs)) => S(lhs, targs)
      case _ => N

object PlainTup:
  def apply(fields: Tree*): Tree = Tup(fields.toList)



sealed abstract class OuterKind(val desc: Str)
case object BlockKind extends OuterKind("block")
sealed abstract class DeclKind(desc: Str) extends OuterKind(desc)
sealed abstract class TermDefKind(val str: Str, desc: Str) extends DeclKind(desc)
case object Val extends TermDefKind("val", "value")
case object Fun extends TermDefKind("fun", "function")
sealed abstract class TypeDefKind(desc: Str) extends DeclKind(desc)
sealed trait ObjDefKind
sealed trait ClsLikeKind extends ObjDefKind
case object Cls extends TypeDefKind("class") with ClsLikeKind
case object Trt extends TypeDefKind("trait") with ObjDefKind
case object Mxn extends TypeDefKind("mixin")
case object Als extends TypeDefKind("type alias")
case object Mod extends TypeDefKind("module") with ClsLikeKind



private def getName(t: Tree): Diagnostic \/ Ident =
  t match
    case id: Ident =>
      R(id)
    case TyApp(base, args) =>
      getName(base)
    case App(base, args) =>
      getName(base)
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      getName(lhs)
    case _ => L(ErrorReport(
      msg"Expected a valid definition head, found ${t.describe} instead" -> t.toLoc :: Nil))

trait TermDefImpl:
  this: TermDef =>
  lazy val (name, params, typeParams, signature): (Diagnostic \/ Ident, Opt[Tree], Opt[Tree], Opt[Tree]) =
    alphaName.orElse(symName) match
    case S(InfixApp(id: Ident, Keyword.`:`, sign)) =>
      (R(id), N, N, S(sign))
    // show(t: Tree): Str
    case S(InfixApp(App(id: Ident, args), Keyword.`:`, ret)) =>
      (R(id), S(args), N, N)
    // show[A](t: Tree[A]): Str
    case S(InfixApp(App(App(id: Ident, typeParams: TyTup), args), Keyword.`:`, ret)) =>
      // val sign = S(InfixApp(typeParams, Keyword.`->`, InfixApp(args, Keyword.`->`, ret)))
      (R(id), S(args), S(typeParams), N)
    case S(id: Ident) =>
      (R(id), N, N, N)
    case S(App(id: Ident, args)) =>
      (R(id), S(args), N, N)
  lazy val symbolicName: Opt[Ident] = symName match
    case S(id: Ident) => S(id)
    case _ => N

trait TypeDefImpl:
  this: TypeDef =>
  lazy val name: Diagnostic \/ Ident = getName(head)

