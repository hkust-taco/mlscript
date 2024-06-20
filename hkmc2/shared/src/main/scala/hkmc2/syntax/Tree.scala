package hkmc2
package syntax

import mlscript.utils.*, shorthands.*

import hkmc2.Message.MessageContext
import Tree._


sealed trait Literal extends Located:
  this: Tree =>
  def asTree: Tree = this
  val idStr: Str = this match
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case UnitLit(value) => if value then "undefined" else "null"
    case BoolLit(value) => value.toString
  // def children: List[Located] = Nil


enum Tree extends Located:
  case Empty()
  case Error()
  case Ident(name: Str)
  case IntLit(value: BigInt)          extends Tree with Literal
  case DecLit(value: BigDecimal)      extends Tree with Literal
  case StrLit(value: Str)             extends Tree with Literal
  case UnitLit(undefinedOrNull: Bool) extends Tree with Literal
  case BoolLit(value: Bool)           extends Tree with Literal
  case Block(stmts: Ls[Tree])
  case Let(lhs: Tree, rhs: Tree, body: Opt[Tree])
  // case TermDef(k: TermDefKind, symName: Opt[Tree], alphaName: Opt[Tree], sign: Opt[Tree], rhs: Opt[Tree])
  case TermDef(k: TermDefKind, symName: Opt[Tree], alphaName: Opt[Tree], rhs: Opt[Tree]) extends Tree with TermDefImpl
  case TypeDef(k: TypeDefKind, head: Tree, extension: Opt[Tree], body: Opt[Tree]) extends Tree with TypeDefImpl
  case Modified(modifier: Keyword, body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Tup(fields: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case TyApp(lhs: Tree, targs: Ls[Tree])
  case Sel(prefix: Tree, name: Ident)
  case InfixApp(lhs: Tree, kw: Keyword.Infix, rhs: Tree)
  case New(body: Tree)
  case Forall(tvs: Ls[Tree], body: Tree) // TODO: bounds

  def children: Ls[Tree] = this match
    case Empty() | Error() | Ident(_) | IntLit(_) | DecLit(_) | StrLit(_) | UnitLit(_) => Nil
    case Block(stmts) => stmts
    case Let(lhs, rhs, body) => Ls(lhs, rhs) ++ body
    case TypeDef(k, head, extension, body) => Ls(head) ++ extension ++ body
    case Modified(_, body) => Ls(body)
    case Quoted(body) => Ls(body)
    case Unquoted(body) => Ls(body)
    case Tup(fields) => fields
    case App(lhs, rhs) => Ls(lhs, rhs)
    case InfixApp(lhs, _, rhs) => Ls(lhs, rhs)
    case TermDef(k, symName, alphaName, rhs) => symName.toList ++ alphaName ++ rhs
    case New(body) => body :: Nil
    case Forall(tvs, body) => body :: tvs
  
  def describe: Str = ??? // TODO
  
  def showDbg: Str = toString // TODO

object PlainTup:
  def apply(fields: Tree*): Tree = Tup(fields.toList)



sealed abstract class OuterKind(val desc: Str)
case object BlockKind extends OuterKind("block")
sealed abstract class DeclKind(desc: Str) extends OuterKind(desc)
sealed abstract class TermDefKind(val str: Str, desc: Str) extends DeclKind(desc)
case object Val extends TermDefKind("val", "value")
case object Fun extends TermDefKind("fun","function")
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
    case _ => L(ErrorReport(
      msg"Expected a valid definition head, found ${t.describe} instead" -> t.toLoc :: Nil))

trait TermDefImpl:
  this: TermDef =>
  lazy val (name, params, signature): (Diagnostic \/ Ident, Opt[Tree], Opt[Tree]) = alphaName.orElse(symName) match
    case S(InfixApp(id: Ident, Keyword.`:`, sign)) =>
      (R(id), N, S(sign))
    case S(id: Ident) =>
      (R(id), N, N)
    case S(App(id: Ident, args)) =>
      (R(id), S(args), N)
  lazy val symbolicName: Opt[Ident] = symName match
    case S(id: Ident) => S(id)
    case _ => N

trait TypeDefImpl:
  this: TypeDef =>
  lazy val name: Diagnostic \/ Ident = getName(head)

