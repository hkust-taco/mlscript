package hkmc2
package syntax

import mlscript.utils.*, shorthands.*

import Tree._


sealed trait Literal extends Located:
  this: Tree =>
  def asTree: Tree = this
  val idStr: Str = this match
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case UnitLit(value) => if value then "undefined" else "null"
  // def children: List[Located] = Nil


enum Tree extends Located:
  case Empty()
  case Error()
  case Ident(name: Str)
  case IntLit(value: BigInt)          extends Tree with Literal
  case DecLit(value: BigDecimal)      extends Tree with Literal
  case StrLit(value: Str)             extends Tree with Literal
  case UnitLit(undefinedOrNull: Bool) extends Tree with Literal
  case Block(stmts: Ls[Tree])
  case Let(lhs: Tree, rhs: Tree, body: Opt[Tree])
  case TermDef(symName: Opt[Tree], alphaName: Opt[Tree], sign: Opt[Tree], rhs: Opt[Tree])
  case TypeDecl(head: Tree, extension: Opt[Tree], body: Opt[Tree])
  case Modified(modifier: Keyword, body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Lam(lhs: Tree, rhs: Tree)
  case Tup(fields: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case InfixApp(lhs: Tree, kw: Keyword.Infix, rhs: Tree)
  
  def children: Ls[Tree] = this match
    case Empty() | Error() | Ident(_) | IntLit(_) | DecLit(_) | StrLit(_) | UnitLit(_) => Nil
    case Block(stmts) => stmts
    case Let(lhs, rhs, body) => Ls(lhs, rhs) ++ body
    case TypeDecl(head, extension, body) => Ls(head) ++ extension ++ body
    case Modified(_, body) => Ls(body)
    case Quoted(body) => Ls(body)
    case Unquoted(body) => Ls(body)
    case Lam(lhs, rhs) => Ls(lhs, rhs)
    case Tup(fields) => fields
    case App(lhs, rhs) => Ls(lhs, rhs)
    case InfixApp(lhs, _, rhs) => Ls(lhs, rhs)
    case TermDef(symName, alphaName, sign, rhs) => symName.toList ++ alphaName ++ sign ++ rhs
  
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


