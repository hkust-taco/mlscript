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
  case Empty
  case Ident(name: Str)
  case IntLit(value: BigInt)          extends Tree with Literal
  case DecLit(value: BigDecimal)      extends Tree with Literal
  case StrLit(value: Str)             extends Tree with Literal
  case UnitLit(undefinedOrNull: Bool) extends Tree with Literal
  case Block(stmts: Ls[Tree])
  case Let(lhs: Tree, rhs: Tree, body: Opt[Tree])
  case Val(body: Tree)
  case TypeDecl(head: Tree, extension: Opt[Tree], body: Opt[Tree])
  case Modified(modifier: Keyword, body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Lam(lhs: Tree, rhs: Tree)
  case Tup(fields: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case InfixApp(lhs: Tree, kw: Keyword.Infix, rhs: Tree)
  
  def children: Ls[Tree] = this match
    case Empty | Ident(_) | IntLit(_) | DecLit(_) | StrLit(_) | UnitLit(_) => Nil
    case Block(stmts) => stmts
    case Let(lhs, rhs, body) => Ls(lhs, rhs) ++ body
    case Val(body) => Ls(body)
    case TypeDecl(head, extension, body) => Ls(head) ++ extension ++ body
    case Modified(_, body) => Ls(body)
    case Quoted(body) => Ls(body)
    case Unquoted(body) => Ls(body)
    case Lam(lhs, rhs) => Ls(lhs, rhs)
    case Tup(fields) => fields
    case App(lhs, rhs) => Ls(lhs, rhs)
    case InfixApp(lhs, _, rhs) => Ls(lhs, rhs)
  
  def describe: Str = ??? // TODO
  
  def showDbg: Str = toString // TODO

object PlainTup:
  def apply(fields: Tree*): Tree = Tup(fields.toList)


