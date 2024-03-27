package hkmc2
package syntax

import mlscript.utils.*, shorthands.*

import Tree._


sealed trait Lit:
  this: Tree =>
  def asTree: Tree = this
  val idStr: Str = this match
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case UnitLit(value) => if value then "undefined" else "null"


enum Tree:
  case Empty
  case Ident(name: Str)
  case IntLit(value: BigInt)          extends Tree with Lit
  case DecLit(value: BigDecimal)      extends Tree with Lit
  case StrLit(value: Str)             extends Tree with Lit
  case UnitLit(undefinedOrNull: Bool) extends Tree with Lit
  case Block(stmts: Ls[Tree])
  case Let(lhs: Tree, rhs: Tree, body: Opt[Tree])
  case Val(body: Tree)
  case TypeDecl(head: Tree, extension: Opt[Tree], body: Opt[Tree])


