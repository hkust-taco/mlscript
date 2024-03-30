package hkmc2
package syntax

import scala.util.boundary

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
  case Modified(modifier: Keyword, body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Lam(lhs: Tree, rhs: Tree)
  case Tup(fields: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  
  private var loc: Opt[Loc] = N
  
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
  
  def withLoc(s: Int, e: Int, ori: Origin): this.type =
    withLoc(S(Loc(s, e, ori)))
  def withLoc(loco: Opt[Loc]): this.type =
    require(loc.isEmpty)
    loc = loco
    this
  def withLocOf(that: Located): this.type = withLoc(that.toLoc)
  def toLoc: Opt[Loc] = boundary:
    if loc.isEmpty then
      def subLocs = children.iterator.flatMap(_.toLoc.iterator)
      val spanStart =
        subLocs.map(_.spanStart).minOption.getOrElse(boundary.break(N))
      val spanEnd =
        subLocs.map(_.spanEnd).maxOption.getOrElse(boundary.break(N))
      val origins = subLocs.map(_.origin).toList.distinct
      assert(origins.size === 1, origins)
      val res = S(Loc(spanStart, spanEnd, origins.head))
      val _ = withLoc(res)
      res
    else loc
  private[syntax] def getLoc: Opt[Loc] = ???
  
  def describe: Str = ??? // TODO

object PlainTup:
  def apply(fields: Tree*): Tree = Tup(fields.toList)


