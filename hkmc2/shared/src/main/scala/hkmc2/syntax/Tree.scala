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
    case StrLit(value) => value.iterator.map: // TODO dedup logi with `JSBuilder.makeStringLiteral`?
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
  case LetLike(kw: Keyword.letLike, lhs: Tree, rhs: Opt[Tree], body: Opt[Tree])
  case Def(lhs: Tree, rhs: Tree)
  case TermDef(k: TermDefKind, head: Tree, rhs: Opt[Tree]) extends Tree with TermDefImpl
  case TypeDef(k: TypeDefKind, head: Tree, extension: Opt[Tree], body: Opt[Tree]) extends Tree with TypeDefImpl
  case Open(body: Tree)
  case Modified(modifier: Keyword, modLoc: Opt[Loc], body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Tup(fields: Ls[Tree])
  case TyTup(tys: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case Jux(lhs: Tree, rhs: Tree)
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
    case LetLike(kw, lhs, rhs, body) => lhs :: Nil ++ rhs ++ body
    case TypeDef(k, head, extension, body) =>
      head :: extension.toList ::: body.toList
    case Modified(_, _, body) => Ls(body)
    case Quoted(body) => Ls(body)
    case Unquoted(body) => Ls(body)
    case Tup(fields) => fields
    case App(lhs, rhs) => Ls(lhs, rhs)
    case Jux(lhs, rhs) => Ls(lhs, rhs)
    case InfixApp(lhs, _, rhs) => Ls(lhs, rhs)
    case TermDef(k, head, rhs) => head :: rhs.toList
    case New(body) => body :: Nil
    case If(split) => split :: Nil
    case IfElse(cond, alt) => cond :: alt :: Nil
    case Case(bs) => Ls(bs)
    case Region(name, body) => name :: body :: Nil
    case RegRef(reg, value) => reg :: value :: Nil
    case Effectful(eff, body) => eff :: body :: Nil
    case TyTup(tys) => tys
    case Sel(prefix, name) => prefix :: Nil
    case Open(bod) => bod :: Nil
  
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
    case LetLike(kw, lhs, rhs, body) => kw.name
    case TermDef(k, alphaName, rhs) => "term definition"
    case TypeDef(k, head, extension, body) => "type definition"
    case Modified(kw, _, body) => s"${kw.name}-modified ${body.describe}"
    case Quoted(body) => "quoted"
    case Unquoted(body) => "unquoted"
    case Tup(fields) => "tuple"
    case TyTup(tys) => "type tuple"
    case App(lhs, rhs) => "application"
    case Jux(lhs, rhs) => "juxtaposition"
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
  
  lazy val desugared: Tree = this match
    case Modified(Keyword.`mut`, modLoc, TermDef(ImmutVal, anme, rhs)) =>
      TermDef(MutVal, anme, rhs).desugared
    case LetLike(letLike, App(f @ Ident(nme), Tup((id: Ident) :: r :: Nil)), N, bodo)
    if nme.endsWith("=") =>
      LetLike(letLike, id, S(App(Ident(nme.init), Tup(id :: r :: Nil))), bodo).desugared
    case _ => this

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

object Apps:
  def unapply(t: Tree): S[(Tree, Ls[Tup])] = t match
    case App(Apps(id, args), arg: Tup) => S(id, args :+ arg)
    case t => S(t, Nil)


sealed abstract class OuterKind(val desc: Str)
case object BlockKind extends OuterKind("block")
sealed abstract class DeclKind(desc: Str) extends OuterKind(desc)
sealed abstract class TermDefKind(val str: Str, desc: Str) extends DeclKind(desc)
sealed abstract class ValLike(str: Str, desc: Str) extends TermDefKind(str, desc)
sealed abstract class Val(str: Str, desc: Str) extends ValLike(str, desc)
case object ImmutVal extends Val("val", "value")
case object MutVal extends Val("mut val", "mutable value")
case object LetBind extends ValLike("let", "let binding")
case object ParamBind extends ValLike("", "parameter")
case object Fun extends TermDefKind("fun", "function")
sealed abstract class TypeDefKind(desc: Str) extends DeclKind(desc)
sealed trait ObjDefKind
sealed trait ClsLikeKind extends ObjDefKind
case object Cls extends TypeDefKind("class") with ClsLikeKind
case object Trt extends TypeDefKind("trait") with ObjDefKind
case object Mxn extends TypeDefKind("mixin")
case object Als extends TypeDefKind("type alias")
case object Mod extends TypeDefKind("module") with ClsLikeKind



private def getName(t: Tree, symNme: Opt[Tree]): (Opt[Tree], Diagnostic \/ Ident) =
  t match
    case id: Ident =>
      symNme -> R(id)
    case TyApp(base, args) =>
      getName(base, symNme)
    case App(base, args) =>
      getName(base, symNme)
    case Jux(symNme2, rest) =>
      require(symNme.isEmpty) // TODO
      getName(rest, S(symNme2))
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      getName(lhs, symNme)
    case InfixApp(lhs, Keyword.`extends`, rhs) =>
      getName(lhs, symNme)
    case _ => symNme -> L(ErrorReport(
      msg"Expected a valid definition head, found ${t.describe} instead" -> t.toLoc :: Nil))

trait TermDefImpl:
  this: TermDef =>
  lazy val (symName, name, paramLists, typeParams, signature): (Opt[Tree], Diagnostic \/ Ident, Ls[Tup], Opt[Tree], Opt[Tree]) =
    def rec(t: Tree, symName: Opt[Tree]): 
      (Opt[Tree], Diagnostic \/ Ident, Ls[Tup], Opt[Tree], Opt[Tree]) = 
      t match
      // fun f: Int
      // fun f(n1: Int): Int
      // fun f(n1: Int)(nn: Int): Int
      case InfixApp(Apps(id: Ident, paramLists), Keyword.`:`, sign) =>
        (symName, R(id), paramLists, N, S(sign))
      // fun f[T]: Int
      // fun f[T](n1: Int): Int
      // fun f[T](n1: Int)(nn: Int): Int
      case InfixApp(Apps(App(id: Ident, typeParams: TyTup), paramLists), Keyword.`:`, ret) =>
        (symName, R(id), paramLists, S(typeParams), N)
      
      case InfixApp(Jux(lhs, rhs), Keyword.`:`, ret) =>
        rec(InfixApp(rhs, Keyword.`:`, ret), S(lhs))
      
      // fun f
      // fun f(n1: Int)
      // fun f(n1: Int)(nn: Int)
      case Apps(id: Ident, paramLists) =>
        (symName, R(id), paramLists, N, N)
      // fun f[T]
      // fun f[T](n1: Int)
      // fun f[T](n1: Int)(nn: Int)
      case Apps(App(id: Ident, typeParams: TyTup), paramLists) =>
        (symName, R(id), paramLists, S(typeParams), N)

      case Jux(lhs, rhs) => // happens in `fun (op) nme` form
        require(symName.isEmpty) // TOOD
        rec(rhs, S(lhs))
    rec(head, N)
  lazy val symbolicName: Opt[Ident] = symName match
    case S(id: Ident) => S(id)
    case _ => N

trait TypeDefImpl:
  this: TypeDef =>
  lazy val (symName, name): (Opt[Tree], Diagnostic \/ Ident) = getName(head, N)

