package hkmc2
package syntax

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import hkmc2.Message.MessageContext
import semantics.Elaborator.State
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
    case UnitLit(value) => if value then "null" else "undefined"
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
  case Under()
  case Ident(name: Str)
  case IntLit(value: BigInt)          extends Tree with Literal
  case DecLit(value: BigDecimal)      extends Tree with Literal
  case StrLit(value: Str)             extends Tree with Literal
  case UnitLit(undefinedOrNull: Bool) extends Tree with Literal
  case BoolLit(value: Bool)           extends Tree with Literal
  case Block(stmts: Ls[Tree])(using State) extends Tree with semantics.BlockImpl
  case OpBlock(items: Ls[Tree -> Tree])
  case LetLike(kw: Keyword.letLike, lhs: Tree, rhs: Opt[Tree], body: Opt[Tree])
  case Handle(lhs: Tree, cls: Tree, defs: Tree, body: Opt[Tree])
  case Def(lhs: Tree, rhs: Tree)
  case TermDef(k: TermDefKind, head: Tree, rhs: Opt[Tree]) extends Tree with TermDefImpl
  case TypeDef(k: TypeDefKind, head: Tree, extension: Opt[Tree], body: Opt[Tree])(using State) extends Tree with TypeDefImpl
  case Open(body: Tree)
  case Modified(modifier: Keyword, modLoc: Opt[Loc], body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Tup(fields: Ls[Tree])
  case TyTup(tys: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case Jux(lhs: Tree, rhs: Tree)
  case SynthSel(prefix: Tree, name: Ident)
  case Sel(prefix: Tree, name: Ident)
  case InfixApp(lhs: Tree, kw: Keyword.Infix, rhs: Tree)
  case New(body: Tree)
  case IfLike(kw: Keyword.`if`.type | Keyword.`while`.type, kwLoc: Opt[Loc], split: Tree)
  @deprecated("Use If instead", "hkmc2-ucs")
  case IfElse(cond: Tree, alt: Tree)
  case Case(kwLoc: Opt[Loc], branches: Tree)
  case Region(name: Tree, body: Tree)
  case RegRef(reg: Tree, value: Tree)
  case Effectful(eff: Tree, body: Tree)
  case Spread(kw: Keyword.Ellipsis, kwLoc: Opt[Loc], body: Opt[Tree])

  def children: Ls[Tree] = this match
    case _: Empty | _: Error | _: Ident | _: Literal | _: Under => Nil
    case Block(stmts) => stmts
    case OpBlock(items) => items.flatMap:
      case (op, body) => op :: body :: Nil
    case LetLike(kw, lhs, rhs, body) => lhs :: Nil ++ rhs ++ body
    case Handle(lhs, rhs, defs, body) => body match
      case Some(value) => lhs :: rhs :: defs :: value :: Nil
      case None => lhs :: rhs :: defs :: Nil
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
    case IfLike(_, _, split) => split :: Nil
    case IfElse(cond, alt) => cond :: alt :: Nil
    case Case(_, bs) => Ls(bs)
    case Region(name, body) => name :: body :: Nil
    case RegRef(reg, value) => reg :: value :: Nil
    case Effectful(eff, body) => eff :: body :: Nil
    case TyTup(tys) => tys
    case SynthSel(prefix, name) => prefix :: Nil
    case Sel(prefix, name) => prefix :: Nil
    case Open(bod) => bod :: Nil
    case Def(lhs, rhs) => lhs :: rhs :: Nil
    case Spread(_, _, body) => body.toList
  
  def describe: Str = this match
    case Empty() => "empty"
    case Error() => "error"
    case Under() => "underscore"
    case Ident(name) => "identifier"
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case UnitLit(value) => if value then "null" else "undefined"
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
    case SynthSel(prefix, name) => "synthetic selection"
    case Sel(prefix, name) => "selection"
    case InfixApp(lhs, kw, rhs) => "infix operation"
    case New(body) => "new"
    case IfLike(Keyword.`if`, _, split) => "if expression"
    case IfLike(Keyword.`while`, _, split) => "while expression"
    case Case(_, branches) => "case"
    case Region(name, body) => "region"
    case RegRef(reg, value) => "region reference"
    case Effectful(eff, body) => "effectful"
    case Handle(_, _, _, _) => "handle"
    case Def(lhs, rhs) => "defining assignment"
    case Spread(_, _, _) => "spread"
  
  def showDbg: Str = toString // TODO
  
  lazy val desugared: Tree = this match
    
    // TODO generalize to pattern-let and rm this special case
    case LetLike(kw, und @ Under(), r, b) =>
      LetLike(kw, Ident("_").withLocOf(und), r, b)
    
    case Modified(Keyword.`declare`, modLoc, s) =>
      // TODO handle `declare` modifier!
      s
    case Modified(Keyword.`abstract`, modLoc, s) =>
      // TODO handle `declare` modifier!
      s
    case Modified(Keyword.`mut`, modLoc, TermDef(ImmutVal, anme, rhs)) =>
      TermDef(MutVal, anme, rhs).desugared
    case LetLike(letLike, App(f @ Ident(nme), Tup((id: Ident) :: r :: Nil)), N, bodo)
    if nme.endsWith("=") =>
      LetLike(letLike, id, S(App(Ident(nme.init), Tup(id :: r :: Nil))), bodo).desugared
    case _ => this

  /** S(true) means eager spread, S(false) means lazy spread, N means no spread. */
  def asParam: Opt[(Opt[Bool], Ident, Opt[Tree])] = this match
    case und: Under => S(N, new Ident("_").withLocOf(und), N)
    case id: Ident => S(N, id, N)
    case Spread(Keyword.`..`, _, S(id: Ident)) => S(S(false), id, N)
    case Spread(Keyword.`...`, _, S(id: Ident)) => S(S(true), id, N)
    case Spread(Keyword.`..`, _, S(und: Under)) => S(S(false), new Ident("_").withLocOf(und), N)
    case Spread(Keyword.`...`, _, S(und: Under)) => S(S(true), new Ident("_").withLocOf(und), N)
    case InfixApp(lhs: Ident, Keyword.`:`, rhs) => S(N, lhs, S(rhs))
    case TermDef(ImmutVal, inner, _) => inner.asParam
  
  def isModuleModifier: Bool = this match
    case Tree.TypeDef(Mod, _, N, N) => true
    case _ => false

object Tree:
  object Block:
    def mk(stmts: Ls[Tree])(using State): Tree = stmts match
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
    case App(Apps(base, args), arg: Tup) => S(base, args :+ arg)
    case t => S(t, Nil)

/** Matches applications with underscores in some argument and/or prefix positions. */
object PartialApp:
  def unapply(t: App): Opt[(Tree \/ Under, Ls[Tree \/ Under])] = t match
    case Apps(base, Tup(args) :: Nil) =>
      var hasUnderscores = false
      def opt(t: Tree) = t match
        case u: Under => hasUnderscores = true; R(u)
        case _ => L(t)
      val res = (base |> opt, args.map(opt))
      Opt.when(hasUnderscores)(res)
    case _ => N


sealed abstract class OuterKind(val desc: Str)
case object BlockKind extends OuterKind("block")
sealed abstract class DeclKind(desc: Str) extends OuterKind(desc)
sealed abstract class TermDefKind(val str: Str, desc: Str) extends DeclKind(desc)
sealed abstract class ValLike(str: Str, desc: Str) extends TermDefKind(str, desc)
sealed abstract class Val(str: Str, desc: Str) extends ValLike(str, desc)
case object ImmutVal extends Val("val", "value")
case object MutVal extends Val("mut val", "mutable value")
case object LetBind extends ValLike("let", "let binding")
case object Handler extends TermDefKind("handler", "handler binding")
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
case object Obj extends TypeDefKind("object") with ClsLikeKind
case object Pat extends TypeDefKind("pattern") with ClsLikeKind



trait TermDefImpl extends TypeOrTermDef:
  this: TermDef =>
  

trait TypeOrTermDef:
  this: TypeDef | TermDef =>
  
  def head: Tree
  
  lazy val (symbName, name, paramLists, typeParams, annotatedResultType)
      : (Opt[Tree], Diagnostic \/ Ident, Ls[Tup], Opt[TyTup], Opt[Tree]) =
    def rec(t: Tree, symbName: Opt[Tree]): 
      (Opt[Tree], Diagnostic \/ Ident, Ls[Tup], Opt[TyTup], Opt[Tree]) = 
      t match
      
      // fun f: Int
      // fun f(n1: Int): Int
      // fun f(n1: Int)(nn: Int): Int
      case InfixApp(Apps(id: Ident, paramLists), Keyword.`:`, sign) =>
        (symbName, R(id), paramLists, N, S(sign))
      
      // fun f[T]: Int
      // fun f[T](n1: Int): Int
      // fun f[T](n1: Int)(nn: Int): Int
      case InfixApp(Apps(App(id: Ident, typeParams: TyTup), paramLists), Keyword.`:`, ret) =>
        (symbName, R(id), paramLists, S(typeParams), S(ret))
      
      case InfixApp(Jux(lhs, rhs), Keyword.`:`, ret) =>
        rec(InfixApp(rhs, Keyword.`:`, ret), S(lhs))
      
      case InfixApp(derived, Keyword.`extends`, base) =>
        // TODO handle `extends`!
        rec(derived, symbName)
      
      // fun f
      // fun f(n1: Int)
      // fun f(n1: Int)(nn: Int)
      case Apps(id: Ident, paramLists) =>
        (symbName, R(id), paramLists, N, N)
      
      // fun f[T]
      // fun f[T](n1: Int)
      // fun f[T](n1: Int)(nn: Int)
      case Apps(App(id: Ident, typeParams: TyTup), paramLists) =>
        (symbName, R(id), paramLists, S(typeParams), N)

      case Jux(lhs, rhs) => // happens in `fun (op) nme` form
        require(symbName.isEmpty) // TOOD
        rec(rhs, S(lhs))
      
      case _ =>
        (N, L(ErrorReport(
          msg"Expected a valid definition head, found ${t.describe} instead" -> t.toLoc :: Nil)),
          Nil, N, N)
      
    rec(head, N)
  
  lazy val symbolicName: Opt[Ident] = symbName match
    case S(id: Ident) => S(id)
    case _ => N

end TypeOrTermDef


trait TypeDefImpl(using semantics.Elaborator.State) extends TypeOrTermDef:
  this: TypeDef =>
  
  lazy val symbol = k match
    case Cls => semantics.ClassSymbol(this, name.getOrElse(Ident("<error>")))
    case Mod | Obj => semantics.ModuleSymbol(this, name.getOrElse(Ident("<error>")))
    case Als => semantics.TypeAliasSymbol(name.getOrElse(Ident("<error>")))
    case Pat => semantics.PatternSymbol(name.getOrElse(Ident("<error>")))
    case Trt | Mxn => ???
  
  lazy val definedSymbols: Map[Str, semantics.BlockMemberSymbol] =
    // val fromParams = 
    // val fromTypeParams = 
    body match
    case S(blk: Block) =>
      blk.definedSymbols.toMap
    case _ =>
      Map.empty
  
  lazy val clsParams: Ls[semantics.TermSymbol] =
    this.paramLists.headOption.fold(Nil): tup =>
      tup.fields.iterator.flatMap(_.asParam).map:
        case (S(spd), id, _) => ??? // spreads are not allowed in class parameters
        case (N, id, _) => semantics.TermSymbol(ParamBind, symbol.asClsLike, id)
      .toList

