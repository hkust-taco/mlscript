package hkmc2
package syntax

import scala.annotation.tailrec
import scala.collection.mutable
import sourcecode.Line

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import hkmc2.Message.MessageContext
import semantics.{FldFlags, TermDefFlags, Modulefulness}
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
      case UnitLit(isNull) => if isNull then "null" else "undefined"
      case _: BoolLit => "boolean"
    + " literal"
  
  // def children: List[Located] = Nil

enum SpreadKind:
  case Eager, Lazy
  def str: Str = this match
    case Eager => "..."
    case Lazy => ".."
object SpreadKind:
  def fromKw(kw: Keywrd[Keyword.Ellipsis]) = kw.kw match
    case Keyword.`..` => SpreadKind.Lazy
    case Keyword.`...` => SpreadKind.Eager

enum Tree extends AutoLocated:
  case Empty()
  case Error()
  case Dummy // TODO change the places where this is used
  case Under()
  case Unt()
  case Ident(name: Str)
  case Pun(eql: Bool, id: Ident) // `=ident` (eql) or `:ident` (!eql)
  case Keywrd[+K <: Keyword & Singleton](kw: K)
  case IntLit(value: BigInt)             extends Tree with Literal
  case DecLit(value: BigDecimal)         extends Tree with Literal
  case StrLit(value: Str)                extends Tree with Literal
  case UnitLit(isNullNotUndefined: Bool) extends Tree with Literal
  case BoolLit(value: Bool)              extends Tree with Literal
  case Bra(k: BracketKind, inner: Tree)
  case Block(stmts: Ls[Tree])(using State) extends Tree with semantics.BlockImpl
  case LetLike(kw: Keywrd[Keyword.LetLike], lhs: Tree, rhs: Opt[Tree], body: Opt[Tree])
  case Hndl(lhs: Tree, cls: Tree, defs: Tree, body: Opt[Tree])
  case Def(lhs: Tree, rhs: Tree)
  case TermDef(k: TermDefKind, head: Tree, rhs: Opt[Tree]) extends Tree with TermDefImpl
  case TypeDef(k: TypeDefKind, head: Tree, rhs: Opt[Tree])(using State)
    extends Tree with TypeDefImpl
  case Open(opened: Tree)
  case OpenIn(opened: Tree, body: Tree)
  case DynAccess(obj: Tree, fld: Tree)
  case Modified(modifier: Keywrd[Keyword.Modifier], body: Tree)
  case Quoted(body: Tree)
  case Unquoted(body: Tree)
  case Tup(fields: Ls[Tree])
  case TyTup(tys: Ls[Tree])
  case App(lhs: Tree, rhs: Tree)
  case OpApp(lhs: Tree, op: Tree, rhss: Ls[Tree])
  case Jux(lhs: Tree, rhs: Tree)
  case SynthSel(prefix: Tree, name: Ident)
  case Sel(prefix: Tree, name: Ident)
  case MemberProj(cls: Tree, name: Ident)
  case PrefixApp(kw: Keywrd[Keyword.Prefix], rhs: Tree)
  case InfixApp(lhs: Tree, kw: Keywrd[Keyword.Infix], rhs: Tree)
  case LexicalNew(body: Opt[Tree], rft: Opt[Block]) // * New as it is parsed, with its weird precedence – eg (new C)(123)
  case ProperNew(body: Opt[Tree], rft: Opt[Block]) // * A desugared version of New that sets it right – eg new(C(123))
  case DynamicNew(cls: Tree) // * Dynamic version – eg new! C(123)
  case IfLike(kw: Keywrd[Keyword.IfLike], split: Tree)
  case SplitPoint()
  case OpSplit(lhs: Tree, ops_rhss: Ls[Tree]) // * the rhss trees are expressions rooted in `SplitPoint`s
  case Case(kw: Keywrd[Keyword.`case`.type], branches: Tree)
  case Region(name: Tree, body: Tree)
  case RegRef(reg: Tree, value: Tree)
  case Effectful(eff: Tree, body: Tree)
  case Outer(name: Opt[Tree])
  case Spread(kw: Keywrd[Keyword.Ellipsis], body: Opt[Tree])
  case Annotated(annotation: Tree, target: Tree)
  case Constructor(decl: Tree)
  /** Represents a term that has already been elaborated. When desugaring
   *  operator splits in the UCS, the `lhs` of `OpSplit` has already been elaborated
   *  into a `Term`, so we need to embed `Term` into `Tree` using `Trm`. */
  case Trm(term: semantics.Term)
  
  def splitOn(acc: Tree): Tree = this match
    case SplitPoint() => acc
    case Sel(pre, id) => Sel(pre.splitOn(acc), id)
    case App(lhs, rhs) => App(lhs.splitOn(acc), rhs)
    case OpApp(lhs, op, rhss) => OpApp(lhs.splitOn(acc), op, rhss)
    case OpSplit(lhs, rhss) => OpSplit(lhs.splitOn(acc), rhss)
    case InfixApp(lhs, kw, rhs) => InfixApp(lhs.splitOn(acc), kw, rhs)
    case _: (Ident | Literal | Error) => acc
    case _ => die
  
  def children: Ls[Located] = this match
    case _: Empty | _: Error | _: Ident | _: Literal | _: Under | _: Unt => Nil
    case Pun(_, e) => e :: Nil
    case Bra(_, e) => e :: Nil
    case Block(stmts) => stmts
    case LetLike(kw, lhs, rhs, body) => lhs :: Nil ++ rhs ++ body
    case Hndl(lhs, rhs, defs, body) => body match
      case Some(value) => lhs :: rhs :: defs :: value :: Nil
      case None => lhs :: rhs :: defs :: Nil
    case TypeDef(k, head, rhs) => head :: rhs.toList
    case Modified(_, body) => Ls(body)
    case Quoted(body) => Ls(body)
    case Unquoted(body) => Ls(body)
    case Tup(fields) => fields
    case App(lhs, rhs) => Ls(lhs, rhs)
    case OpApp(lhs, op, rhss) => lhs :: op :: rhss
    case Jux(lhs, rhs) => Ls(lhs, rhs)
    case PrefixApp(kw, rhs) => kw :: rhs :: Nil
    case InfixApp(lhs, kw, rhs) => lhs :: kw :: rhs :: Nil
    case TermDef(k, head, rhs) => head :: rhs.toList
    case LexicalNew(body, rft) => body.toList ::: rft.toList
    case ProperNew(body, rft) => body.toList ::: rft.toList
    case DynamicNew(body) => body :: Nil
    case IfLike(_, split) => split :: Nil
    case Case(_, bs) => Ls(bs)
    case Region(name, body) => name :: body :: Nil
    case RegRef(reg, value) => reg :: value :: Nil
    case Effectful(eff, body) => eff :: body :: Nil
    case Outer(name) => name.toList
    case TyTup(tys) => tys
    case Sel(prefix, name) => prefix :: Nil
    case SynthSel(prefix, name) => prefix :: Nil
    case DynAccess(prefix, fld) => prefix :: fld :: Nil
    case Open(bod) => bod :: Nil
    case OpenIn(opened, body) => opened :: body :: Nil
    case Def(lhs, rhs) => lhs :: rhs :: Nil
    case Spread(kw, body) => kw :: body.toList
    case Annotated(annotation, target) => annotation :: target :: Nil
    case Constructor(decl) => decl :: Nil
    case MemberProj(cls, name) => cls :: Nil
    case Keywrd(kw) => Nil
    case Dummy => Nil
    case OpSplit(lhs, ops_rhss) => lhs :: ops_rhss
    case SplitPoint() => Nil
    case Trm(trm) => trm :: Nil
  
  def describe: Str = this match
    case Empty() => "empty"
    case Error() => "‹erroneous syntax›"
    case Under() => "underscore"
    case Ident(name) => "identifier"
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case BoolLit(value) => s"$value literal"
    case UnitLit(value) => if value then "null" else "undefined"
    case Unt() => "unit"
    case Bra(k, _) => k.name + " section"
    case Block(stmts) => "block"
    case LetLike(kw, lhs, rhs, body) => kw.name
    case TermDef(k, alphaName, rhs) => "term definition"
    case TypeDef(k, head, rhs) => "type definition"
    case Modified(kw, body) => s"'${kw.name}'-modified ${body.describe}"
    case Quoted(body) => "quoted"
    case Unquoted(body) => "unquoted"
    case Tup(fields) => "tuple"
    case TyTup(tys) => "type tuple"
    case App(lhs, rhs) => "application"
    case OpApp(lhs, op, rhss) => "operator application"
    case Jux(lhs, rhs) => "juxtaposition"
    case Sel(prefix, name) => "selection"
    case SynthSel(prefix, name) => "synthetic selection"
    case DynAccess(prefix, name) => "dynamic field access"
    case PrefixApp(kw, body) => s"prefix operator '${kw.name}'"
    case InfixApp(lhs, kw, rhs) => s"infix operator '${kw.name}'"
    case LexicalNew(body, _) => "new"
    case ProperNew(body, _) => "new"
    case DynamicNew(body) => "dynamic new"
    case IfLike(Keywrd(Keyword.`if`), split) => "if expression"
    case IfLike(Keywrd(Keyword.`while`), split) => "while expression"
    case Case(_, branches) => "case"
    case Region(name, body) => "region"
    case RegRef(reg, value) => "region reference"
    case Effectful(eff, body) => "effectful"
    case Outer(_) => "outer binding"
    case Hndl(_, _, _, _) => "handle"
    case Def(lhs, rhs) => "defining assignment"
    case Spread(_, _) => "spread"
    case Annotated(_, _) => "annotated"
    case Open(_) => "open"
    case Constructor(_) => "constructor"
    case MemberProj(_, _) => "member projection"
    case Keywrd(kw) => s"'${kw.name}' keyword"
    case Dummy => "‹dummy›"
    case Trm(t) => t.describe + " term"
    case Pun(eql, id) => "pun"
    case SplitPoint() => "split point"
    case OpSplit(lhs, ops_rhss) => "operator split"
    case OpenIn(opened, body) => "open-in"
    
  def deparenthesized: Tree = this match
    case Bra(BracketKind.Round, inner) => inner.deparenthesized
    case _ => this
  
  def showDbg: Str = toString // TODO
  
  lazy val desugared: Tree = this match
    
    case Pun(false, id) =>
      InfixApp(id, Keywrd(Keyword.`:`), id)
    
    // TODO generalize to pattern-let and rm this special case
    case LetLike(kw, und @ Under(), r, b) =>
      LetLike(kw, Ident("_").withLocOf(und), r, b)
    
    case PossiblyAnnotated(anns, m: Modified) =>
      PossiblyAnnotated(anns,
        m match
        case Modified(kw @ Keywrd(Keyword.`declare`), s) =>
          Annotated(kw, s.desugared)
        case Modified(kw @ Keywrd(Keyword.`data`), s) =>
          Annotated(kw, s.desugared)
        case Modified(kw @ Keywrd(Keyword.`abstract`), s) =>
          Annotated(kw, s.desugared)
        case Modified(kw @ Keywrd(Keyword.`staged`), s) =>
          Annotated(kw, s.desugared)
        case Modified(kw @ Keywrd(Keyword.`mut`), TermDef(ImmutVal, anme, rhs)) =>
          TermDef(MutVal, anme, rhs).withLocOf(this).desugared
        case _ => m
      )
    
    case PossiblyAnnotated(anns, LetLike(letLike, OpApp(lhs, f @ Ident(nme), rhss), N, bodo))
    if nme.endsWith("=") =>
      // TODO only do this if the lhs is non-expansive/a valid assignment receiver?
      PossiblyAnnotated(anns, LetLike(letLike, lhs, S(OpApp(lhs, Ident(nme.init), rhss)), bodo).withLocOf(this).desugared)
    
    case Apps(PrefixApp(Keywrd(Keyword.`new!`), cls), argss) =>
      DynamicNew(Apps(cls, argss)).withLocOf(this)
    case Apps(LexicalNew(S(body), N), argss) =>
      ProperNew(S(Apps(body, argss)), N).withLocOf(this)
    case LexicalNew(bodo, rfto) =>
      ProperNew(bodo, rfto).withLocOf(this)
    case InfixApp(Desugared(ProperNew(bodo, N)), Keywrd(Keyword.`with`), rhs: Block) =>
      ProperNew(bodo, S(rhs)).withLocOf(this)
    
    case _ => this
  
  /**
   * Parse a tree as a parameter.
   * @param inUsing whether the parameter is in a `using` parameter list
   */
  def asParam(inUsing: Bool): Diagnostic \/ ParamTree =
    @tailrec
    def go(t: Tree, flags: FldFlags, modifiers: Set[DeclKind]): Diagnostic \/ ParamTree = t match
      // * Base Cases.
      // fun f(_)
      case und: Under => 
        R(ParamTree(flags, new Ident("_").withLocOf(und), N, N, modifiers))
      // fun f(a)
      case id: Ident if !inUsing =>
        R(ParamTree(flags, id, N, N, modifiers))
      // fun f(a: A)
      case InfixApp(id: Ident, Keywrd(Keyword.`:`), sign) =>
        R(ParamTree(flags, id, S(sign), N, modifiers))
      // fun f(..a) | fun f(...a)
      case SpreadParam(id, spd) =>
        R(ParamTree(flags, id, N, S(spd), modifiers))
      
      // * Unwrapping Cases
      // fun f(module <...>)
      case TypeDef(Mod, inner, N) =>
        go(inner, flags, modifiers + Mod)
      // fun f(pattern <...>)
      case TypeDef(Pat, inner, N) =>
        go(inner, flags.copy(pat = true), modifiers + Pat)
      // class C(val <...>)
      case TermDef(ImmutVal, inner, _) =>
        go(inner, flags.copy(isVal = true), modifiers + ImmutVal)
      // class C(mut val <...>)
      case TermDef(MutVal, inner, _) =>
        go(inner, flags.copy(isVal = true, mut = true), modifiers + MutVal)
      // fun f(using <...>)
      case TermDef(Ins, inner, N) =>
        go(inner, flags, modifiers + Ins)
      
      // * Base Case (for `using` clause)
      // fun f(using A)
      case ty: Tree if inUsing =>
        // In contextual parameter lists, a single Tree as parameter is
        // understood as a type for unnamed contextual parameters, as
        // opposed to that an identifier is understood as the identifier
        // for a regular parameter list.
        R(ParamTree(flags, Ident(""), S(ty), N, modifiers))
      
      // * Default Case
      case _ => L:
        ErrorReport:
          msg"Expected a valid parameter, found ${this.describe}" -> this.toLoc :: Nil
    
    go(this, flags = FldFlags.empty, modifiers = Set.empty)

  def isModified(modifier: Keyword | DeclKind): Bool = this match
    case td @ Tree.TypeDef(m, head, N) =>
      (td.extension.isEmpty && td.withPart.isEmpty && m == modifier) || head.isModified(modifier)
    case td @ Tree.TermDef(m, head, N) =>
      (td.extension.isEmpty && td.withPart.isEmpty && m == modifier) || head.isModified(modifier)
    case Modified(Keywrd(m), body) =>
      (modifier is m) || body.isModified(modifier)
    case _ =>
      false

object Tree:
  val DummyApp: App = App(Dummy, Dummy) // TODO change the places where this is used
  val DummyTup: Tup = Tup(Dummy :: Nil)
  def DummyTypeDef(k: TypeDefKind)(using State): TypeDef =
    Tree.TypeDef(k, Tree.Dummy, N)
  object Block:
    def mk(stmts: Ls[Tree])(using State): Tree = stmts match
      case Nil => UnitLit(false)
      case e :: Nil => e
      case es => Block(es)
  object TyApp:
    def apply(lhs: Tree, targs: Ls[Tree]): App =
      App(lhs, TyTup(targs))
    def unapply(t: App): Opt[(Tree, Ls[Tree])] = t match
      case App(lhs, TyTup(targs)) => S(lhs, targs)
      case _ => N
  
  extension [T <: Keyword & Singleton](kw: Tree.Keywrd[T])
    def name = kw.kw.name

/**
 * A parameter yet to be elaborated, which is different from
 * semantics.Param. It merely contains the information directly
 * extracted from the syntax tree.
 */
case class ParamTree(
  flags: FldFlags, ident: Ident, sign: Opt[Tree], 
  spd: Opt[SpreadKind], modifiers: Set[DeclKind]
)

object SpreadParam:
  def unapply(t: Tree): Opt[(Ident, SpreadKind)] = t match
    // fun f(..a)
    // fun f(...a)
    case Spread(kw, S(id: Ident)) =>
      S(id, SpreadKind.fromKw(kw))
    // fun f(.._)
    // fun f(..._)
    case Spread(kw, S(und: Under)) =>
      S(new Ident("_").withLocOf(und), SpreadKind.fromKw(kw))
    // fun f(..)
    // fun f(...)
    case Spread(kw, N) =>
      S(new Ident("_").withLocOf(kw), SpreadKind.fromKw(kw))
    case _ => N

object Desugared:
  def unapply(t: Tree): S[Tree] = S(t.desugared)

object PlainTup:
  def apply(fields: Tree*): Tree = Tup(fields.toList)

object Apps:
  def apply(t: Tree, as: Ls[Tup]): Tree = as match
    case Nil => t
    case arg :: args => Apps(App(t, arg), args)
  def unapply(t: Tree): S[(Tree, Ls[Tup])] = t match
    case App(Apps(base, args), arg: Tup) => S(base, args :+ arg)
    case t => S(t, Nil)
    
object PossiblyAnnotated:
  def apply(anns: Ls[Tree], t: Tree): Tree = anns.foldRight(t)(Annotated(_, _))
  def unapply(t: Tree): Opt[(Ls[Tree], Tree)] = t match
    case Annotated(q, PossiblyAnnotated(qs, target)) => S(q :: qs, target)
    case other => S((Nil, other))

object PossiblyParenthesized:
  def unapply(t: Tree): S[Tree] = t match
    case Bra(BracketKind.Round, inner) => S(inner)
    case _ => S(t)


sealed abstract class OuterKind(val desc: Str)(using line: Line) extends Ordered[OuterKind]:
  val ordinal: Int = line.value // YOLO
  assert(!OuterKind.kinds.contains(ordinal))
  OuterKind.kinds += (ordinal -> this)
  def compare(that: OuterKind): Int = this.ordinal - that.ordinal
object OuterKind:
  private var counter = 0
  private val kinds = mutable.Map.empty[Int, OuterKind]

// Please don't put any of these on the same line...
case object BlockKind extends OuterKind("block")
sealed abstract class DeclKind(desc: Str)(using Line) extends OuterKind(desc)
sealed abstract class TermDefKind(val str: Str, desc: Str)(using Line) extends DeclKind(desc)
sealed abstract class ValLike(str: Str, desc: Str)(using Line) extends TermDefKind(str, desc)
sealed abstract class Val(str: Str, desc: Str)(using Line) extends ValLike(str, desc)
case object ImmutVal extends Val("val", "value")
case object MutVal extends Val("mut val", "mutable value")
case object LetBind extends ValLike("let", "let binding")
case object HandlerBind extends TermDefKind("handler", "handler binding")
case object ParamBind extends ValLike("", "parameter")
case object Fun extends TermDefKind("fun", "function")
case object Ins extends TermDefKind("using", "implicit instance")
sealed abstract class TypeDefKind(desc: Str)(using Line) extends DeclKind(desc)
sealed trait ObjDefKind
sealed trait ClsLikeKind extends ObjDefKind:
  val desc: Str
case object Cls extends TypeDefKind("class") with ClsLikeKind
case object Trt extends TypeDefKind("trait") with ObjDefKind
case object Mxn extends TypeDefKind("mixin")
case object Als extends TypeDefKind("type alias")
case object Pat extends TypeDefKind("pattern") with ClsLikeKind
case object Obj extends TypeDefKind("object") with ClsLikeKind
case object Mod extends TypeDefKind("module") with ClsLikeKind



trait TermDefImpl extends TypeOrTermDef:
  this: TermDef =>
  
  def isParameterizedMethod: Bool =
    (k is Fun) && paramLists.length > 0
  

trait TypeOrTermDef extends Located:
  this: TypeDef | TermDef =>
  
  def describe: Str
  
  def k: DeclKind
  def head: Tree
  
  type MaybeIdent = Diagnostic \/ Ident
  
  lazy val (symbName, name, paramLists, typeParams, annotatedResultType)
      : (Opt[MaybeIdent], MaybeIdent, Ls[Tup], Opt[TyTup], Opt[Tree]) =
    val k = this match
      case td: TypeDef => td.k
      case td: TermDef => td.k
    def rec(t: Tree, symbName: Opt[MaybeIdent], annot: Opt[Tree]): 
      (Opt[MaybeIdent], MaybeIdent, Ls[Tup], Opt[TyTup], Opt[Tree]) = 
      t match
      
      // use Foo as foo = ...
      case InfixApp(typ, Keywrd(Keyword.`as`), id: Ident) if k == Ins =>
        (S(R(id)), R(id), Nil, N, S(typ))
      
      // use Foo = ...
      case typ if k == Ins =>
        val name = typ.showDbg
        val id: Ident = Ident(s"instance$$$name")
        (S(R(id)), R(id), Nil, N, S(typ))
      
      
      case InfixApp(tree, Keywrd(Keyword.`:`), ann) =>
        rec(tree, symbName, S(ann))
      
      // fun f
      // fun f(n1: Int)
      // fun f(n1: Int)(nn: Int)
      case Apps(PossiblyParenthesized(id: Ident), paramLists) =>
        (symbName, R(id), paramLists, N, annot)
      
      // fun f[T]
      // fun f[T](n1: Int)
      // fun f[T](n1: Int)(nn: Int)
      case Apps(App(PossiblyParenthesized(id: Ident), typeParams: TyTup), paramLists) =>
        (symbName, R(id), paramLists, S(typeParams), annot)
      
      case Jux(id: Ident, rhs) =>
        val err = L:
          ErrorReport:
            msg"Invalid ${k.desc} definition head: unexpected ${rhs.describe} in this position" -> rhs.toLoc :: Nil
        (S(err), R(id), Nil, N, annot)
      
      case Jux(lhs, rhs) => // happens in `fun (op) nme` form
        val sn = lhs match
          case Bra(BracketKind.Round, id: Ident) =>
            require(symbName.isEmpty) // TODO
            R(id)
          case Bra(BracketKind.Round, lhs) =>
            L:
              ErrorReport:
                msg"This ${lhs.describe} is not a valid symbolic name" -> lhs.toLoc :: Nil
          case tree =>
            L:
              ErrorReport:
                msg"Invalid ${k.desc} definition head: unexpected ${lhs.describe} in this position" -> lhs.toLoc :: Nil
        rec(rhs, S(sn), annot)
        
      case _ =>
        (N, L(ErrorReport(
          msg"Expected a valid ${k.desc} definition head; found ${t.describe} instead" -> t.toLoc :: Nil)),
          Nil, N, annot)
      
    rec(baseHead, N, N)
  
  val (baseHead, extension, withPart) =
    head match
    case InfixApp(InfixApp(base, Keywrd(Keyword.`extends`), ext), Keywrd(Keyword.`with`), wp) =>
      (base, S(ext), S(wp))
    case InfixApp(base, Keywrd(Keyword.`with`), wp) =>
      (base, N, S(wp))
    case InfixApp(base, Keywrd(Keyword.`extends`), ext) =>
      (base, S(ext), N)
    case h => 
      (h, N, N)
  
end TypeOrTermDef


trait TypeDefImpl(using State) extends TypeOrTermDef:
  this: TypeDef =>
  
  import semantics.*
  
  lazy val symbol: DefinitionSymbol[? <: TypeLikeDef] = k match
    case Cls => ClassSymbol(this, name.getOrElse(Ident("‹error›")))
    case Mod | Obj => ModuleOrObjectSymbol(this, name.getOrElse(Ident("‹error›")))
    case Als => TypeAliasSymbol(name.getOrElse(Ident("‹error›")))
    case Pat => PatternSymbol(
      name.getOrElse(Ident("‹error›")),
      paramLists.headOption,
      rhs.getOrElse(Empty()))
    case Trt | Mxn => ???
  
  lazy val definedSymbols: Map[Str, BlockMemberSymbol] =
    // val fromParams = 
    // val fromTypeParams = 
    withPart match
    case S(blk: Block) =>
      blk.definedSymbols.toMap
    case _ =>
      Map.empty
  
  lazy val clsParams: Ls[TermSymbol] =
    this.paramLists.headOption.fold(Nil): tup =>
      val pts = tup.fields
      val inUsing = pts.headOption.exists(_.isModified(Ins))
      pts.flatMap(_.asParam(inUsing = inUsing).toOption).map:
        case ParamTree(spd = S(_)) => lastWords("spreads are not allowed in class parameters")
        case ParamTree(ident = id) => TermSymbol(ParamBind, symbol.asClsLike, id)
      .toList
    
  lazy val allSymbols = definedSymbols ++ clsParams.map(s => s.nme -> s).toMap

