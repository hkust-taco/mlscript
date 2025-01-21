package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree}
import semantics.*
import semantics.Term.*
import sem.Elaborator.State


case class Program(
  imports: Ls[Local -> Str],
  main: Block,
)


sealed abstract class Block extends Product with AutoLocated:
  
  protected def children: Ls[Located] = ??? // Maybe extending AutoLocated is unnecessary
  
  lazy val definedVars: Set[Local] = this match
    case _: Return | _: Throw => Set.empty
    case Begin(sub, rst) => sub.definedVars ++ rst.definedVars
    case Assign(l: TermSymbol, r, rst) => rst.definedVars
    case Assign(l, r, rst) => rst.definedVars + l
    case AssignField(l, n, r, rst) => rst.definedVars
    case Match(scrut, arms, dflt, rst) =>
      arms.flatMap(_._2.definedVars).toSet ++ dflt.toList.flatMap(_.definedVars) ++ rst.definedVars
    case End(_) => Set.empty
    case Break(_) => Set.empty
    case Continue(_) => Set.empty
    case Define(defn, rst) => rst.definedVars
    case HandleBlock(lhs, res, par, cls, hdr, bod, rst) => bod.definedVars ++ rst.definedVars + lhs
    case HandleBlockReturn(_) => Set.empty
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, bod, rst) => bod.definedVars ++ rst.definedVars
  
  lazy val size: Int = this match
    case _: Return | _: Throw | _: End | _: Break | _: Continue | _: HandleBlockReturn => 1
    case Begin(sub, rst) => sub.size + rst.size
    case Assign(_, _, rst) => 1 + rst.size
    case AssignField(_, _, _, rst) => 1 + rst.size
    case Match(_, arms, dflt, rst) =>
      1 + arms.map(_._2.size).sum + dflt.map(_.size).getOrElse(0) + rst.size
    case Define(_, rst) => 1 + rst.size
    case TryBlock(sub, fin, rst) => 1 + sub.size + fin.size + rst.size
    case Label(_, bod, rst) => 1 + bod.size + rst.size
    case HandleBlock(lhs, res, par, cls, handlers, bdy, rst) => 1 + handlers.map(_.body.size).sum + bdy.size + rst.size
  
  // TODO conserve if no changes
  def mapTail(f: BlockTail => BlockTail): Block = this match
    case b: BlockTail => f(b)
    case Begin(sub, rst) => Begin(sub, rst.mapTail(f))
    case Assign(lhs, rhs, rst) => Assign(lhs, rhs, rst.mapTail(f))
    case Define(defn, rst) => Define(defn, rst.mapTail(f))
    case HandleBlock(lhs, res, par, cls, handlers, body, rest) =>
      HandleBlock(lhs, res, par, cls, handlers.map(h => Handler(h.sym, h.resumeSym, h.params, h.body)), body, rest.mapTail(f))
    case Match(scrut, arms, dflt, rst: End) =>
      Match(scrut, arms.map(_ -> _.mapTail(f)), dflt.map(_.mapTail(f)), rst)
    case Match(scrut, arms, dflt, rst) =>
      Match(scrut, arms, dflt, rst.mapTail(f))
  
  lazy val freeVars: Set[Local] = this match
    case Match(scrut, arms, dflt, rest) =>
      scrut.freeVars ++ dflt.toList.flatMap(_.freeVars) ++ rest.freeVars
      ++ arms.flatMap:
        (pat, arm) => arm.freeVars -- pat.freeVars
    case Return(res, implct) => res.freeVars
    case Throw(exc) => exc.freeVars
    case Label(label, body, rest) => (body.freeVars - label) ++ rest.freeVars 
    case Break(label) => Set(label)
    case Continue(label) => Set(label)
    case Begin(sub, rest) => sub.freeVars ++ rest.freeVars
    case TryBlock(sub, finallyDo, rest) => sub.freeVars ++ finallyDo.freeVars ++ rest.freeVars
    case Assign(lhs, rhs, rest) => Set(lhs) ++ rhs.freeVars ++ rest.freeVars
    case AssignField(lhs, nme, rhs, rest) => lhs.freeVars ++ rhs.freeVars ++ rest.freeVars
    case Define(defn, rest) => defn.freeVars ++ rest.freeVars
    case HandleBlock(lhs, res, par, cls, hdr, bod, rst) =>
      (bod.freeVars - lhs) ++ rst.freeVars ++ hdr.flatMap(_.freeVars)
    case HandleBlockReturn(res) => res.freeVars
    case End(msg) => Set.empty

  def floatOutDefns =
    def rec(b: Block, acc: List[Defn]): (Block, List[Defn]) = b match
      case Match(scrut, arms, dflt, rest) =>
        val (armsRes, armsDefns) = arms.foldLeft[(List[(Case, Block)], List[Defn])](Nil, acc)(
          (accc, d) =>
            val (accCases, accDefns) = accc
            val (cse, blk) = d
            val (resBlk, resDefns) = rec(blk, accDefns)
            ((cse, resBlk) :: accCases, resDefns)
        )
        dflt match
        case None =>
          val (rstRes, rstDefns) = rec(rest, armsDefns)
          (Match(scrut, armsRes, None, rstRes), rstDefns)

        case Some(dflt) =>
          val (dfltRes, dfltDefns) = rec(dflt, armsDefns)
          val (rstRes, rstDefns) = rec(rest, dfltDefns)
          (Match(scrut, armsRes, S(dfltRes), rstRes), rstDefns)
        
      case Return(res, implct) => (b, acc)
      case Throw(exc) => (b, acc)
      case Label(label, body, rest) =>
        val (bodyRes, bodyDefns) = rec(body, acc)
        val (rstRes, rstDefns) = rec(rest, bodyDefns)
        (Label(label, bodyRes, rstRes), rstDefns)
      case Break(label) => (b, acc)
      case Continue(label) => (b, acc)
      case Begin(sub, rest) => 
        val (subRes, subDefns) = rec(sub, acc)
        val (rstRes, rstDefns) = rec(rest, subDefns)
        (Begin(subRes, rstRes), rstDefns)
      case TryBlock(sub, finallyDo, rest) =>
        val (subRes, subDefns) = rec(sub, acc)
        val (finallyRes, finallyDefns) = rec(rest, subDefns)
        val (rstRes, rstDefns) = rec(rest, finallyDefns)
        (TryBlock(subRes, finallyRes, rstRes), rstDefns)
      case Assign(lhs, rhs, rest) => 
        val (rstRes, rstDefns) = rec(rest, acc)
        (Assign(lhs, rhs, rstRes), rstDefns)
      case a @ AssignField(path, nme, result, rest) =>
        val (rstRes, rstDefns) = rec(rest, acc)
        (AssignField(path, nme, result, rstRes)(a.symbol), rstDefns)
      case Define(defn, rest) => defn match
        case ValDefn(owner, k, sym, rhs) => 
          val (rstRes, rstDefns) = rec(rest, acc)
          (Define(defn, rstRes), rstDefns)
        case _ =>
          val (rstRes, rstDefns) = rec(rest, defn :: acc)
          (rstRes, rstDefns)
      case HandleBlock(lhs, res, par, cls, handlers, body, rest) =>
        val (rstRes, rstDefns) = rec(rest, acc)
        (HandleBlock(lhs, res, par, cls, handlers, body, rstRes), rstDefns)
      case HandleBlockReturn(res) => (b, acc)
      case End(msg) => (b, acc)
    rec(this, Nil)

end Block

sealed abstract class BlockTail extends Block

case class Match(
  scrut: Path,
  arms: Ls[Case -> Block],
  dflt: Opt[Block],
  rest: Block,
) extends Block with ProductWithTail

// * `implct`: whether it's a JS implicit return, without the `return` keyword
// * TODO could just remove this flag and add a flag in Scope instead
case class Return(res: Result, implct: Bool) extends BlockTail

case class Throw(exc: Result) extends BlockTail

case class Label(label: Local, body: Block, rest: Block) extends BlockTail

case class Break(label: Local) extends BlockTail
case class Continue(label: Local) extends BlockTail

// TODO: remove this form?
case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail

case class TryBlock(sub: Block, finallyDo: Block, rest: Block) extends Block with ProductWithTail

case class Assign(lhs: Local, rhs: Result, rest: Block) extends Block with ProductWithTail
// case class Assign(lhs: Path, rhs: Result, rest: Block) extends Block with ProductWithTail

case class AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block)(val symbol: Opt[FieldSymbol]) extends Block with ProductWithTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail

case class HandleBlock(lhs: Local, res: Local, par: Path, cls: ClassSymbol, handlers: Ls[Handler], body: Block, rest: Block) extends Block with ProductWithTail
case class HandleBlockReturn(res: Result) extends BlockTail

sealed abstract class Defn:
  val sym: MemberSymbol[?]

  lazy val freeVars: Set[Local] = this match
    case FunDefn(sym, params, body) => body.freeVars -- params.flatMap(_.paramSyms) - sym
    case ValDefn(owner, k, sym, rhs) => rhs.freeVars
    case ClsLikeDefn(sym, k, parentSym, methods, privateFields, publicFields, preCtor, ctor) =>
      preCtor.freeVars
        ++ ctor.freeVars ++ methods.flatMap(_.freeVars)
        -- privateFields -- publicFields.map(_.sym)
  
final case class FunDefn(
    sym: BlockMemberSymbol,
    params: Ls[ParamList],
    body: Block,
) extends Defn

final case class ValDefn(
    owner: Opt[InnerSymbol],
    k: syntax.Val,
    sym: BlockMemberSymbol,
    rhs: Path,
) extends Defn

final case class ClsLikeDefn(
  sym: MemberSymbol[? <: ClassLikeDef],
  k: syntax.ClsLikeKind,
  parentPath: Opt[Path],
  methods: Ls[FunDefn],
  privateFields: Ls[TermSymbol],
  publicFields: Ls[TermDefinition],
  preCtor: Block,
  ctor: Block,
) extends Defn

final case class Handler(
    sym: BlockMemberSymbol,
    resumeSym: LocalSymbol & NamedSymbol,
    params: Ls[ParamList],
    body: Block,
):
  lazy val freeVars: Set[Local] = body.freeVars -- params.flatMap(_.paramSyms) - sym - resumeSym

/* Represents either unreachable code (for functions that must return a result)
 * or the end of a non-returning function or a REPL block */
case class End(msg: Str = "") extends BlockTail with ProductWithTail

enum Case:
  case Lit(lit: Literal)
  case Cls(cls: ClassLikeSymbol, path: Path)
  case Tup(len: Int, inf: Bool)

  lazy val freeVars: Set[Local] = this match
    case Lit(_) => Set.empty
    case Cls(_, path) => path.freeVars
    case Tup(_, _) => Set.empty

sealed abstract class Result:

  lazy val freeVars: Set[Local] = this match
    case Call(fun, args) => args.flatMap(_.value.freeVars).toSet
    case Instantiate(cls, args) => args.flatMap(_.freeVars).toSet
    case Select(qual, name) => qual.freeVars 
    case Value.Ref(l) => Set(l)
    case Value.This(sym) => Set.empty
    case Value.Lit(lit) => Set.empty
    case Value.Lam(params, body) => body.freeVars -- params.paramSyms
    case Value.Arr(elems) => elems.flatMap(_.value.freeVars).toSet
  
// type Local = LocalSymbol
type Local = Symbol

case class Call(fun: Path, args: Ls[Arg])(val isMlsFun: Bool) extends Result

case class Instantiate(cls: Path, args: Ls[Path]) extends Result

sealed abstract class Path extends Result:
  def selN(id: Tree.Ident) = Select(this, id)(N)
  def asArg = Arg(false, this)

case class Select(qual: Path, name: Tree.Ident)(val symbol: Opt[FieldSymbol]) extends Path with ProductWithExtraInfo:
  def extraInfo: Str = symbol.mkString

enum Value extends Path:
  case Ref(l: Local)
  case This(sym: InnerSymbol) // TODO rm – just use Ref
  case Lit(lit: Literal)
  case Lam(params: ParamList, body: Block)
  case Arr(elems: Ls[Arg])

case class Arg(spread: Bool, value: Path)

extension (k: Block => Block)
  
  def chain(other: Block => Block): Block => Block = b => k(other(b))
  def rest(b: Block): Block = k(b)
  def transform(f: (Block => Block) => (Block => Block)) = f(k)
  
  def assign(l: Local, r: Result) = k.chain(Assign(l, r, _))
  def assignFieldN(lhs: Path, nme: Tree.Ident, rhs: Result) = k.chain(AssignField(lhs, nme, rhs, _)(N))
  def break(l: Local): Block = k.rest(Break(l))
  def continue(l: Local): Block = k.rest(Continue(l))
  def define(defn: Defn) = k.chain(Define(defn, _))
  def end = k.rest(End())
  def ifthen(scrut: Path, cse: Case, trm: Block): Block => Block = k.chain(Match(scrut, cse -> trm :: Nil, N, _))
  def label(label: Local, body: Block) = k.chain(Label(label, body, _))
  def ret(r: Result) = k.rest(Return(r, false))
  def staticif(b: Boolean, f: (Block => Block) => (Block => Block)) = if b then k.transform(f) else k

def blockBuilder: Block => Block = identity

extension (l: Local)
  def asPath: Path = Value.Ref(l)
