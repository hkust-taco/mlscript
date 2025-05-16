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
  
  def ~(that: Block): Block = Begin(this, that)
  
  protected def children: Ls[Located] = this match
    case Match(scrut, arms, dflt, rest) => scrut :: arms.map(_._2) ++ dflt.toList :+ rest
    case Return(res, implct) => res :: Nil
    case Throw(exc) => exc :: Nil
    case Label(label, body, rest) => label :: body :: rest :: Nil
    case Break(label) => label :: Nil
    case Continue(label) => label :: Nil
    case Begin(sub, rest) => sub :: rest :: Nil
    case TryBlock(sub, finallyDo, rest) => sub :: finallyDo :: rest :: Nil
    case Assign(lhs, rhs, rest) => lhs :: rhs :: rest :: Nil
    case AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block) => lhs :: nme :: rhs :: rest :: Nil
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => lhs :: fld :: rhs :: rest :: Nil
    case Define(FunDefn(owner, sym, params, body), rest) => sym :: (params :+ body :+ rest)
    case Define(ValDefn(owner, k, sym, rhs), rest) => sym :: rhs :: rest :: Nil
    case Define(ClsLikeDefn(owner, isym, sym, k, paramsOpt, aux, parentSym, methods, privFlds, pubFlds, preCtor, ctor), rest) =>
      isym :: sym :: paramsOpt.toList ++ aux ++ parentSym.toList ++ methods.flatMap(_.subBlocks) ++ privFlds ++ pubFlds
      ++ preCtor.subBlocks ++ ctor.subBlocks :+ rest
    case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
      lhs :: res :: par :: args ++ handlers.flatMap: handler =>
        handler.sym :: handler.resumeSym :: (handler.params :+ handler.body)
      :+ body :+ rest
    case End(msg) => Nil
  
  lazy val definedVars: Set[Local] = this match
    case _: Return | _: Throw => Set.empty
    case Begin(sub, rst) => sub.definedVars ++ rst.definedVars
    case Assign(l: TermSymbol, r, rst) => rst.definedVars
    case Assign(l, r, rst) => rst.definedVars + l
    case AssignField(l, n, r, rst) => rst.definedVars
    case AssignDynField(l, n, ai, r, rst) => rst.definedVars
    case Match(scrut, arms, dflt, rst) =>
      arms.flatMap(_._2.definedVars).toSet ++ dflt.toList.flatMap(_.definedVars) ++ rst.definedVars
    case End(_) => Set.empty
    case Break(_) => Set.empty
    case Continue(_) => Set.empty
    case Define(defn, rst) =>
      val rest = rst.definedVars
      if defn.isOwned then rest else rest + defn.sym
    // Note that the handler's LHS and body are not part of the current block, so we do not consider them here.
    case HandleBlock(lhs, res, par, args, cls, hdr, bod, rst) => rst.definedVars + res
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, bod, rst) => bod.definedVars ++ rst.definedVars
  
  lazy val size: Int = this match
    case _: Return | _: Throw | _: End | _: Break | _: Continue => 1
    case Begin(sub, rst) => sub.size + rst.size
    case Assign(_, _, rst) => 1 + rst.size
    case AssignField(_, _, _, rst) => 1 + rst.size
    case AssignDynField(_, _, _, _, rst) => 1 + rst.size
    case Match(_, arms, dflt, rst) =>
      1 + arms.map(_._2.size).sum + dflt.map(_.size).getOrElse(0) + rst.size
    case Define(_, rst) => 1 + rst.size
    case TryBlock(sub, fin, rst) => 1 + sub.size + fin.size + rst.size
    case Label(_, bod, rst) => 1 + bod.size + rst.size
    case HandleBlock(lhs, res, par, args, cls, handlers, bdy, rst) => 1 + handlers.map(_.body.size).sum + bdy.size + rst.size
  
  // TODO conserve if no changes
  def mapTail(f: BlockTail => Block): Block = this match
    case b: BlockTail => f(b)
    case Begin(sub, rst) => Begin(sub, rst.mapTail(f))
    case Assign(lhs, rhs, rst) => Assign(lhs, rhs, rst.mapTail(f))
    case Define(defn, rst) => Define(defn, rst.mapTail(f))
    case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
      HandleBlock(lhs, res, par, args, cls, handlers.map(h => Handler(h.sym, h.resumeSym, h.params, h.body)), body, rest.mapTail(f))
    case Match(scrut, arms, dflt, rst: End) =>
      Match(scrut, arms.map(_ -> _.mapTail(f)), dflt.map(_.mapTail(f)), rst)
    case Match(scrut, arms, dflt, rst) =>
      Match(scrut, arms, dflt, rst.mapTail(f))
    case Label(label, body, rest) => Label(label, body, rest.mapTail(f))
    case af @ AssignField(lhs, nme, rhs, rest) =>
      AssignField(lhs, nme, rhs, rest.mapTail(f))(af.symbol)
    case adf @ AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      AssignDynField(lhs, fld, arrayIdx, rhs, rest.mapTail(f))
    case tb @ TryBlock(sub, fin, rest) =>
      TryBlock(sub, fin, rest.mapTail(f))
  
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
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => lhs.freeVars ++ fld.freeVars ++ rhs.freeVars ++ rest.freeVars
    case Define(defn, rest) => defn.freeVars ++ rest.freeVars
    case HandleBlock(lhs, res, par, args, cls, hdr, bod, rst) =>
      (bod.freeVars - lhs) ++ rst.freeVars ++ hdr.flatMap(_.freeVars)
    case End(msg) => Set.empty
  
  lazy val freeVarsLLIR: Set[Local] = this match
    case Match(scrut, arms, dflt, rest) =>
      scrut.freeVarsLLIR ++ dflt.toList.flatMap(_.freeVarsLLIR) ++ rest.freeVarsLLIR
      ++ arms.flatMap:
        (pat, arm) => arm.freeVarsLLIR -- pat.freeVarsLLIR
    case Return(res, implct) => res.freeVarsLLIR
    case Throw(exc) => exc.freeVarsLLIR
    case Label(label, body, rest) => (body.freeVarsLLIR - label) ++ rest.freeVarsLLIR 
    case Break(label) => Set.empty
    case Continue(label) => Set.empty
    case Begin(sub, rest) => sub.freeVarsLLIR ++ rest.freeVarsLLIR
    case TryBlock(sub, finallyDo, rest) => sub.freeVarsLLIR ++ finallyDo.freeVarsLLIR ++ rest.freeVarsLLIR
    case Assign(lhs, rhs, rest) => rhs.freeVarsLLIR ++ (rest.freeVarsLLIR - lhs)
    case AssignField(lhs, nme, rhs, rest) => lhs.freeVarsLLIR ++ rhs.freeVarsLLIR ++ rest.freeVarsLLIR
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => lhs.freeVarsLLIR ++ fld.freeVarsLLIR ++ rhs.freeVarsLLIR ++ rest.freeVarsLLIR
    case Define(defn, rest) => defn.freeVarsLLIR ++ (rest.freeVarsLLIR - defn.sym)
    case HandleBlock(lhs, res, par, args, cls, hdr, bod, rst) =>
      (bod.freeVarsLLIR - lhs) ++ rst.freeVarsLLIR ++ hdr.flatMap(_.freeVarsLLIR)
    case End(msg) => Set.empty
  
  lazy val subBlocks: Ls[Block] = this match
    case Match(p, arms, dflt, rest) => p.subBlocks ++ arms.map(_._2) ++ dflt.toList :+ rest
    case Begin(sub, rest) => sub :: rest :: Nil
    case TryBlock(sub, finallyDo, rest) => sub :: finallyDo :: rest :: Nil
    case Assign(_, rhs, rest) => rhs.subBlocks ::: rest :: Nil
    case AssignField(_, _, rhs, rest) => rhs.subBlocks ::: rest :: Nil
    case AssignDynField(_, _, _, rhs, rest) => rhs.subBlocks ::: rest :: Nil
    case Define(d, rest) => d.subBlocks ::: rest :: Nil
    case HandleBlock(_, _, par, args, _, handlers, body, rest) => par.subBlocks ++ args.flatMap(_.subBlocks) ++ handlers.map(_.body) :+ body :+ rest
    case Label(_, body, rest) => body :: rest :: Nil
    
    // TODO rm Lam from values and thus the need for these cases
    case Return(r, _) => r.subBlocks
    case Throw(r) => r.subBlocks
    
    case _: Return | _: Throw | _: Break | _: Continue | _: End => Nil
  
  // Moves definitions in a block to the top. Only scans the top-level definitions of the block;
  // i.e, definitions inside other definitions are not moved out. Definitions inside `match`/`if`
  // and `while` statements are moved out.
  //
  // Note that this returns the definitions in reverse order, with the bottommost definiton appearing
  // last. This is so that using defns.foldLeft later to add the definitions to the front of a block, 
  // we don't need to reverse the list again to preserve the order of the definitions.
  def floatOutDefns(
      ignore: Defn => Bool = _ => false, 
      preserve: Defn => Bool = _ => false
    ) =
    var defns: List[Defn] = Nil
    val transformer = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(defn, rest) if !ignore(defn) => defn match
          case v: ValDefn => super.applyBlock(b)
          case _ =>
            defns ::= defn
            if preserve(defn) then super.applyBlock(b)
            else applyBlock(rest)
        case _ => super.applyBlock(b)
    
    (transformer.applyBlock(this), defns)
    
  lazy val flattened: Block = this.flatten(identity)
  
  private def flatten(k: End => Block): Block = this match
    case Match(scrut, arms, dflt, rest) =>
      val newRest = rest.flatten(k)
      val newArms = arms.mapConserve: arm =>
        val newBody = arm._2.flattened
        if newBody is arm._2 then arm else (arm._1, newBody)
      val newDflt = dflt.map(_.flattened)
      if (newRest is rest) && (newArms is arms) && (dflt is newDflt)
      then this
      else Match(scrut, newArms, newDflt, newRest)

    case Label(label, body, rest) =>
      val newBody = body.flattened
      val newRest = rest.flatten(k)
      if (newBody is body) && (newRest is rest)
      then this
      else Label(label, newBody, newRest)
      
    case Begin(sub, rest) =>
      sub.flatten(_ => rest.flatten(k))
    
    case TryBlock(sub, finallyDo, rest) =>
      val newSub = sub.flattened
      val newFinallyDo = finallyDo.flattened
      val newRest = rest.flatten(k)
      if (newSub is sub) && (newFinallyDo is finallyDo) && (newRest is rest)
      then this
      else TryBlock(newSub, newFinallyDo, newRest)
      
    case Assign(lhs, rhs, rest) =>
      val newRest = rest.flatten(k)
      if newRest is rest
      then this
      else Assign(lhs, rhs, newRest)
      
    case a@AssignField(lhs, nme, rhs, rest) =>
      val newRest = rest.flatten(k)
      if newRest is rest
      then this
      else AssignField(lhs, nme, rhs, newRest)(a.symbol)
      
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      val newRest = rest.flatten(k)
      if newRest is rest
      then this
      else AssignDynField(lhs, fld, arrayIdx, rhs, newRest)
    
    case Define(defn, rest) =>
      val newDefn = defn match
        case d: FunDefn =>
          val newBody = d.body.flattened
          if newBody is d.body
          then d
          else d.copy(body = newBody)
        case v: ValDefn => v
        case c: ClsLikeDefn =>
          val newPreCtor = c.preCtor.flattened
          val newCtor = c.ctor.flattened
          if (newPreCtor is c.preCtor) && (newCtor is c.ctor)
          then c
          else c.copy(preCtor = newPreCtor, ctor = newCtor)
      
      val newRest = rest.flatten(k)
      if (newDefn is defn) && (newRest is rest)
      then this
      else Define(newDefn, newRest)
    
    case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
      val newHandlers = handlers.mapConserve: h =>
        val newBody = h.body.flattened
        if newBody is h.body then h else h.copy(body = newBody)
      val newBody = body.flattened
      val newRest = rest.flatten(k)
      if (newHandlers is handlers) && (newBody is body) && (newRest is rest)
      then this
      else HandleBlock(lhs, res, par, args, cls, newHandlers, newBody, newRest)

    case e: End => k(e)
    case t: BlockTail => this
  
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

case class Label(label: Local, body: Block, rest: Block) extends Block

case class Break(label: Local) extends BlockTail
case class Continue(label: Local) extends BlockTail

// TODO: remove this form?
case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail

case class TryBlock(sub: Block, finallyDo: Block, rest: Block) extends Block with ProductWithTail

case class Assign(lhs: Local, rhs: Result, rest: Block) extends Block with ProductWithTail
// case class Assign(lhs: Path, rhs: Result, rest: Block) extends Block with ProductWithTail

case class AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block)(val symbol: Opt[FieldSymbol]) extends Block with ProductWithTail

case class AssignDynField(lhs: Path, fld: Path, arrayIdx: Bool, rhs: Result, rest: Block) extends Block with ProductWithTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail

case class HandleBlock(
    lhs: Local,
    res: Local,
    par: Path,
    args: Ls[Path],
    cls: ClassSymbol,
    handlers: Ls[Handler],
    body: Block,
    rest: Block
) extends Block with ProductWithTail

sealed abstract class Defn:
  val innerSym: Opt[MemberSymbol[?]]
  val sym: BlockMemberSymbol
  def isOwned: Bool = owner.isDefined
  def owner: Opt[InnerSymbol]
  
  def subBlocks: Ls[Block] = this match
    case FunDefn(body = body) => body :: Nil
    case _: ValDefn => Nil
    case ClsLikeDefn(preCtor = preCtor, ctor = ctor, methods = mtds) =>
      preCtor :: ctor :: mtds.flatMap(_.subBlocks)
  
  // * Note that `privateFields` abd `publicFields` can't possibly be free since they are never
  // * referred to directly (they are only accessed through selections).
  // * At some point we'll want to make `Local` more specific than `Symbol` to express this
  // * in the type system.
  lazy val freeVars: Set[Local] = this match
    case FunDefn(own, sym, params, body) => body.freeVars -- params.flatMap(_.paramSyms) - sym
    case ValDefn(owner, k, sym, rhs) => rhs.freeVars
    case ClsLikeDefn(own, isym, sym, k, paramsOpt, auxParams, parentSym, 
        methods, privateFields, publicFields, preCtor, ctor) =>
      preCtor.freeVars
        ++ ctor.freeVars ++ methods.flatMap(_.freeVars)
        -- auxParams.flatMap(_.paramSyms)
  
  lazy val freeVarsLLIR: Set[Local] = this match
    case FunDefn(own, sym, params, body) => body.freeVarsLLIR -- params.flatMap(_.paramSyms) - sym
    case ValDefn(owner, k, sym, rhs) => rhs.freeVarsLLIR
    case ClsLikeDefn(own, isym, sym, k, paramsOpt, auxParams, parentSym, 
        methods, privateFields, publicFields, preCtor, ctor) =>
      preCtor.freeVarsLLIR
        ++ ctor.freeVarsLLIR ++ methods.flatMap(_.freeVarsLLIR)
        -- auxParams.flatMap(_.paramSyms)
  
final case class FunDefn(
    owner: Opt[InnerSymbol],
    sym: BlockMemberSymbol,
    params: Ls[ParamList],
    body: Block,
) extends Defn:
  val innerSym = N

final case class ValDefn(
    owner: Opt[InnerSymbol],
    k: syntax.Val,
    sym: BlockMemberSymbol,
    rhs: Path,
) extends Defn:
  val innerSym = N

final case class ClsLikeDefn(
    owner: Opt[InnerSymbol],
    isym: MemberSymbol[? <: ClassLikeDef] & InnerSymbol,
    sym: BlockMemberSymbol,
    k: syntax.ClsLikeKind,
    paramsOpt: Opt[ParamList],
    auxParams: List[ParamList],
    parentPath: Opt[Path],
    methods: Ls[FunDefn],
    privateFields: Ls[TermSymbol],
    publicFields: Ls[BlockMemberSymbol],
    preCtor: Block,
    ctor: Block,
) extends Defn:
  val innerSym = S(isym)

final case class Handler(
    sym: BlockMemberSymbol,
    resumeSym: VarSymbol,
    params: Ls[ParamList],
    body: Block,
):
  lazy val freeVars: Set[Local] = body.freeVars -- params.flatMap(_.paramSyms) - sym - resumeSym
  lazy val freeVarsLLIR: Set[Local] = body.freeVarsLLIR -- params.flatMap(_.paramSyms) - sym - resumeSym

/* Represents either unreachable code (for functions that must return a result)
 * or the end of a non-returning function or a REPL block */
case class End(msg: Str = "") extends BlockTail with ProductWithTail

enum Case:
  case Lit(lit: Literal)
  case Cls(cls: ClassLikeSymbol, path: Path)
  case Tup(len: Int, inf: Bool)
  /** checks field existence
    * @param safe true will omit the instanceof Object check
  */
  case Field(name: Tree.Ident, safe: Bool)

  lazy val freeVars: Set[Local] = this match
    case Lit(_) => Set.empty
    case Cls(_, path) => path.freeVars
    case Tup(_, _) => Set.empty
    case Field(_, _) => Set.empty
  
  lazy val freeVarsLLIR: Set[Local] = this match
    case Lit(_) => Set.empty
    case Cls(_, path) => path.freeVarsLLIR
    case Tup(_, _) => Set.empty
    case Field(_, _) => Set.empty

sealed trait TrivialResult extends Result

sealed abstract class Result extends AutoLocated:

  protected def children: List[Located] = this match
    case Call(fun, args) => fun :: args.map(_.value)
    case Instantiate(cls, args) => cls :: args
    case Select(qual, name) => qual :: name :: Nil
    case DynSelect(qual, fld, arrayIdx) => qual :: fld :: Nil
    case Value.Ref(l) => Nil
    case Value.This(sym) => Nil
    case Value.Lit(lit) => lit :: Nil
    case Value.Lam(params, body) => params :: body :: Nil
    case Value.Arr(elems) => elems.map(_.value)
    case Value.Rcd(elems) => elems.map(_.value)
  
  // TODO rm Lam from values and thus the need for this method
  def subBlocks: Ls[Block] = this match
    case Call(fun, args) => fun.subBlocks ::: args.flatMap(_.value.subBlocks)
    case Instantiate(cls, args) => args.flatMap(_.subBlocks)
    case Select(qual, name) => qual.subBlocks
    case Value.Lam(params, body) => body :: Nil
    case Value.Arr(elems) => elems.flatMap(_.value.subBlocks)
    case _ => Nil
  
  lazy val freeVars: Set[Local] = this match
    case Call(fun, args) => fun.freeVars ++ args.flatMap(_.value.freeVars).toSet
    case Instantiate(cls, args) => cls.freeVars ++ args.flatMap(_.freeVars).toSet
    case Select(qual, name) => qual.freeVars 
    case Value.Ref(l) => Set(l)
    case Value.This(sym) => Set.empty
    case Value.Lit(lit) => Set.empty
    case Value.Lam(params, body) => body.freeVars -- params.paramSyms
    case Value.Arr(elems) => elems.flatMap(_.value.freeVars).toSet
    case Value.Rcd(elems) => elems.flatMap(_.value.freeVars).toSet
    case DynSelect(qual, fld, arrayIdx) => qual.freeVars ++ fld.freeVars
    case Value.Rcd(args) => args.flatMap(arg => arg.idx.fold(Set.empty)(_.freeVars) ++ arg.value.freeVars).toSet

  lazy val freeVarsLLIR: Set[Local] = this match
    case Call(fun, args) => fun.freeVarsLLIR ++ args.flatMap(_.value.freeVarsLLIR).toSet
    case Instantiate(cls, args) => cls.freeVarsLLIR ++ args.flatMap(_.freeVarsLLIR).toSet
    case Select(qual, name) => qual.freeVarsLLIR 
    case Value.Ref(l: (BuiltinSymbol | TopLevelSymbol | ClassSymbol | TermSymbol)) => Set.empty
    case Value.Ref(l: MemberSymbol[?]) => l.defn match
      case Some(d: ClassLikeDef) => Set.empty
      case _ => Set(l)
    case Value.Ref(l) => Set(l)
    case Value.This(sym) => Set.empty
    case Value.Lit(lit) => Set.empty
    case Value.Lam(params, body) => body.freeVarsLLIR -- params.paramSyms
    case Value.Arr(elems) => elems.flatMap(_.value.freeVarsLLIR).toSet
    case Value.Rcd(elems) => elems.flatMap(_.value.freeVarsLLIR).toSet
    case DynSelect(qual, fld, arrayIdx) => qual.freeVarsLLIR ++ fld.freeVarsLLIR
    case Value.Rcd(args) => args.flatMap(arg => arg.idx.fold(Set.empty)(_.freeVarsLLIR) ++ arg.value.freeVarsLLIR).toSet
  
// type Local = LocalSymbol
type Local = Symbol

/* mayRaiseEffects indicates whether this call may raise effect (algebraic effect),
 * regardless of whether the check for effect is inserted or not.
 * Note that the check for effect is inserted during HandlerLowering and setting this to true
 * after handler is lowered does not have any effect on the code generation. */
case class Call(fun: Path, args: Ls[Arg])(val isMlsFun: Bool, val mayRaiseEffects: Bool) extends Result

case class Instantiate(cls: Path, args: Ls[Path]) extends Result

sealed abstract class Path extends TrivialResult:
  def selN(id: Tree.Ident): Path = Select(this, id)(N)
  def sel(id: Tree.Ident, sym: FieldSymbol): Path = Select(this, id)(S(sym))
  def selSN(id: Str): Path = selN(new Tree.Ident(id))
  def asArg = Arg(false, this)

case class Select(qual: Path, name: Tree.Ident)(val symbol: Opt[FieldSymbol]) extends Path with ProductWithExtraInfo:
  def extraInfo: Str = symbol.mkString

case class DynSelect(qual: Path, fld: Path, arrayIdx: Bool) extends Path

enum Value extends Path:
  case Ref(l: Local)
  case This(sym: InnerSymbol) // TODO rm – just use Ref
  case Lit(lit: Literal)
  case Lam(params: ParamList, body: Block)
  case Arr(elems: Ls[Arg])
  case Rcd(elems: Ls[RcdArg])

case class Arg(spread: Bool, value: Path)

// * `IndxdArg(S(idx), value)` represents a key-value pair in a record `(idx): value`
// * `IndxdArg(N, value)` represents a spread element in a record `...value`
case class RcdArg(idx: Opt[Path], value: Path):
  def spread: Bool = idx.isEmpty

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
  def ifthen(scrut: Path, cse: Case, trm: Block, els: Opt[Block] = N): Block => Block =
    k.chain(Match(scrut, cse -> trm :: Nil, els, _))
  def label(label: Local, body: Block) = k.chain(Label(label, body, _))
  def ret(r: Result) = k.rest(Return(r, false))
  def staticif(b: Boolean, f: (Block => Block) => (Block => Block)) = if b then k.transform(f) else k
  def foldLeft[A](xs: Iterable[A])(f: (Block => Block, A) => Block => Block) = xs.foldLeft(k)(f)

def blockBuilder: Block => Block = identity

extension (l: Local)
  def asPath: Path = Value.Ref(l)


