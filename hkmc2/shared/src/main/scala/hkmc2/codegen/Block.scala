package hkmc2
package codegen

import scala.collection.mutable.Buffer

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree, SpreadKind, Keyword}
import semantics.*
import semantics.Term.*
import sem.Elaborator.State


/* Important design notes.

The Middle IR (MIR) or "Block IR" or just "IR" is an implementation of a form of imperative ANF.

While the IR is mostly immutable, for easier manipulation and to enable some optimizations,
we do assume that each DefinitionSymbol coming from the source program is "owned" by at most one IR definition;
this is implemented by making the `Define` and `ClsLikeDefn` constructors
set the `irDefn` field of the symbol they define.
This means that if a program fragment containing definitions is rewritten at all,
then the rewritten version must be kept as the "currently valid" version, and the old one must no longer be reused,
as a given symbol can never correspond to more than one IR definition.

Moreover, we generally assume that in a given program, no symbol is every bound more than once
by any binding form, such as Scoped, Label, Define. (This is currently not completely enforced, though.)
This means that processes that duplicate binding forms within a program (eg, inlining)
must refresh the corresponding symbols – see SymbolRefresher for this purpose.

*/


case class Program(
  imports: Ls[ImportSymbol -> Str],
  main: Block,
)


/** Symbol that can be used in a `SimpleRef`. */
type SimpleSymbol = LocalVarSymbol | BuiltinSymbol

/** Symbol that can be used as the left-hand side of an `Assign`. */
type Assignable = LocalVarSymbol | NoSymbol

/** Symbols that `Scoped` introduces as block-local bindings.
  * This deliberately excludes things like `TermSymbol`s, which never need to be scoped.
  */
type ScopedSymbol = LocalVarSymbol | BlockMemberSymbol

/** A "catch-all" symbol for value-like things.
  * Slightly better than just `Symbol`, but we should still try migrating away to more specific symbol types.
  */
type ValueSymbol = SimpleSymbol | TermSymbol | BlockMemberSymbol | InnerSymbol

/** Symbols that may be bound by MIR binding forms such as `Scoped`.
  */
type BoundSymbol = ScopedSymbol | TermSymbol

/** Symbols that may occur in MIR free-variable sets.
  */
type FreeSymbol = SimpleSymbol | BlockMemberSymbol | LabelSymbol


sealed abstract class Block extends Product:
  
  def ~(that: Block): Block = Begin(this, that)
  
  def isEmpty: Bool = this match
    case _: End => true
    case _ => false
  
  def showDbg(using DebugPrinter): Str = this match
    case End(msg) => s"End(${msg})"
    case Unreachable(msg) => s"Unreachable(${msg})"
    case Break(lbl) => s"Break(${lbl.showDbg})"
    case Continue(lbl) => s"Continue(${lbl.showDbg})"
    case Return(res) => s"Return(${res.showDbg})"
    case Match(scrut, arms, dflt, rest) =>
      val armsStr = arms.map((pat, arm) => s"case ${pat.showDbg} => ${arm.showDbg}").mkString("\n")
      val dfltStr = dflt.map(d => s"default => ${d.showDbg}\n").getOrElse("")
      s"""|Match(${scrut.showDbg}) {
          |$armsStr
          |$dfltStr
          |}
          |${rest.showDbg}""".stripMargin
    case Label(lbl, loop, body, rest) =>
      s"""|Label(${lbl.showDbg}, loop = $loop) {
          |${body.showDbg}
          |}
          |${rest.showDbg}""".stripMargin
    case Begin(sub, rest) =>
      s"""|Begin {
          |${sub.showDbg}
          |}
          |${rest.showDbg}""".stripMargin
    case TryBlock(sub, finallyDo, rest) =>
      s"""|Try {
          |${sub.showDbg}
          |} finally {
          |${finallyDo.showDbg}
          |}
          |${rest.showDbg}""".stripMargin
    case Assign(lhs, rhs, rest) =>
      s"""|Assign(${lhs.showDbg} = ${rhs.showDbg})
          |${rest.showDbg}""".stripMargin
    case AssignField(lhs, nme, rhs, rest) =>
      s"""|AssignField(${lhs.showDbg}.${nme} = ${rhs.showDbg})
          |${rest.showDbg}""".stripMargin
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      val access = if arrayIdx then s"[${fld.showDbg}]" else s".${fld.showDbg}"
      s"""|AssignDynField(${lhs.showDbg}$access = ${rhs.showDbg})
          |${rest.showDbg}""".stripMargin
    case Define(defn, rest) =>
      s"""|Define(${defn.showDbg})
          |${rest.showDbg}""".stripMargin
    case Throw(exc) => s"Throw(${exc.showDbg})"
    case Scoped(syms, body) =>
      s"""|Scoped(${syms.toList.map(_.showDbg).sorted.mkString(", ")}) {
          |${body.showDbg}
          |}""".stripMargin
  
  lazy val isAbortive: Bool = this match
    case _: End => false
    case _: Throw | _: Break | _: Continue | _: Unreachable => true
    case _: Return => true
    case Begin(sub, rst) => sub.isAbortive || rst.isAbortive
    case Assign(_, _, rst) => rst.isAbortive
    case AssignField(_, _, _, rst) => rst.isAbortive
    case AssignDynField(_, _, _, _, rst) => rst.isAbortive
    case Match(_, arms, dflt, rst) => rst.isAbortive || arms.forall(_._2.isAbortive) && dflt.exists(_.isAbortive)
    case Define(_, rst) => rst.isAbortive
    case TryBlock(sub, fin, rst) => rst.isAbortive || sub.isAbortive || fin.isAbortive
    case Label(sym, loop, bod, rst) =>
      // * Note: the body may be abortive for the reason of breaking to the rest!
      // * So we can't really use the result of bod.isAbortive even when `loop` is false.
      rst.isAbortive
    case Scoped(_, body) => body.isAbortive
  
  // * Note: this function is only for rather fringe use-cases in the optimizer;
  // * it should not be used for scope analysis purposes
  // * (like it used to before we added Scoped blocks).
  lazy val definedVars: Set[BoundSymbol] = this match
    case _: Return | _: Throw | _: Unreachable => Set.empty
    case Begin(sub, rst) => sub.definedVars ++ rst.definedVars
    case Assign(NoSymbol, r, rst) => rst.definedVars
    case Assign(l: LocalVarSymbol, r, rst) => rst.definedVars + l
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
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, _, bod, rst) => bod.definedVars ++ rst.definedVars
    case Scoped(syms, body) => body.definedVars -- syms
  
  lazy val size: Int = 1 + this.match
    case Return(r: Result) => r.size
    case Throw(r: Result) => r.size
    case _: End | _: Break | _: Continue | _: Unreachable => 0
    case Begin(sub, rst) => sub.size + rst.size
    case Assign(_, r, rst) => r.size + rst.size
    case AssignField(p, _, r, rst) => p.size + r.size + rst.size
    case AssignDynField(p, fld, _, r, rst) => p.size + fld.size + r.size + rst.size
    case Match(p, arms, dflt, rst) =>
      p.size + arms.iterator.map(_._2.size).sum + dflt.fold(0)(_.size) + rst.size
    case Define(defn, rst) => defn.size + rst.size
    case TryBlock(sub, fin, rst) => sub.size + fin.size + rst.size
    case Label(_, _, bod, rst) => bod.size + rst.size
    case Scoped(_, body) => body.size - 1
  
  
  // TODO: make patmat use unreach
  
  def mapReturn(f: Return => Block): Block =
    new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(b: Block): Block = b match
        case ret: Return => f(ret)
        case _ => super.applyBlock(b)
    .applyBlock(this)
  
  lazy val freeVars: Set[FreeSymbol] = this match
    case Match(scrut, arms, dflt, rest) =>
      scrut.freeVars ++ dflt.toList.flatMap(_.freeVars) ++ rest.freeVars
      ++ arms.flatMap:
        (pat, arm) => arm.freeVars -- pat.freeVars
    case Return(res) => res.freeVars
    case Throw(exc) => exc.freeVars
    case Label(label, _, body, rest) => (body.freeVars - label) ++ rest.freeVars 
    case Break(label) => Set.single(label)
    case Continue(label) => Set.single(label)
    case Begin(sub, rest) => sub.freeVars ++ rest.freeVars
    case TryBlock(sub, finallyDo, rest) => sub.freeVars ++ finallyDo.freeVars ++ rest.freeVars
    case Assign(NoSymbol, rhs, rest) => rhs.freeVars ++ rest.freeVars
    case Assign(lhs: LocalVarSymbol, rhs, rest) => Set.single(lhs) ++ rhs.freeVars ++ rest.freeVars
    case AssignField(lhs, nme, rhs, rest) => lhs.freeVars ++ rhs.freeVars ++ rest.freeVars
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => lhs.freeVars ++ fld.freeVars ++ rhs.freeVars ++ rest.freeVars
    case Define(defn, rest) => defn.freeVars ++ rest.freeVars
    case Scoped(syms, body) => body.freeVars -- syms
    case End(msg) => Set.empty
    case Unreachable(msg) => Set.empty
  
  lazy val scopedVars: collection.Set[ScopedSymbol] = this match
    case Scoped(syms, body) => syms ++ body.scopedVars
    case _ => this.subBlocks.iterator.flatMap(_.scopedVars).toSet
  
  lazy val subBlocks: Ls[Block] = this match
    case Match(p, arms, dflt, rest) => p.subBlocks ++ arms.map(_._2) ++ dflt.toList :+ rest
    case Begin(sub, rest) => sub :: rest :: Nil
    case TryBlock(sub, finallyDo, rest) => sub :: finallyDo :: rest :: Nil
    case Assign(_, rhs, rest) => rhs.subBlocks ::: rest :: Nil
    case AssignField(_, _, rhs, rest) => rhs.subBlocks ::: rest :: Nil
    case AssignDynField(_, _, _, rhs, rest) => rhs.subBlocks ::: rest :: Nil
    case Define(d, rest) => d.subBlocks ::: rest :: Nil
    case Label(_, _, body, rest) => body :: rest :: Nil
    case Scoped(_, body) => body :: Nil
    
    // TODO rm Lam from results and thus the need for these cases
    case Return(r) => r.subBlocks
    case Throw(r) => r.subBlocks
    
    case _: Return | _: Throw | _: Break | _: Continue | _: End | _: Unreachable => Nil
  
  // Moves definitions in a block to the top. Only scans the top-level definitions of the block;
  // i.e, definitions inside other definitions are not moved out. Definitions inside `match`/`if`
  // and `while` statements are moved out.
  //
  // Note that this returns the definitions in reverse order, with the bottommost definiton appearing
  // last. This is so that using defns.foldLeft later to add the definitions to the front of a block, 
  // we don't need to reverse the list again to preserve the order of the definitions.
  def extractDefns(
        ignore: Defn => Bool = _ => false, 
        preserve: Defn => Bool = _ => false
      ): (Block, List[Defn]) =
    var defns: List[Defn] = Nil
    val transformer = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(b: Block): Block = b match
        case Define(defn, rest) if !ignore(defn) => defn match
          case v: ValDefn => super.applyBlock(b)
          case _ =>
            defns ::= defn
            if preserve(defn) then super.applyBlock(b)
            else applyBlock(rest)
        case _ => super.applyBlock(b)
    
    (transformer.applyBlock(this), defns)
    
  def gatherDefns(
      ignore: Defn => Bool = _ => false, 
      preserve: Defn => Bool = _ => false
    ): List[Defn] = extractDefns(ignore, preserve)._2 // TODO: fix this very inefficient implementation
  
  
  lazy val flattened: Block = this.flatten(identity)
  
  private def flatten(k: End => Block): Block = this match
    
    case Match(scrut, arms, dflt, rest) =>
      val newRest = rest.flatten(k)
      val newArms = arms.mapConserve: arm =>
        val newBody = arm._2.flattened
        if newBody is arm._2 then arm else (arm._1, newBody)
      val newDflt = dflt.mapConserve(_.flattened)
      if (newRest is rest) && (newArms is arms) && (newDflt is dflt)
      then this
      else Match(scrut, newArms, newDflt, newRest)
      
    case Label(label, loop, body, rest) =>
      val newBody = body.flattened
      val newRest = rest.flatten(k)
      if (newBody is body) && (newRest is rest)
      then this
      else Label(label, loop, newBody, newRest)
      
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
      
    case a @ AssignField(lhs, nme, rhs, rest) =>
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
          else d.copy(body = newBody)(configOverride = d.configOverride, annotations = d.annotations)
        case v: ValDefn => v
        case c: ClsLikeDefn =>
          val newPreCtor = c.preCtor.flattened
          val newCtor = c.ctor.flattened
          def flattenMethods(ms: List[FunDefn]) = ms.mapConserve:
            case f@FunDefn(owner, sym, dSym, params, body) =>
              val newBody = body.flattened
              if newBody is body then f else f.copy(body = newBody)(configOverride = f.configOverride, annotations = f.annotations)
          val newMethods = flattenMethods(c.methods)
          val newCompanion = c.companion.mapConserve: c =>
            val newCtor = c.ctor.flattened
            val newMethods = flattenMethods(c.methods)
            if (newCtor is c.ctor) && (newMethods is c.methods) then c
              else c.copy(ctor = newCtor, methods = newMethods)
          if (newPreCtor is c.preCtor)
          && (newCtor is c.ctor)
          && (newMethods is c.methods)
          && (newCompanion is c.companion)
          then c
          else c.copy(
            preCtor = newPreCtor,
            ctor = newCtor,
            methods = newMethods,
            companion = newCompanion,
          )(c.configOverride, c.annotations)
      
      val newRest = rest.flatten(k)
      if (newDefn is defn) && (newRest is rest)
      then this
      else Define(newDefn, newRest)
    
    case Scoped(syms, body) =>
      val newBody = body.flatten(k)
      if newBody is body
      then this
      else Scoped(syms, newBody)

    case e: End => k(e)
    case t: BlockTail => this
  
end Block

sealed abstract class BlockTail extends Block

sealed abstract trait NonBlockTail:
  val rest: Block

case class Match(
  scrut: Path,
  arms: Ls[Case -> Block],
  dflt: Opt[Block],
  rest: Block,
) extends Block with ProductWithTail with NonBlockTail

case class Return(res: Result) extends BlockTail

case class Throw(exc: Result) extends BlockTail

case class Label(label: LabelSymbol, loop: Bool, body: Block, rest: Block)
extends Block with NonBlockTail with ProductWithTail

case class Break(label: LabelSymbol) extends BlockTail
case class Continue(label: LabelSymbol) extends BlockTail


case class Scoped(syms: collection.Set[ScopedSymbol], body: Block)
extends Block with NonBlockTail:
  val rest = body

// TODO: remove this form?
case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail with NonBlockTail

case class TryBlock(sub: Block, finallyDo: Block, rest: Block) extends Block with ProductWithTail with NonBlockTail

case class Assign(lhs: Assignable, rhs: Result, rest: Block) extends Block with ProductWithTail with NonBlockTail

case class AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block)(val symbol: Opt[MemberSymbol])
  extends Block with ProductWithTail with NonBlockTail

case class AssignDynField(lhs: Path, fld: Path, arrayIdx: Bool, rhs: Result, rest: Block)
  extends Block with ProductWithTail with NonBlockTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail with NonBlockTail:
  defn.defnSym.foreach: ds =>
    ds.irDefn = S(defn)

inline def whenValidatingIR(inline code: => Unit): Unit =
  () // code // * uncomment to run on-the fly IR validations
  
object Label:
  def apply(label: LabelSymbol, loop: Bool, body: Block, rest: Block): Block = body match
    case _: Unreachable => body
    case _ =>
      rest match
      case Scoped(syms, rest) => Scoped(syms, Label(label, loop, body, rest))
      case _ => new Label(label, loop, body, rest)
object Scoped:
  def apply(syms: collection.Set[ScopedSymbol], body: Block): Block = body match
    case _: Unreachable => body
    case _ if syms.isEmpty => body
    case Scoped(syms2, body) =>
      whenValidatingIR:
        assert(!syms2.exists(syms.contains), "overlapping symbols in nested Scoped")
      Scoped(syms ++ syms2, body)
    case _ =>
      new Scoped(syms, body)
object TryBlock:
  def apply(body: Block, finallyDo: Block, rest: Block): Block =
    body match
    case _: Unreachable => body
    case _ =>
      rest match
      case Scoped(syms, innerRest) => Scoped(syms, TryBlock(body, finallyDo, innerRest))
      case _ => new TryBlock(body, finallyDo, rest)
object Assign:
  def apply(lhs: Assignable, rhs: Result, rest: Block): Block = rest match
    case _: Unreachable =>
      if rhs.isPure then rest else new Assign(lhs, rhs, rest)
    case Scoped(syms, body) => Scoped(syms, Assign(lhs, rhs, body))
    case _ =>
      lhs match
      case NoSymbol =>
        if rhs.isPure then rest else new Assign(lhs, rhs, rest)
      case _ => new Assign(lhs, rhs, rest)
  def discard(res: Result, rest: Block)(using State): Block =
    res match
    case _: Value | _: Lambda => rest
    case p: Path if p.isPure => rest
    case r => Assign(NoSymbol, r, rest)
object AssignField:
  def apply(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block)(symbol: Opt[MemberSymbol]): Block = rest match
    case Scoped(syms, body) => Scoped(syms, AssignField(lhs, nme, rhs, body)(symbol))
    case _ => new AssignField(lhs, nme, rhs, rest)(symbol)
object AssignDynField:
  def apply(lhs: Path, fld: Path, arrayIdx: Bool, rhs: Result, rest: Block): Block = rest match
    case Scoped(syms, body) => Scoped(syms, AssignDynField(lhs, fld, arrayIdx, rhs, body))
    case _ => new AssignDynField(lhs, fld, arrayIdx, rhs, rest)
object Define:
  def apply(defn: Defn, rest: Block): Block = rest match
    case Scoped(syms, body) => Scoped(syms, Define(defn, body))
    case _ => new Define(defn, rest)

object Match:
  def apply(scrut: Path, _arms: Ls[Case -> Block], _dflt: Opt[Block], rest: Block): Block =
    val emptyDflt = _dflt.forall(_.isEmpty)
    val dflt = if emptyDflt then N else _dflt
    val arms = if emptyDflt then _arms.filterNot(_._2.isEmpty) else _arms
    if arms.isEmpty && scrut.isPure then dflt.fold(rest)(Begin(_, rest))
    else dflt match
    case S(Unreachable(_)) if scrut.isPure && arms.sizeCompare(1) === 0 =>
      Begin(arms.head._2, rest)
    case S(Match(`scrut`, arms2, dflt2, _: End)) => // TODO: also handle non-End rest (may require a join point)
      // * Currently, this branch does not seem used often (or at all?),
      // * because the UCS and (especially) MergeMatchArmTransformer already do a good job at merging matches
      Match(scrut, arms ::: arms2, dflt2, rest)
    case _ =>
      val numNonAbortive = arms.count(!_._2.isAbortive)
      def mapDflt = dflt match
        case S(d) => S(if d.isAbortive then d else Begin(d, rest))
        case N => S(rest)
      if numNonAbortive === 0 then
        if rest.isEmpty then new Match(scrut, arms, mapDflt, rest)
        else new Match(scrut, arms, mapDflt, End("(Unreachable:) rest of abortive match"))
      else if numNonAbortive === 1 && dflt.exists(_.isAbortive) || rest.size <= 1 then
        new Match(scrut,
          arms.map: a =>
            if a._2.isAbortive then a else (a._1, Begin(a._2, rest)),
          mapDflt,
          // * We used to produce an `Unreachable` here, but that got in the way of the useless-break optimization;
          // * Indeed, `L: { match scrut { C => break L }; end }` can no longer be optimized
          // * if we replace `end` with `unreachable`, since the break is no longer jumping over nothing,
          // * ie no longer in tail position of the label (trying to treat it as such is unsound).
          End("Rest moved to non-abortive branch(es)"))
      else rest match
        case Scoped(syms, body) => Scoped(syms, Match(scrut, arms, dflt, body))
        case _ => new Match(scrut, arms, dflt, rest)

object Begin:
  def apply(sub: Block, rest: Block): Block =
    if sub.isEmpty then rest
    else if rest.isEmpty then sub
    else if sub.isAbortive then sub
    else sub match
      case Scoped(symsSub, bodySub) =>
        rest match
        case Scoped(symsRest, bodyRest) =>
          whenValidatingIR:
            assert(
              !symsSub.exists(symsRest.contains),
              "overlapping symbols when trying to merge Scoped blocks")
          Scoped(symsSub ++ symsRest, Begin(bodySub, bodyRest))
        case _ => Scoped(symsSub, Begin(bodySub, rest))
      case Match(scrut, arms, dflt, rst) => Match(scrut, arms, dflt, Begin(rst, rest))
      case Label(lbl, loop, body, rst) => Label(lbl, loop, body, Begin(rst, rest))
      case TryBlock(sub, fin, rst) => TryBlock(sub, fin, Begin(rst, rest))
      case Assign(lhs, rhs, rst) => Assign(lhs, rhs, Begin(rst, rest))
      case Define(defn, rst) => Define(defn, Begin(rst, rest))
      case _: End => rest
      case Begin(sub, rst) => Begin(sub, Begin(rst, rest))
      case _ => new Begin(sub, rest)
      // * Note: we used to match on (sub, rest) with:
      // case (_, Scoped(symsRest, bodyRest)) => Scoped(symsRest, Begin(sub, bodyRest))
      // * ^ Not a good idea: we won't want to commute Scoped past things like Match in the future


object HandleBlock:

  def suspend(tag: Path, handlerFun: Path)(using Elaborator.Ctx): Result =
    val bms = Elaborator.ctx.builtins.runtime.suspend
    Call(bms.asMemberRef(bms.asPrincipal.get), (tag.asArg :: handlerFun.asArg :: Nil) ne_:: Nil)(CallMetadata.mlsFunWithEffect)

  def handleSuspension(tag: Path, bodyFun: Path)(using Elaborator.Ctx): Result =
    val bms = Elaborator.ctx.builtins.runtime.handle_suspension
    Call(bms.asMemberRef(bms.asPrincipal.get), (tag.asArg :: bodyFun.asArg :: Nil) ne_:: Nil)(CallMetadata.mlsFunWithEffect)
  
  private def create(
      lhs: LocalVarSymbol,
      res: LocalVarSymbol,
      par: Path,
      args: Ls[Path],
      cls: ClassSymbol,
      handlers: Ls[Handler],
      body: Block,
      rest: Block
  )(using Elaborator.State, Elaborator.Ctx) =
    val sym = new BlockMemberSymbol("handleBlock$", Nil, false)

    val bodyDefn = FunDefn.withFreshSymbol(N, sym, PlainParamList(Nil) :: Nil, body)(N, annotations = Nil)
    
    val handlerMtds = handlers.map: handler =>
      val sym = BlockMemberSymbol(cls.nme + handler.sym.nme, Nil, true)
      val fDef = FunDefn.withFreshSymbol(
        N, sym, PlainParamList(Param(FldFlags.empty, handler.resumeSym, N, Modulefulness.none) :: Nil) :: Nil,
        handler.body
        )(N, annotations = Nil)
      val rSym = TempSymbol(N, "suspendRes")
      FunDefn.withFreshSymbol(
        S(cls),
        handler.sym,
        handler.params,
        Scoped(Set(sym, rSym), Define(
          fDef,
          Return(suspend(cls.asThis, sym.asMemberRef(fDef.dSym))))))(N, annotations = Nil)

    val clsDefn = ClsLikeDefn(
      N, // no owner
      cls,
      BlockMemberSymbol(cls.id.name, Nil),
      N,
      syntax.Cls,
      N, Nil,
      S(par), handlerMtds, Nil, Nil,
      // Apparently, the lifter is not happy with any assignment in the preCtor...
      Assign(State.noSymbol, Call(State.builtinOpsMap("super").asSimpleRef, args.map(_.asArg) ne_:: Nil)(CallMetadata.mlsFunWithEffect), End()),
      End(),
      N,
      N,
    )(N, Nil)

    blockBuilder
      .scopedVars(Set(clsDefn.sym, sym))
      .define(clsDefn)
      .assign(lhs, Instantiate(mut = true, clsDefn.sym.asMemberRef(cls), Nil :: Nil)(InstantiateMetadata.empty))
      .define(bodyDefn)
      .assign(res, handleSuspension(lhs.asSimpleRef, bodyDefn.sym.asMemberRef(bodyDefn.dSym)))
      .rest(rest)
  
  def apply(
      lhs: LocalVarSymbol,
      res: LocalVarSymbol,
      par: Path,
      args: Ls[Path],
      cls: ClassSymbol,
      handlers: Ls[Handler],
      body: Block,
      rest: Block
    )(using Elaborator.State, Elaborator.Ctx) =
  rest match
  case Scoped(syms, rest) =>
    Scoped(syms, create(lhs, res, par, args, cls, handlers, body, rest))
  case _ => create(lhs, res, par, args, cls, handlers, body, rest)


sealed abstract class Defn:
  val defnSym: Opt[DefinitionSymbol[?]]
  val sym: BlockMemberSymbol
  val configOverride: Opt[Config]
  val annotations: Ls[Annot]
  def isStaged: Bool = annotations.exists:
    case Annot.Modifier(Keyword.`staged`) => true
    case _ => false
  def isOwned: Bool = owner.isDefined
  def owner: Opt[InnerSymbol]
  
  def showDbg(using DebugPrinter): Str = this match
    case vd: ValDefn => s"ValDefn(${vd.sym.showDbg} = ${vd.rhs.showDbg})"
    case fd: FunDefn => s"FunDefn(${fd.sym.showDbg}(...))"
    case c: ClsLikeDefn => s"ClsLikeDefn(${c.sym.showDbg}, ...)"
  
  /** Whether this definition as a statement has any side effect (if unused). */
  def isPure: Bool = this match
    case vd: ValDefn => vd.rhs.isPure && vd.tsym.owner.isEmpty
    case fd: FunDefn => fd.owner.isEmpty
    case c: ClsLikeDefn =>
      // * Simple heuristic. TODO: check the purity of the ctor somehow? (ignore pure local field inits)
      c.companion.isEmpty
        && (!(c.k is syntax.Obj) || c.ctor.isEmpty)
  
  def subBlocks: Ls[Block] = this match
    case FunDefn(body = body) => body :: Nil
    case _: ValDefn => Nil
    case ClsLikeDefn(preCtor = preCtor, ctor = ctor, methods = mtds, companion = comp) =>
      preCtor :: ctor :: mtds.flatMap(_.subBlocks) ::: comp.toList.flatMap(_.subBlocks)
  
  // * Note that `privateFields` abd `publicFields` can't possibly be free since they are never
  // * referred to directly (they are only accessed through selections).
  lazy val freeVars: Set[FreeSymbol] = this match
    case FunDefn(own, sym, dSym, params, body) =>
      body.freeVars -- params.flatMap(_.paramSyms) ++ sym.optionIf(own.isEmpty)
    case vd @ ValDefn(tsym, sym, rhs) =>
      rhs.freeVars ++
        // * Value definitions without an owner are similar to local variables;
        // * they need to be declared with `let` in JS, which is why we add them here.
        vd.sym.optionIf(tsym.owner.isEmpty)
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, 
        methods, privateFields, publicFields, preCtor, ctor, stat, bufferable) =>
      preCtor.freeVars
        ++ ctor.freeVars ++ methods.flatMap(_.freeVars)
        -- auxParams.flatMap(_.paramSyms)
        ++ stat.iterator.flatMap(_.freeVars)
        ++ sym.optionIf(own.isEmpty)
        ++ parentSym.iterator.flatMap(_.freeVars)
  
  lazy val size: Int = this match
    case FunDefn(_, _, _, params, body) => 1 + body.size
    case ValDefn(_, _, rhs) => 1
    case ClsLikeDefn(_, _, _, _, _, paramsOpt, auxParams, parentSym, methods, privateFields, publicFields, preCtor, ctor, stat, bufferable) =>
      1 + methods.map(_.size).sum + preCtor.size + ctor.size + stat.fold(0)(_.size)
  

final case class FunDefn(
    owner: Opt[InnerSymbol],
    sym: BlockMemberSymbol,
    dSym: TermSymbol,
    params: Ls[ParamList],
    body: Block,
  )(
    val configOverride: Opt[Config],
    val annotations: Ls[Annot],
) extends Defn:
  val defnSym = S(dSym)
  val asPath = sym.asMemberRef(dSym)
  lazy val tailRec: Bool = annotations.contains(Annot.TailRec)
  lazy val inline: Bool = annotations.contains(Annot.Inline)
  lazy val noInline: Bool = annotations.contains(Annot.NoInline) || generator
  lazy val generator: Bool = annotations.contains(Annot.Generator)
  lazy val visibility: Visibility = annotations.collectFirst:
    case Annot.Modifier(Keyword.`private`) => Visibility.Private
    case Annot.Modifier(Keyword.`public`) => Visibility.Public
  .getOrElse(Visibility.Public)
  lazy val affineInfo: Ls[Int] =
    annotations.collect:
      case Annot.Affine(whichParamList) => whichParamList

  // * This deliberately is not a lazy val: its initialization would synchronize on the JVM.
  // * Computing the summary is pure, and a reference write is atomic, so concurrent traversals may
  // * harmlessly compute equal immutable summaries and overwrite this slot in either order.
  private var _inlinerBodySummary: InlinerBodySummary = null
  private[hkmc2] def inlinerBodySummary: InlinerBodySummary = _inlinerBodySummary
  private[codegen] def getOrComputeInlinerBodySummary: InlinerBodySummary =
    if _inlinerBodySummary != null then _inlinerBodySummary
    else
      val summary = InlinerBodySummary.compute(this)
      _inlinerBodySummary = summary
      summary
  
  // `configOverride` and `annotations` live in a secondary constructor list,
  // so case-class equality would otherwise ignore them.
  // We currently use structural equality in JSBackendDiffMaker.scala
  // to make sure that structurally equal blocks retain object identity.
  override def equals(obj: Any): Bool = obj match
    case that: FunDefn =>
      owner == that.owner &&
        sym == that.sym &&
        dSym == that.dSym &&
        params == that.params &&
        body == that.body &&
        configOverride == that.configOverride &&
        annotations == that.annotations
    case _ => false
  override def hashCode: Int =
    (owner, sym, dSym, params, body, configOverride, annotations).hashCode


/** Configuration-independent facts collected by one structural traversal of a function body.
  * Importing units replay these entries to rebuild their candidate graph without walking the body.
  * `transitiveCallTargets` also includes calls under lexically nested function definitions because
  * those bodies are copied when the enclosing function is inlined.
  */
private[codegen] final case class InlinerBodySummary(
  entries: Ls[InlinerBodySummary.Entry],
  transitiveCallTargets: Set[TermSymbol],
)

private[codegen] object InlinerBodySummary:
  enum Entry:
    /** A direct call found in the summarized body.
      *
      * `hasCallGraphSource` is false for calls in nested constructor bodies: those calls can expose
      * more inline candidates, but constructors are not function vertices and add no graph edge.
      */
    case DirectCall(callee: TermSymbol, call: Call, hasCallGraphSource: Bool)
    /** A nested function definition, replayed through the importing unit's eligibility checks. */
    case NestedFunction(defn: FunDefn, isMethod: Bool)

  /** Computes the summary independently from the inliner analysis that will consume it.
    * Nested function bodies get their own summaries when they are analyzed, so this traversal only
    * records their definitions and does not enter them.
    */
  def compute(fun: FunDefn): InlinerBodySummary =
    val entries = Buffer.empty[Entry]
    var transitiveCallTargets = Set.empty[TermSymbol]

    (new BlockTraverser:
      var hasCallGraphSource = true

      def withoutCallGraphSource(thunk: => Unit): Unit =
        val previous = hasCallGraphSource
        hasCallGraphSource = false
        try thunk
        finally hasCallGraphSource = previous

      def recordFunction(fun: FunDefn, isMethod: Bool): Unit =
        entries += Entry.NestedFunction(fun, isMethod)
        transitiveCallTargets ++= fun.getOrComputeInlinerBodySummary.transitiveCallTargets

      override def applyDefn(defn: Defn): Unit = defn match
        case fun: FunDefn =>
          recordFunction(fun, false)
        case cls: ClsLikeDefn =>
          cls.parentPath.foreach(applyPath)
          cls.methods.foreach(recordFunction(_, true))
          withoutCallGraphSource:
            applySubBlock(cls.preCtor)
            applySubBlock(cls.ctor)
          cls.companion.foreach: module =>
            module.methods.foreach(recordFunction(_, true))
            // The module constructor is run with the enclosing constructor and therefore inherits
            // whether its surrounding block has a call-graph source.
            applySubBlock(module.ctor)
        case _ => super.applyDefn(defn)

      override def applyResult(result: Result): Unit = result match
        case call @ Call(TermSymbolPath(callee), argss) =>
          entries += Entry.DirectCall(callee, call, hasCallGraphSource)
          if hasCallGraphSource then transitiveCallTargets += callee
          argss.foreach(_.foreach(applyArg))
        case _ => super.applyResult(result)
    ).applyBlock(fun.body)

    InlinerBodySummary(entries.toList, transitiveCallTargets)

object FunDefn:
  def withFreshSymbol(owner: Opt[InnerSymbol], sym: BlockMemberSymbol, params: Ls[ParamList], body: Block)(configOverride: Opt[Config], annotations: Ls[Annot])(using State) =
    val tSym = TermSymbol(syntax.Fun, owner, Tree.Ident(sym.nme))
    sym.tsym = S(tSym)
    FunDefn(owner, sym, tSym, params, body)(configOverride, annotations)

final case class ValDefn(
    tsym: TermSymbol,
    sym: BlockMemberSymbol,
    rhs: Path,
)(
    val configOverride: Opt[Config],
    val annotations: Ls[Annot],
) extends Defn:
  val defnSym = S(tsym)
  val owner: Opt[InnerSymbol] = tsym.owner


object ValDefn:
  def mk(
      owner: Opt[InnerSymbol],
      k: syntax.Val,
      sym: BlockMemberSymbol,
      rhs: Path,
      configOverride: Opt[Config],
      annotations: Ls[Annot],
    )(using State)
    : ValDefn =
      ValDefn(tsym = TermSymbol(k, owner, Tree.Ident(sym.nme)), sym = sym, rhs = rhs)(configOverride, annotations)


/*
  The following explains the difference between paramsOpt, auxParams, privateFields and publicFields.
  
  paramsOpt is the main parameter list of a class, i.e. in `class A(plist0)`, `plist0` will be in paramsOpt.
  If there is no such parameter list, for example `class A`, then paramsOpt will be None.
  
  auxParams are the secondary parameter lists, and in the future, will be defined using the syntax
  
  class A with
    constructor(plist1)(plist2) = ...
  
  with the difference being that they are not printed in the class's toString function. If paramsOpt is None,
  the class won't have a `.class` field and must be instantiated using `new`. Otherwise, it can be instantiated
  using either a function call or `new A` or even `new A.class` (the latter is the recommended way when done in JS). The first parameter list will always be passed to `paramsOpt`,
  if it exists.
  
  Private and public fields are defined by the user using `let` and `val` in the class's constructor.
  Each parameter in the main parameter list **defined by the user** will automatically have an asociated
  public/private field. The field will be public if the parameter is marked `val`, i.e. class `A(val x)`, 
  and private otherwise. Fields in the main parameter list created after lowering will not automatically
  have a field created.
  
  For example:
  
  class A(privateField0, val publicField0) with
    let privateField1 = 0
    val publicField1 = 0
    
  In the codegen, private and public fields are initialized by an assignment to a member symbol and a term definition
  respectively. The symbols must match what is defined in `privateFields` and `publicFields`. 
  (An assignment to a flow symbol will be treated as a local symbol to the constructor, not a field assignment.)
*/
// * This is only supposed to be for classes, objects, and patterns;
// * a lone module is represented as an empty class with a `companion` module.
final case class ClsLikeDefn(
    owner: Opt[InnerSymbol],
    isym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol,
    sym: BlockMemberSymbol,
    ctorSym: Opt[ClassCtorSymbol],
    k: syntax.ClsLikeKind,
    paramsOpt: Opt[ParamList],
    auxParams: List[ParamList],
    parentPath: Opt[Path],
    methods: Ls[FunDefn],
    privateFields: Ls[TermSymbol],
    publicFields: Ls[BlockMemberSymbol -> TermSymbol],
    preCtor: Block,
    ctor: Block,
    companion: Opt[ClsLikeBody],
    bufferable: Option[Bool],
)(
    val configOverride: Opt[Config],
    val annotations: Ls[Annot],
) extends Defn:
  require(k isnt syntax.Mod)
  methods.foreach: m =>
    m.dSym.irDefn = S(m)
  companion.foreach: c =>
    c.methods.foreach: m =>
      m.dSym.irDefn = S(m)
  val defnSym = S(isym)


// * This is only supposed to be for companion module definitions (notably, not for `object`)
final case class ClsLikeBody(
    isym: DefinitionSymbol[? <: ModuleOrObjectDef] & InnerSymbol,
    methods: Ls[FunDefn],
    privateFields: Ls[TermSymbol],
    publicFields: Ls[BlockMemberSymbol -> TermSymbol],
    ctor: Block,
    annotations: Ls[Annot],
):
  def isStaged: Bool = annotations.exists:
    case Annot.Modifier(Keyword.`staged`) => true
    case _ => false
  def subBlocks: Ls[Block] =
    ctor :: methods.flatMap(_.subBlocks)
  lazy val freeVars: Set[FreeSymbol] =
    ctor.freeVars ++ methods.flatMap(_.freeVars)
  lazy val size = 1 + methods.map(_.size).sum + ctor.size

/*
object ClsLikeBody:
  // TODO rm `empty`? it's currently unused
  def empty(id: Tree.Ident)(using State) = ClsLikeBody(
    isym = ModuleOrObjectSymbol(Tree.DummyTypeDef(syntax.Mod), id),
    methods = Nil,
    privateFields = Nil,
    publicFields = Nil,
    ctor = End(),
  )
*/

final case class Handler(
    sym: BlockMemberSymbol,
    resumeSym: VarSymbol,
    params: Ls[ParamList],
    body: Block,
):
  lazy val freeVars: Set[FreeSymbol] = body.freeVars -- params.flatMap(_.paramSyms) - sym - resumeSym


/* Represents either unreachable code (for functions that must return a result)
 * or the end of a non-returning function or a REPL block */
case class End(msg: Str = "") extends BlockTail with ProductWithTail

case class Unreachable(cause: Str) extends BlockTail with ProductWithTail

enum Case:
  case Lit(lit: Literal)
  case Cls(cls: ClassLikeSymbol, path: Path)
  case Tup(len: Int, inf: Bool)
  /** checks field existence
    * @param safe true will omit the instanceof Object check
  */
  case Field(name: Tree.Ident, safe: Bool)
  
  def showDbg(using DebugPrinter): Str = this match
    case Lit(lit) => lit.idStr
    case Cls(cls, path) => s"Cls(${cls.showDbg}, ${path.showDbg})"
    case Tup(len, inf) => s"Tup($len, $inf)"
    case Field(name, safe) => s"Field(${name.showDbg}, $safe)"
  
  lazy val freeVars: Set[FreeSymbol] = this match
    case Lit(_) => Set.empty
    case Cls(_, path) => path.freeVars
    case Tup(_, _) => Set.empty
    case Field(_, _) => Set.empty

sealed trait TrivialResult extends Result

sealed abstract class Result extends AutoLocated:
// // * Used for debugging locations:
// sealed abstract class Result extends AutoLocated with ProductWithExtraInfo:
//   def extraInfo: Str = toLoc.toString
  
  def showDbg(using DebugPrinter): Str = this match
    case Value.SimpleRef(l) => l.showDbg
    case Value.MemberRef(l, disamb) => s"${l.showDbg}${s"‹${disamb.showDbg}›"}"
    case Value.This(sym) => s"this[${sym.showDbg}]"
    case Value.Lit(lit) => lit.idStr
    case Select(q, n) => s"Select(${q.showDbg}, ${n.showDbg})"
    case DynSelect(q, fld, arrayIdx) => s"DynSelect(${q.showDbg}, ${fld.showDbg}, $arrayIdx)"
    case Call(fun, argss) => s"Call(${fun.showDbg}, [${
      argss.map(_.map(a => a.value.showDbg).mkString("[", ", ", "]")).mkString(", ")}])"
    case Lambda(params, body) => s"Lambda(${params.showDbg}, ${body.showDbg})"
    case Record(mut, args) => s"Record($mut, [${args.map(a => s"${a.showDbg} = ${a.value.showDbg}").mkString(", ")}])"
    case Tuple(mut, elems) => s"Tuple($mut, [${elems.map(_.value.showDbg).mkString(", ")}])"
    case Instantiate(mut, cls, argss) => s"Instantiate($mut, ${cls.showDbg}, [${
      argss.map(_.map(a => a.value.showDbg).mkString("[", ", ", "]")).mkString(", ")}])"
  
  lazy val isPure: Bool = this match
    case _: Value => true
    case sel @ Select(q, n) =>
      q.isPure && sel.symbol.exists(_.isPure)
    case c @ Call(fun, ass) if c.isKnownUnsaturatedCall =>
      fun.isPure && ass.forall(_.forall(a => a.spread.isEmpty && a.value.isPure))
    case Call(Value.SimpleRef(bs: BuiltinSymbol), ass) if bs.isPure =>
      ass.forall(_.forall(_.value.isPure))
    case Record(mut, args) => args.forall(_.value.isPure)
    case Tuple(mut, elems) => elems.forall(_.value.isPure)
    // case Instantiate(mut, cls, args) => // TODO?
    case _ => false
  
  // * Note: this function is used to piece together a location;
  // * for the location to be valid, we should NOT have it include children whose location
  // * is from some different place (with a different Origin), such as the location attached to symbols.
  // * That's why for example, we're not adding the `l` of `Value.Ref` to the children list.
  protected def children: Vector[Located] = this match
    case Call(fun, argss) => fun +: argss.iterator.flatten.map(_.value).toVector
    case Instantiate(mut, cls, argss) => cls +: argss.iterator.flatten.map(_.value).toVector
    case Select(qual, name) => Vector.double(qual, name)
    case DynSelect(qual, fld, arrayIdx) => Vector.double(qual, fld)
    case Lambda(params, body) => Vector.single(params)
    case Tuple(mut, elems) => elems.iterator.map(_.value).toVector
    case Record(mut, elems) => elems.iterator.map(_.value).toVector
    case Value.SimpleRef(l) => Vector.empty
    case Value.MemberRef(bms, disamb) => Vector.empty
    case Value.This(sym) => Vector.empty
    case Value.Lit(lit) => Vector.single(lit)
  
  // TODO rm Lam from values and thus the need for this method
  def subBlocks: Ls[Block] = this match
    case Call(fun, argss) => fun.subBlocks ::: argss.flatten.flatMap(_.value.subBlocks)
    case Instantiate(mut, cls, argss) => argss.flatten.flatMap(_.value.subBlocks)
    case Select(qual, name) => qual.subBlocks
    case Lambda(params, body) => body :: Nil
    case Tuple(mut, elems) => elems.flatMap(_.value.subBlocks)
    case _ => Nil
  
  lazy val freeVars: Set[FreeSymbol] = this match
    case Call(fun, argss) => fun.freeVars ++ argss.flatten.flatMap(_.value.freeVars).toSet
    case Instantiate(mut, cls, argss) => cls.freeVars ++ argss.flatten.flatMap(_.value.freeVars).toSet
    case Select(qual, name) => qual.freeVars
    case Lambda(params, body) => body.freeVars -- params.paramSyms
    case Tuple(mut, elems) => elems.flatMap(_.value.freeVars).toSet
    case Record(mut, args) =>
      args.flatMap(arg => arg.idx.fold(Set.empty[FreeSymbol])(_.freeVars) ++ arg.value.freeVars).toSet
    case Value.SimpleRef(l) => Set.single(l)
    case Value.MemberRef(bms, disamb) => Set.single(bms)
    case Value.This(sym) => Set.empty
    case Value.Lit(lit) => Set.empty
    case DynSelect(qual, fld, arrayIdx) => qual.freeVars ++ fld.freeVars
  
  lazy val size: Int = this match
    case Call(fun, argss) => fun.size + argss.iterator.flatten.map(_.value.size).sum
    case Instantiate(mut, cls, argss) => cls.size + argss.iterator.flatten.map(_.value.size).sum
    case Select(qual, name) => qual.size
    case Lambda(params, body) => 1 + body.size
    case Tuple(mut, elems) => elems.iterator.map(_.value.size).sum
    case Record(mut, args) => args.iterator.map(arg => arg.idx.fold(0)(_.size) + arg.value.size).sum
    case _: Value.RefLike => 0
    case Value.Lit(l: Tree.StrLit) => l.value.length / 4
    case Value.Lit(lit) => 0
    case DynSelect(qual, fld, arrayIdx) => qual.size + fld.size

/* mayRaiseEffects indicates whether this call may raise effect (algebraic effect),
 * regardless of whether the check for effect is inserted or not.
 * Note that the check for effect is inserted during HandlerLowering and setting this to true
 * after handler is lowered does not have any effect on the code generation. */
case class CallMetadata(
  isMlsFun: Bool,
  mayRaiseEffects: Bool,
  annotations: Ls[Annot],
):
  lazy val explicitTailCall: Bool = annotations.contains(Annot.TailCall)

object CallMetadata:
  val defaultMlsFun = CallMetadata(true, false, Nil)
  val defaultFun = CallMetadata(false, false, Nil)
  val mlsFunWithEffect = CallMetadata(true, true, Nil)


case class Call(fun: Path, argss: NELs[Ls[Arg]])(val metadata: CallMetadata) extends Result:
  lazy val isKnownUnsaturatedCall: Bool =
    fun.targetSymbol match
    case S(ts: TermSymbol) =>
      ts.irDefn.exists:
        case fd: FunDefn => argss.lengthCompare(fd.params.length) < 0
        case _ => false
    case _ => false
  // `metadata` lives in a secondary constructor list, so case-class equality
  // would otherwise ignore annotations such as @tailcall.
  override def equals(obj: Any): Bool = obj match
    case that: Call =>
      fun == that.fun &&
        argss == that.argss &&
        metadata == that.metadata
    case _ => false
  override def hashCode: Int =
    (fun, argss, metadata).hashCode

object Call:
  
  def raw(fun: Path, argss: NELs[Ls[Arg]])(metadata: CallMetadata): Call =
    new Call(fun, argss)(metadata)
  
  def apply(fun: Path, argss: NELs[Ls[Arg]])(metadata: CallMetadata): Result =
    fun match
    case Value.SimpleRef(sym: BuiltinSymbol) =>
      argss match
      case (Arg(N, arg1: Value) :: Arg(N, arg2: Value) :: Nil) :: Nil =>
        evalBuiltin(sym, arg1, arg2)(return _)
      case (Arg(N, arg1: Value) :: Nil) :: Nil =>
        evalBuiltin(sym, arg1)(return _)
      case _ =>
    case _ =>
    raw(fun, argss)(metadata)
  
  private def literalArgValues(args: Ls[Arg]): Opt[Ls[Value]] =
    args.foldRight[Opt[Ls[Value]]](S(Nil)):
      case (Arg(N, value: Value), S(acc)) => S(value :: acc)
      case _ => N
  
  import Value.Lit
  
  private inline def evalBuiltin(sym: BuiltinSymbol, arg1: Value, arg2: Value)(inline k: Value => Unit): Unit =
    (sym.nme, arg1, arg2) match
    case ("+", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.IntLit(v1 + v2)))
    case ("+", Lit(Tree.StrLit(v1)), Lit(Tree.StrLit(v2))) => k(Lit(Tree.StrLit(v1 + v2)))
    case ("-", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.IntLit(v1 - v2)))
    case ("*", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.IntLit(v1 * v2)))
    // * For "/", should check for 0 and return a DecLit.
    case ("%", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) if v2 =/= 0 => k(Lit(Tree.IntLit(v1 % v2)))
    case ("===", Lit(l1), Lit(l2)) => k(Lit(Tree.BoolLit(l1 == l2)))
    case ("!==", Lit(l1), Lit(l2)) => k(Lit(Tree.BoolLit(l1 != l2)))
    case ("<", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.BoolLit(v1 < v2)))
    case ("<=", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.BoolLit(v1 <= v2)))
    case (">", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.BoolLit(v1 > v2)))
    case (">=", Lit(Tree.IntLit(v1)), Lit(Tree.IntLit(v2))) => k(Lit(Tree.BoolLit(v1 >= v2)))
    case ("&&", Lit(Tree.BoolLit(v1)), Lit(Tree.BoolLit(v2))) => k(Lit(Tree.BoolLit(v1 && v2)))
    case ("||", Lit(Tree.BoolLit(v1)), Lit(Tree.BoolLit(v2))) => k(Lit(Tree.BoolLit(v1 || v2)))
    case _ =>
    
  private inline def evalBuiltin(sym: BuiltinSymbol, arg1: Value)(inline k: Value => Unit): Unit =
    (sym.nme, arg1) match
    case ("+", Lit(Tree.IntLit(v1))) => k(Lit(Tree.IntLit(v1)))
    case ("-", Lit(Tree.IntLit(v1))) => k(Lit(Tree.IntLit(-v1)))
    case ("!", Lit(Tree.BoolLit(v))) => k(Lit(Tree.BoolLit(!v)))
    case _ =>
  
end Call


case class InstantiateMetadata(
  annotations: Ls[Annot],
)

object InstantiateMetadata:
  def empty: InstantiateMetadata = InstantiateMetadata(Nil)

case class Instantiate(mut: Bool, cls: Path, argss: Ls[Ls[Arg]])(val metadata: InstantiateMetadata) extends Result

case class Lambda(params: ParamList, body: Block)(val annot: Ls[Annot]) extends Result:
  lazy val affine: Bool = annot.exists(_.isInstanceOf[Annot.Affine])


case class Tuple(mut: Bool, elems: Ls[Arg]) extends Result

case class Record(mut: Bool, elems: Ls[RcdArg]) extends Result


sealed abstract class Path extends TrivialResult:
  def selN(id: Tree.Ident): Path = Select(this, id)(N)(false)
  def sel(id: Tree.Ident, sym: DefinitionSymbol[?]): Path = Select(this, id)(S(sym))(false)
  def selSN(id: Str): Path = selN(new Tree.Ident(id))
  def asArg = Arg(spread = N, this)
  def targetSymbol: Opt[DefinitionSymbol[?]] = this match
    case ref: Value.MemberRef => S(ref.disamb)
    case sel: Select => sel.symbol
    case _ => N

/**
 * @param symbol The symbol representing the definition that the selection refers to, if known.
 */
case class Select(qual: Path, name: Tree.Ident)(val symbol: Opt[DefinitionSymbol[?]])(val sanitize: Boolean) extends Path with ProductWithExtraInfo:
  def extraInfo(using DebugPrinter): Str = symbol.map(s => s"sym=${s.showAsPlain}").mkString

case class DynSelect(qual: Path, fld: Path, arrayIdx: Bool) extends Path

enum Value extends Path with ProductWithExtraInfo:
  case SimpleRef(sym: SimpleSymbol)
  /**
    * @param disamb The symbol disambiguating the definition that the reference refers to.
    */
  case MemberRef(bms: BlockMemberSymbol, disamb: DefinitionSymbol[?])
  case This(sym: InnerSymbol)
  case Lit(lit: Literal)
  
  override def extraInfo(using DebugPrinter): Str = this match
    case MemberRef(bms, disamb) => s"disamb=${disamb.showAsPlain}"
    case _ => ""

object Value:
  /** A value-level reference. */
  type RefLike = SimpleRef | MemberRef | This
  object RefLike:
    def unapply(v: Value.RefLike): S[ValueSymbol] = S(v.symbol)

  /** Value-level references that are not [[`Value.This`]]. */
  type Ref = SimpleRef | MemberRef

  extension (r: RefLike)
    def symbol: ValueSymbol = r match
      case SimpleRef(l) => l
      case MemberRef(bms, disamb) => bms
      case This(sym) => sym

  @deprecated("Use Value.SimpleRef, Value.MemberRef, or Value.This instead.")
  object Ref:
    def apply(l: ValueSymbol | NoSymbol.type, disamb: Opt[DefinitionSymbol[?]]): Value.RefLike =
      l match
        case l: SimpleSymbol => l.asSimpleRef
        case l: TermSymbol => l.asPath
        case bms: BlockMemberSymbol => bms.asMemberRef:
          disamb.getOrElse:
            lastWords(s"Cannot disambiguate overloaded member symbol ${bms.nme}: no disambiguation provided")
        case sym: InnerSymbol => sym.asThis
        case NoSymbol => lastWords("NoSymbol should not be used as a Path/Value")
    
    // * Some helper constructors that allow omitting the disambiguation symbol.
    // * If the ref itself is a DefinitionSymbol, then disambiguating it results in itself.
    def apply(l: DefinitionSymbol[?]): Value.RefLike = l match
      case l: ValueSymbol => Ref(l, S(l))
      case sym => lastWords(s"$sym (of type ${sym.getClass.getSimpleName}) cannot be converted to a Path/Value")
    // * If the ref is a symbol that does not refer to a definition, then there is no disambiguation.
    def apply(l: TempSymbol | VarSymbol | BuiltinSymbol): Value.RefLike = Ref(l, N)

    def unapply(v: Value): Opt[(ValueSymbol, Opt[DefinitionSymbol[?]])] = v match
      case SimpleRef(l) => S(l -> N)
      case MemberRef(bms, disamb) => S(bms -> S(disamb))
      case This(sym) => S(sym -> N)
      case _ => N

/** Extracts the function symbol from either form of a direct function reference: `f` or `a.f`. */
object TermSymbolPath:
  def unapply(path: Path): Opt[TermSymbol] = path match
    case Value.MemberRef(_, sym: TermSymbol) => S(sym)
    case selection: Select => selection.symbol match
      case S(sym: TermSymbol) => S(sym)
      case _ => N
    case _ => N

case class Arg(spread: Opt[SpreadKind], value: Path)

// * `IndxdArg(S(idx), value)` represents a key-value pair in a record `(idx): value`
// * `IndxdArg(N, value)` represents a spread element in a record `...value`
case class RcdArg(idx: Opt[Path], value: Path):
  def spread: Bool = idx.isEmpty
  def showDbg(using DebugPrinter): Str =
    if spread then s"...${value.showDbg}" else s"(${idx.get.showDbg}): ${value.showDbg}"

extension (k: Block => Block)
  
  def chain(other: Block => Block): Block => Block = b => k(other(b))
  def rest(b: Block): Block = k(b)
  def transform(f: (Block => Block) => (Block => Block)) = f(k)
  
  def assign(l: Assignable, r: Result) = k.chain(Assign(l, r, _))
  def assignScoped(l: LocalVarSymbol, r: Result) = k.scopedVars(Set.single(l)).assign(l, r)
  def assignFieldN(lhs: Path, nme: Tree.Ident, rhs: Result) = k.chain(AssignField(lhs, nme, rhs, _)(N))
  def break(l: LabelSymbol): Block = k.rest(Break(l))
  def continue(l: LabelSymbol): Block = k.rest(Continue(l))
  def define(defn: Defn) = k.chain(Define(defn, _))
  def end = k.rest(End())
  def ifthen(scrut: Path, cse: Case, trm: Block, els: Opt[Block] = N): Block => Block =
    k.chain(Match(scrut, cse -> trm :: Nil, els, _))
  def label(label: LabelSymbol, loop: Bool, body: Block) = k.chain(Label(label, loop, body, _))
  def ret(r: Result) = k.rest(Return(r))
  def scopedVars(s: collection.Set[ScopedSymbol]) = k.chain(Scoped(s, _))
  def staticif(b: Boolean, f: (Block => Block) => (Block => Block)) = if b then k.transform(f) else k
  def foldLeft[A](xs: Iterable[A])(f: (Block => Block, A) => Block => Block) = xs.foldLeft(k)(f)

def blockBuilder: Block => Block = identity

extension (s: SimpleSymbol)
  inline def asSimpleRef: Value.SimpleRef = Value.SimpleRef(s)

extension (bms: BlockMemberSymbol)
  inline def asMemberRef(disamb: DefinitionSymbol[?]): Value.MemberRef = Value.MemberRef(bms, disamb)

extension (sym: InnerSymbol)
  inline def asThis: Value.This = Value.This(sym)

extension (l: ValueSymbol)
  // TODO(Derppening): Inline `Value.Ref.apply` into this function once that function is removed
  @annotation.nowarn("cat=deprecation")
  def asPath: Value.RefLike =
    l match
      case tsym: TermSymbol =>
        lastWords(s"Cannot make a direct path for non-local term symbol ${tsym.nme}")
      case bms: BlockMemberSymbol =>
        bms.asPrincipal.getOrElse:
          lastWords(s"Cannot resolve overloaded member symbol ${bms.nme}: no principal disambiguation found")
        match
          case disamb =>
            Value.Ref(bms, S(disamb))
      case _ => Value.Ref(l, N)
