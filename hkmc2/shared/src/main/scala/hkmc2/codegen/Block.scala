package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree, SpreadKind, Keyword}
import semantics.*
import semantics.Term.*
import sem.Elaborator.State


case class Program(
  imports: Ls[Local -> Str],
  main: Block,
)


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
    case Return(res, implct) => s"Return(${res.showDbg}, implct = $implct)"
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
  
  lazy val isAbortive: Bool = this match
    case _: End => false
    case _: Throw | _: Break | _: Continue | _: Unreachable => true
    case ret: Return => !ret.implct
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
  
  // * Note: it seems most historical uses of `definedVars` would be better removed,
  // * now that we properly put everything in proper Scoped blocks;
  // * and `definedVars` itself should be removed.
  lazy val definedVars: Set[Local] = this match
    case _: Return | _: Throw | _: Unreachable => Set.empty
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
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, _, bod, rst) => bod.definedVars ++ rst.definedVars
    case Scoped(syms, body) => body.definedVars ++ syms
  
  lazy val size: Int = this match
    case _: Return | _: Throw | _: End | _: Break | _: Continue | _: Unreachable => 1
    case Begin(sub, rst) => sub.size + rst.size
    case Assign(_, _, rst) => 1 + rst.size
    case AssignField(_, _, _, rst) => 1 + rst.size
    case AssignDynField(_, _, _, _, rst) => 1 + rst.size
    case Match(_, arms, dflt, rst) =>
      1 + arms.map(_._2.size).sum + dflt.map(_.size).getOrElse(0) + rst.size
    case Define(_, rst) => 1 + rst.size
    case TryBlock(sub, fin, rst) => 1 + sub.size + fin.size + rst.size
    case Label(_, _, bod, rst) => 1 + bod.size + rst.size
    case Scoped(_, body) => body.size
  
  
  // TODO: make patmat use unreach
  
  def mapReturn(f: Return => Block): Block =
    new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(b: Block): Block = b match
        case ret: Return => f(ret)
        case _ => super.applyBlock(b)
    .applyBlock(this)
  
  lazy val freeVars: Set[Local] = this match
    case Match(scrut, arms, dflt, rest) =>
      scrut.freeVars ++ dflt.toList.flatMap(_.freeVars) ++ rest.freeVars
      ++ arms.flatMap:
        (pat, arm) => arm.freeVars -- pat.freeVars
    case Return(res, implct) => res.freeVars
    case Throw(exc) => exc.freeVars
    case Label(label, _, body, rest) => (body.freeVars - label) ++ rest.freeVars 
    case Break(label) => Set.single(label)
    case Continue(label) => Set.single(label)
    case Begin(sub, rest) => sub.freeVars ++ rest.freeVars
    case TryBlock(sub, finallyDo, rest) => sub.freeVars ++ finallyDo.freeVars ++ rest.freeVars
    case Assign(lhs, rhs, rest) => Set.single(lhs) ++ rhs.freeVars ++ rest.freeVars
    case AssignField(lhs, nme, rhs, rest) => lhs.freeVars ++ rhs.freeVars ++ rest.freeVars
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => lhs.freeVars ++ fld.freeVars ++ rhs.freeVars ++ rest.freeVars
    case Define(defn, rest) => defn.freeVars ++ rest.freeVars
    case Scoped(syms, body) => body.freeVars -- syms
    case End(msg) => Set.empty
    case Unreachable(msg) => Set.empty
  
  lazy val freeVarsLLIR: Set[Local] = this match
    case Match(scrut, arms, dflt, rest) =>
      scrut.freeVarsLLIR ++ dflt.toList.flatMap(_.freeVarsLLIR) ++ rest.freeVarsLLIR
      ++ arms.flatMap:
        (pat, arm) => arm.freeVarsLLIR -- pat.freeVarsLLIR
    case Return(res, implct) => res.freeVarsLLIR
    case Throw(exc) => exc.freeVarsLLIR
    case Label(label, _, body, rest) => (body.freeVarsLLIR - label) ++ rest.freeVarsLLIR 
    case Break(label) => Set.empty
    case Continue(label) => Set.empty
    case Begin(sub, rest) => sub.freeVarsLLIR ++ rest.freeVarsLLIR
    case TryBlock(sub, finallyDo, rest) => sub.freeVarsLLIR ++ finallyDo.freeVarsLLIR ++ rest.freeVarsLLIR
    case Assign(lhs, rhs, rest) => rhs.freeVarsLLIR ++ (rest.freeVarsLLIR - lhs)
    case AssignField(lhs, nme, rhs, rest) => lhs.freeVarsLLIR ++ rhs.freeVarsLLIR ++ rest.freeVarsLLIR
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => lhs.freeVarsLLIR ++ fld.freeVarsLLIR ++ rhs.freeVarsLLIR ++ rest.freeVarsLLIR
    case Define(defn, rest) => defn.freeVarsLLIR ++ (rest.freeVarsLLIR - defn.sym)
    case Scoped(syms, body) => body.freeVarsLLIR
    case End(msg) => Set.empty
    case Unreachable(msg) => Set.empty
  
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
    
    // TODO rm Lam from values and thus the need for these cases
    case Return(r, _) => r.subBlocks
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

// * `implct`: metadata indicating whether this is a JS implicit return, without the `return` keyword.
// * This is currenlty only used for the main blocks of modules and diff-test blocks;
// * for all intents and purposes, one can view an implicit return as a normal return.
// * I would remove it, but it helps print cleaner outputs for diff tests (eg, using `:sir`).
case class Return(res: Result, implct: Bool) extends BlockTail

case class Throw(exc: Result) extends BlockTail

case class Label(label: LabelSymbol, loop: Bool, body: Block, rest: Block)
extends Block with NonBlockTail with ProductWithTail

case class Break(label: LabelSymbol) extends BlockTail
case class Continue(label: LabelSymbol) extends BlockTail


case class Scoped(syms: collection.Set[Local], body: Block)
extends Block with NonBlockTail:
  val rest = body

// TODO: remove this form?
case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail with NonBlockTail

case class TryBlock(sub: Block, finallyDo: Block, rest: Block) extends Block with ProductWithTail with NonBlockTail

case class Assign(lhs: Local, rhs: Result, rest: Block) extends Block with ProductWithTail with NonBlockTail
// case class Assign(lhs: Path, rhs: Result, rest: Block) extends Block with ProductWithTail

case class AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block)(val symbol: Opt[MemberSymbol])
  extends Block with ProductWithTail with NonBlockTail

case class AssignDynField(lhs: Path, fld: Path, arrayIdx: Bool, rhs: Result, rest: Block)
  extends Block with ProductWithTail with NonBlockTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail with NonBlockTail

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
  def apply(syms: collection.Set[Local], body: Block): Block = body match
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
  def apply(lhs: Local, rhs: Result, rest: Block): Block = rest match
    case _: Unreachable =>
      if rhs.isPure then rest else new Assign(lhs, rhs, rest)
    case Scoped(syms, body) => Scoped(syms, Assign(lhs, rhs, body))
    case _ =>
      lhs match
      case _: NoSymbol =>
        if rhs.isPure then rest else new Assign(lhs, rhs, rest)
      case _ => new Assign(lhs, rhs, rest)
  def discard(res: Result, rest: Block)(using State): Block =
    res match
    case _: Value | _: Lambda => rest
    case p: Path if p.isPure => rest
    case r => Assign(State.noSymbol, r, rest)
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
    else (sub, rest) match
      case (Scoped(symsSub, bodySub), Scoped(symsRest, bodyRest)) =>
        whenValidatingIR:
          assert(
            !symsSub.exists(symsRest.contains),
            "overlapping symbols when trying to merge Scoped blocks")
        Scoped(symsSub ++ symsRest, Begin(bodySub, bodyRest))
      case (Scoped(symsSub, bodySub), _) => Scoped(symsSub, Begin(bodySub, rest))
      case (_, Scoped(symsRest, bodyRest)) => Scoped(symsRest, Begin(sub, bodyRest))
      case _ => new Begin(sub, rest)


object HandleBlock:

  def suspend(tag: Path, handlerFun: Path)(using Elaborator.Ctx): Result =
    Call(Value.Ref(Elaborator.ctx.builtins.runtime.suspend, N), (tag.asArg :: handlerFun.asArg :: Nil) ne_:: Nil)(true, true, false)

  def handleSuspension(tag: Path, bodyFun: Path)(using Elaborator.Ctx): Result =
    Call(Value.Ref(Elaborator.ctx.builtins.runtime.handle_suspension, N), (tag.asArg :: bodyFun.asArg :: Nil) ne_:: Nil)(true, true, false)
  
  private def create(
      lhs: Local,
      res: Local,
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
          Return(suspend(cls.asPath, Value.Ref(sym, S(fDef.dSym))), false))))(N, annotations = Nil)

    val clsDefn = ClsLikeDefn(
      N, // no owner
      cls,
      BlockMemberSymbol(cls.id.name, Nil),
      N,
      syntax.Cls,
      N, Nil,
      S(par), handlerMtds, Nil, Nil,
      // Apparently, the lifter is not happy with any assignment in the preCtor...
      Return(Call(Value.Ref(State.builtinOpsMap("super")), args.map(_.asArg) ne_:: Nil)(true, true, false), true),
      End(),
      N,
      N,
    )(N, Nil)

    blockBuilder
      .scopedVars(Set(clsDefn.sym, sym))
      .define(clsDefn)
      .assign(lhs, Instantiate(mut = true, Value.Ref(clsDefn.sym, S(cls)), Nil :: Nil))
      .define(bodyDefn)
      .assign(res, handleSuspension(lhs.asPath, Value.Ref(bodyDefn.sym, S(bodyDefn.dSym))))
      .rest(rest)
  
  def apply(
      lhs: Local,
      res: Local,
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
  val innerSym: Opt[MemberSymbol]
  val sym: BlockMemberSymbol
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
  // * At some point we'll want to make `Local` more specific than `Symbol` to express this
  // * in the type system.
  lazy val freeVars: Set[Local] = this match
    case FunDefn(own, sym, dSym, params, body) =>
      body.freeVars -- params.flatMap(_.paramSyms) ++ sym.optionIf(own.isEmpty)
    case ValDefn(tsym, sym, rhs) => rhs.freeVars ++ sym.optionIf(tsym.owner.isEmpty)
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, 
        methods, privateFields, publicFields, preCtor, ctor, stat, bufferable) =>
      preCtor.freeVars
        ++ ctor.freeVars ++ methods.flatMap(_.freeVars)
        -- auxParams.flatMap(_.paramSyms)
        ++ stat.iterator.flatMap(_.freeVars)
        ++ sym.optionIf(own.isEmpty)
        ++ parentSym.iterator.flatMap(_.freeVars)
  
  lazy val freeVarsLLIR: Set[Local] = this match
    case FunDefn(own, sym, dSym, params, body) => body.freeVarsLLIR -- params.flatMap(_.paramSyms) - sym
    case ValDefn(tsym, sym, rhs) => rhs.freeVarsLLIR
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, 
        methods, privateFields, publicFields, preCtor, ctor, stat, bufferable) =>
      preCtor.freeVarsLLIR
        ++ ctor.freeVarsLLIR ++ methods.flatMap(_.freeVarsLLIR) ++ stat.iterator.flatMap(_.freeVarsLLIR)
        -- auxParams.flatMap(_.paramSyms)
  

// NOTE: Setting isTailRec to false does not affect whether the function is optimized.
// It only affects whether a warning is thrown if the function is not actually tailrec.
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
  val innerSym = N
  val asPath = Value.Ref(sym, S(dSym))
  lazy val forceTailRec: Bool = annotations.contains(Annot.TailRec)
  lazy val visibility: Visibility = annotations.collectFirst:
    case Annot.Modifier(Keyword.`private`) => Visibility.Private
    case Annot.Modifier(Keyword.`public`) => Visibility.Public
  .getOrElse(Visibility.Public)
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
  val innerSym = S(tsym)
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
  val innerSym = S(isym.asMemSym)


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
  lazy val freeVars: Set[Local] =
    ctor.freeVars ++ methods.flatMap(_.freeVars)
  lazy val freeVarsLLIR: Set[Local] = ???

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
  lazy val freeVars: Set[Local] = body.freeVars -- params.flatMap(_.paramSyms) - sym - resumeSym
  lazy val freeVarsLLIR: Set[Local] = body.freeVarsLLIR -- params.flatMap(_.paramSyms) - sym - resumeSym


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
// // * Used for debugging locations:
// sealed abstract class Result extends AutoLocated with ProductWithExtraInfo:
//   def extraInfo: Str = toLoc.toString
  
  def showDbg(using DebugPrinter): Str = this match
    case Value.Ref(l, disamb) => s"${l.showAsPlain}${disamb.fold("")(s => s"‹${s.showAsPlain}›")}"
    case Value.This(sym) => s"this[${sym.showAsPlain}]"
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
    case Call(Value.Ref(bs: BuiltinSymbol, _), ass) if bs.isPure =>
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
    case Value.Ref(l, disamb) => Vector.empty
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
  
  lazy val freeVars: Set[Local] = this match
    case Call(fun, argss) => fun.freeVars ++ argss.flatten.flatMap(_.value.freeVars).toSet
    case Instantiate(mut, cls, argss) => cls.freeVars ++ argss.flatten.flatMap(_.value.freeVars).toSet
    case Select(qual, name) => qual.freeVars 
    case Lambda(params, body) => body.freeVars -- params.paramSyms
    case Tuple(mut, elems) => elems.flatMap(_.value.freeVars).toSet
    case Record(mut, args) =>
      args.flatMap(arg => arg.idx.fold(Set.empty)(_.freeVars) ++ arg.value.freeVars).toSet
    case Value.Ref(l, disamb) => Set(l)
    case Value.This(sym) => Set.empty
    case Value.Lit(lit) => Set.empty
    case DynSelect(qual, fld, arrayIdx) => qual.freeVars ++ fld.freeVars
  
  lazy val freeVarsLLIR: Set[Local] = this match
    case Call(fun, argss) => fun.freeVarsLLIR ++ argss.flatten.flatMap(_.value.freeVarsLLIR).toSet
    case Instantiate(mut, cls, argss) => cls.freeVarsLLIR ++ argss.flatten.flatMap(_.value.freeVarsLLIR).toSet
    case Select(qual, name) => qual.freeVarsLLIR 
    case Lambda(params, body) => body.freeVarsLLIR -- params.paramSyms
    case Tuple(mut, elems) => elems.flatMap(_.value.freeVarsLLIR).toSet
    case Record(mut, args) =>
      args.flatMap(arg => arg.idx.fold(Set.empty)(_.freeVarsLLIR) ++ arg.value.freeVarsLLIR).toSet
    case Value.Ref(l: (BuiltinSymbol | TopLevelSymbol | ClassSymbol | TermSymbol), disamb) => Set.empty
    case Value.Ref(l: BlockMemberSymbol, S(disamb)) => disamb.defn match
      case Some(d: ClassLikeDef) => Set.empty
      case Some(d: TermDefinition) if d.companionClass.isDefined => Set.empty
      case _ => Set(l)
    case Value.Ref(l: DefinitionSymbol[?], N) => l.defn match
      case Some(d: ClassLikeDef) => Set.empty
      case Some(d: TermDefinition) if d.companionClass.isDefined => Set.empty
      case _ => Set(l)
    case Value.Ref(l, disamb) => Set(l)
    case Value.This(sym) => Set.empty
    case Value.Lit(lit) => Set.empty
    case DynSelect(qual, fld, arrayIdx) => qual.freeVarsLLIR ++ fld.freeVarsLLIR
  
// type Local = LocalSymbol
type Local = Symbol

/* mayRaiseEffects indicates whether this call may raise effect (algebraic effect),
 * regardless of whether the check for effect is inserted or not.
 * Note that the check for effect is inserted during HandlerLowering and setting this to true
 * after handler is lowered does not have any effect on the code generation. */
case class Call(fun: Path, argss: NELs[Ls[Arg]])(val isMlsFun: Bool, val mayRaiseEffects: Bool, val explicitTailCall: Bool) extends Result

case class Instantiate(mut: Bool, cls: Path, argss: Ls[Ls[Arg]]) extends Result

case class Lambda(params: ParamList, body: Block) extends Result

case class Tuple(mut: Bool, elems: Ls[Arg]) extends Result

case class Record(mut: Bool, elems: Ls[RcdArg]) extends Result


sealed abstract class Path extends TrivialResult:
  def selN(id: Tree.Ident): Path = Select(this, id)(N)
  def sel(id: Tree.Ident, sym: DefinitionSymbol[?]): Path = Select(this, id)(S(sym))
  def selSN(id: Str): Path = selN(new Tree.Ident(id))
  def asArg = Arg(spread = N, this)
  def targetSymbol: Opt[DefinitionSymbol[?]] = this match
    case ref: Value.Ref => ref.disamb
    case sel: Select => sel.symbol
    case _ => N

/**
 * @param symbol The symbol representing the definition that the selection refers to, if known.
 */
case class Select(qual: Path, name: Tree.Ident)(val symbol: Opt[DefinitionSymbol[?]]) extends Path with ProductWithExtraInfo:
  def extraInfo(using DebugPrinter): Str = symbol.map(s => s"sym=${s.showAsPlain}").mkString

case class DynSelect(qual: Path, fld: Path, arrayIdx: Bool) extends Path

enum Value extends Path with ProductWithExtraInfo:
  /**
   * @param disamb The symbol disambiguating the definition that the reference refers to. This
   * exists if and only if l is a BlockMemberSymbol.
   */
  case Ref(l: Local, disamb: Opt[DefinitionSymbol[?]])
  case This(sym: InnerSymbol) // TODO rm – just use Ref
  case Lit(lit: Literal)
  
  override def extraInfo(using DebugPrinter): Str = this match
    case Ref(l, disamb) => disamb.map(s => s"disamb=${s.showAsPlain}").mkString
    case _ => ""

object Value:
  object Ref:
    // * Some helper constructors that allow omitting the disambiguation symbol.
    // * If the ref itself is a DefinitionSymbol, then disambiguating it results in itself.
    def apply(l: DefinitionSymbol[?]): Ref = Ref(l, S(l))
    // * If the ref is a symbol that does not refer to a definition, then there is no disambiguation.
    def apply(l: TempSymbol | VarSymbol | BuiltinSymbol): Ref = Ref(l, N)

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
  
  def assign(l: Local, r: Result) = k.chain(Assign(l, r, _))
  def assignScoped(l: Local, r: Result) = k.scopedVars(Set.single(l)).assign(l, r)
  def assignFieldN(lhs: Path, nme: Tree.Ident, rhs: Result) = k.chain(AssignField(lhs, nme, rhs, _)(N))
  def break(l: LabelSymbol): Block = k.rest(Break(l))
  def continue(l: LabelSymbol): Block = k.rest(Continue(l))
  def define(defn: Defn) = k.chain(Define(defn, _))
  def end = k.rest(End())
  def ifthen(scrut: Path, cse: Case, trm: Block, els: Opt[Block] = N): Block => Block =
    k.chain(Match(scrut, cse -> trm :: Nil, els, _))
  def label(label: LabelSymbol, loop: Bool, body: Block) = k.chain(Label(label, loop, body, _))
  def ret(r: Result) = k.rest(Return(r, false))
  def scopedVars(s: collection.Set[Local]) = k.chain(Scoped(s, _))
  def staticif(b: Boolean, f: (Block => Block) => (Block => Block)) = if b then k.transform(f) else k
  def foldLeft[A](xs: Iterable[A])(f: (Block => Block, A) => Block => Block) = xs.foldLeft(k)(f)

def blockBuilder: Block => Block = identity

extension (l: Local)
  def asPath: Path = Value.Ref(l, N)

