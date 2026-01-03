package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap}
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, ParamBind, Fun, Ins}

type ResultId = Uid[Result]
type StratVarId = Uid[StratVar]
type InstantiationId = Ls[ResultId]

class StratVarState(val uid: StratVarId, val name: Str, val generatedForDef: Opt[BlockMemberSymbol]):
  lazy val asProdStrat = ProdVar(this)
  lazy val asConsStrat = ConsVar(this)
  override def toString(): String = s"${if name.isEmpty() then "var" else name}@${uid}@$generatedForDef"
object StratVarState:
  def freshVar(nme: String)(using vuid: Uid.StratVar.State) =
    val newId = vuid.nextUid
    StratVarState(newId, nme, N)
  def freshVar(nme: String, generatedForDef: BlockMemberSymbol)(using vuid: Uid.StratVar.State) =
    val newId = vuid.nextUid
    StratVarState(newId, s"${nme}_for_${generatedForDef.nme}", S(generatedForDef))

trait StratVar(s: StratVarState):
  this: ProdVar | ConsVar =>
  def asProdStrat = s.asProdStrat
  def asConsStrat = s.asConsStrat
  def uid = s.uid

sealed abstract class ProdStrat
case class ProdVar(s: StratVarState) extends ProdStrat with StratVar(s)
case class ProdFun(params: Ls[ConsStrat], res: ProdStrat) extends ProdStrat
case object NoProd extends ProdStrat
class Ctor(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId])(
  val ctor: ClassLikeSymbol,
  val args: Ls[TermSymbol -> ProdStrat]) extends ProdStrat
// TODO: a new case class for Tuple

sealed abstract class ConsStrat
case class ConsVar(s: StratVarState) extends ConsStrat with StratVar(s)
case class ConsFun(params: Ls[ProdStrat], res: ConsStrat) extends ConsStrat
case object NoCons extends ConsStrat
class FieldSel(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId],
  val field: TermSymbol,
  val consVar: ConsVar) extends ConsStrat:
    // TODO: with this term symbol, we may not need filter
    assert:
      field.owner.forall:
        _.matches:
          case c: ClassSymbol => c.tree.clsParams.contains(field)
    // this map "filter" means that this selection occurs in match branches where the
    // keys (of type ProdVar) are known to be of the type of the ClassLikeSymbols
    // val filter = MutMap.empty[ProdVar, Ls[ClassLikeSymbol]].withDefaultValue(Nil)
    // def updateFilter(p: ProdVar, c: Ls[ClassLikeSymbol]) =
    //   filter += p -> (c ::: filter(p))

class Dtor(
  val scrutExprId: ResultId,
  val instantiationId: Opt[InstantiationId]) extends ConsStrat





/**
 * PreAnalyzer:
 * - find out what's handleable
 * - collect information about ir: the context of various ir constructs, prodvars for strategies, ...
 */
class DeforestPreAnalyzer(
  val importedInfo: ImportedInfo,
  val b: Block
)(using
  val elabState: Elaborator.State,
  val tl: TraceLogger,
  val dState: Deforest.State
) extends BlockTraverser:
  given stratVarUidState: Uid.StratVar.State = new Uid.StratVar.State
  import StratVarState.freshVar
  
  ctxTracker.inTopLvl(b):
    applyBlock(b)
  
  object res:
    val primitiveStratVar = StratVarState.freshVar("unknown")
    // this contains handleable toplevel
    // - fundefns
    // - modules' methods
    // - blocks
    // - modules' ctors
    // toplevel blocks also contain toplevel fundefns,
    // those toplevel fundefns are ignored during
    // constraints collection in toplevel blocks
    val toplvlFunAndBlkToAnalyze = MutSet.empty[FunDefn | Block]
    // the keys could possibly be one of the following kinds:
    // - BlockMemberSymbol: functions and val definitions without an owner
    // - TermSymbol: functions, let and val definition in an module (with an owner)
    // - TempSymbol: generated during codegen for intermediate results or pattern matching `$argN`
    // - VarSymbol: let bindings without an owner, function parameters, user declared pattern variables
    // TODO: more?
    // when should we add things inside? maybe after deciding the
    // subset of the program which is handleable
    // val symToProdVar = MutMap.empty[Symbol, ProdVar]
    val matchScrutToMatchBlock = MutMap.empty[ResultId, Match]
    val labelSymToLabelBlk = MutMap.empty[Symbol, Label]
    val matchScrutToCtxOfMatch = MutMap.empty[ResultId, Ls[InCtx]]
    val labelSymToCtxOfLabel = MutMap.empty[Symbol, Ls[InCtx]]
    val selToCtxOfSel = MutMap.empty[ResultId, Ls[InCtx]]
    
    def topLvlFunAndModFunSymbols =
      toplvlFunAndBlkToAnalyze.collect:
        case f: FunDefn => f.sym
    def getFullRestOfMatch(scrut: ResultId) = matchScrutToCtxOfMatch(scrut)
      .iterator
      .takeWhile:
        case _: (InCtx.Fn | InCtx.Mod | InCtx.TopLvl) => false
        case _ => true
      .collect:
        case InCtx.Lbl(l) => l.rest
        case InCtx.Mtch(m, cse) => m.rest
        case InCtx.Begn(b) => b.rest
      .foldLeft(matchScrutToMatchBlock(scrut).rest)(Begin.apply)
  
  // private object tmps:
  //   // TODO:
  //   val symToToplvlFunsOrBlocksThatReferIt = MutMap.empty[Symbol, Set[FunDefn | Block]]
  //   val symToAssignedTimes = MutMap.empty[Symbol, Int].withDefaultValue(0)
  
  enum InCtx:
    case TopLvl()
    case Mod(mod: ClsLikeBody)
    case Fn(f: FunDefn)
    case Lbl(l: Label)
    case Mtch(m: Match, cse: Opt[ClassLikeSymbol])
    case Begn(b: Begin)
    case Scped(s: Scoped)
    // non-handleable cases:
    // - TODO: mutable reassignment
    //   now we may miscompile programs containing mutable reassignment,
    //   or I can write a very conservative approximation: as long as
    //   some symbol is assigned twice in IR, that symbol is considered
    //   as being mutably reassigned and everything related to it will be non-handleable
    //   NOTE: the above method still cannot work, because we cannot track
    //   the mutable assignments of object fields
    // - while loop
    // - nested defined class/module in functions
    // - handler and other unsupported forms
    // - `this`
    // - array with spread
    // - vararg
    var handleable: Boolean = true
    
  private object ctxTracker:
    private var ctx: Ls[InCtx] = Nil
    
    def getUntilFnOrCls: Iterator[InCtx] = ctx.iterator.takeWhile:
      case _: (InCtx.Fn | InCtx.Mod) => false
      case _ => true
    def getImmediateCtxFn: Opt[FunDefn] = ctx.collectFirst:
      case f: InCtx.Fn => f.f
    def getTopLvlFn: Opt[FunDefn] = ctx.collectLast:
      case f: InCtx.Fn => f.f
    def getAllMod: Ls[InCtx.Mod] = ctx.collect:
      case c: InCtx.Mod => c
    def isToplvl = ctx.matches:
      case InCtx.TopLvl() :: Nil => true
    
    inline def inCtxOf(
      c: (FunDefn | Label | (Match, Opt[ClassLikeSymbol]) | ClsLikeBody | Begin | Scoped)
    )(inline body: => Any) =
      val newCtx = c match
        case c: ClsLikeBody => InCtx.Mod(c)
        case f: FunDefn => InCtx.Fn(f)
        case l: Label => InCtx.Lbl(l)
        case m: (Match, Opt[_]) => InCtx.Mtch(m._1, m._2)
        case b: Begin => InCtx.Begn(b)
        case s: Scoped => InCtx.Scped(s)
      
      ctx = newCtx :: ctx
      body
      ctx = ctx.tail
      
      c match
        case c: ClsLikeBody =>
          if getAllMod.isEmpty && newCtx.handleable then
            res.toplvlFunAndBlkToAnalyze.add(c.ctor)
        case f: FunDefn =>
          if getImmediateCtxFn.isEmpty && newCtx.handleable then
            res.toplvlFunAndBlkToAnalyze.add(f)
        case l: Label =>
          if newCtx.handleable then
            res.labelSymToLabelBlk.addOne(l.label -> l)
            res.labelSymToCtxOfLabel.addOne(l.label -> ctx)
        case m: (Match, Opt[_]) =>
          if newCtx.handleable then
            res.matchScrutToMatchBlock.addOne(m._1.scrut.uid -> m._1)
            res.matchScrutToCtxOfMatch.addOne(m._1.scrut.uid -> ctx)
        case b: Begin => ()
        case s: Scoped => ()
      ctx.head match
        case _: (InCtx.Fn | InCtx.Lbl | InCtx.Mtch | InCtx.Begn | InCtx.Scped) =>
          ctx.head.handleable &&= newCtx.handleable
         // do not propagate non-handleable flags up to top level and module,
         // because top level may contain handleable computations,
         // and modules may contain handleable computations in their ctors
        case _: (InCtx.TopLvl | InCtx.Mod) => ()
    
    inline def inTopLvl(toplvlBlk: Block)(inline body: => Any) =
      assert(ctx.isEmpty)
      val newCtx = InCtx.TopLvl()
      ctx = newCtx :: ctx
      body
      if newCtx.handleable then
        res.toplvlFunAndBlkToAnalyze.add(toplvlBlk)
      ctx = ctx.tail
      assert(ctx.isEmpty)
    
    def markAsNonHandleable() =
      ctx.head.handleable = false
    
  
  override def applyBlock(b: Block): Unit = b match
    case scpd@Scoped(syms, body) =>
      // val nonClsLikeSyms = syms.filter:
      //   // no need to have fusion strategy for clslikesymbols
      //   case bms: BlockMemberSymbol => bms.asClsLike.isEmpty
      //   case _ => true
      // ctxTracker.getTopLvlFn match
      //   case None => nonClsLikeSyms.foreach: s =>
      //     res.symToProdVar.updateWith(s):
      //       case N => S(freshVar(s.toString()).asProdStrat)
      //       case S(_) => lastWords(s"$s twice")
      //   case Some(forFun) => nonClsLikeSyms.foreach: s =>
      //     res.symToProdVar.updateWith(s):
      //       case N => S(freshVar(s.toString(), forFun.sym).asProdStrat)
      //       case S(_) => lastWords(s"$s twice")
      ctxTracker.inCtxOf(scpd):
        applyBlock(body)
    case m@Match(scrut, arms, dflt, rest) =>
      applyPath(scrut)
      for (cse, body) <- arms do
        val cseCls = cse match
          case Case.Cls(cls, _) => S(cls)
          case _ => N
        ctxTracker.inCtxOf(m -> cseCls):
          applyBlock(body)
      for dft <- dflt do
        ctxTracker.inCtxOf(m -> N):
          applyBlock(dft)
      applyBlock(rest)
    case Return(res, implct) => applyResult(res)
    case lbl@Label(label, false, body, rest) =>
      ctxTracker.inCtxOf(lbl):
        applyBlock(body)
      applyBlock(rest)
    case bgn@Begin(sub, rest) =>
      ctxTracker.inCtxOf(bgn):
        applyBlock(sub)
      applyBlock(rest)
    case Assign(lhs, rhs, rest) =>
      // tmps.symToAssignedTimes(lhs) += 1
      applyResult(rhs)
      applyBlock(rest)
    case Define(defn, rest) =>
      applyDefn(defn)
      applySubBlock(rest)
    case Throw(exc) => applyResult(exc)
    case Break(label) => ()
    case End(msg) => ()
    case b: (TryBlock | AssignField | AssignDynField | HandleBlock | Label | Continue) =>
      ctxTracker.markAsNonHandleable()
      super.applyBlock(b)
  
  override def applyResult(r: Result): Unit = r match
    case Call(fun, args) =>
      applyPath(fun)
      args.foreach(applyArg)
    case Instantiate(mut, cls, args) =>
      if mut then ctxTracker.markAsNonHandleable()
      applyPath(cls)
      args.foreach(applyArg)
    case l: Lambda =>
      applyLam(l)
    case Tuple(mut, elems) =>
      if mut then ctxTracker.markAsNonHandleable()
      elems.foreach(applyArg)
    case Record(_, fields) =>
      ctxTracker.markAsNonHandleable()
      fields.foreach:
        case RcdArg(idx, value) => idx.foreach(applyPath); applyPath(value)
    case p: Path => applyPath(p)
  
  // TODO:
  override def applyPath(p: Path): Unit = p match
    case DynSelect(qual, fld, arrayIdx) =>
      ctxTracker.markAsNonHandleable()
      applyPath(qual); applyPath(fld)
    case p@Select(qual, name) =>
      p.symbol match
        case S(s) if s.asTrm.isDefined =>
          val tSym = s.asTrm.get
          tSym.k match
            case (Ins | HandlerBind | MutVal) =>
              ctxTracker.markAsNonHandleable()
              super.applyPath(p)
            // TODO: update symToToplvlFunsOrBlocksThatReferIt
            case (ImmutVal | LetBind | Fun | ParamBind) => () // TODO:
        case _ =>
          ctxTracker.markAsNonHandleable()
          super.applyPath(p)
      // TODO: handle the following cases
      // - pattern matching branch field access (kind is parambind)
      // - referring to a function/class/object defined in a module
      // - others: just mark as non-handleable?
      // applyPath(qual); p.symbol.foreach(_.traverse)
    case v: Value => applyValue(v)
  
  override def applyValue(v: Value): Unit = v match
    case Value.Ref(l, disamb) => ()
    case Value.This(sym) => ctxTracker.markAsNonHandleable()
    case Value.Lit(lit) => ()
  
  override def applyFunDefn(fun: FunDefn): Unit =
    // TODO: what are the prodvars that are generated by this function?
    // generating prodvars are deferred to later steps, where we know
    // all the handleable top lvl fundefns and blocks
    // fun.owner.foreach(_.traverse)
    // fun.sym.traverse
    // fun.dSym.traverse
    // fun.params.foreach(applyParamList)
    ctxTracker.inCtxOf(fun):
      applyBlock(fun.body)
  
  override def applyDefn(defn: Defn): Unit = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case defn: ValDefn => applyValDefn(defn)
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    =>
      if ctxTracker.isToplvl then
        if locally:
          own.isDefined
          || ctorSym.isDefined
          || paramsOpt.isDefined
          || auxParams.nonEmpty
          || parentPath.isDefined
          || methods.nonEmpty
          || privateFields.nonEmpty
          || publicFields.nonEmpty
          || !preCtor.matches:
              case End("") => true
          || !ctor.matches:
            case Return(Select(q, Tree.Ident("Unit")), true) =>
              q is elabState.runtimeSymbol
        then () // only handle simple modules
        else mod.foreach(applyClsLikeBody)
      else
        ctxTracker.markAsNonHandleable()
  
  override def applyClsLikeBody(b: ClsLikeBody): Unit =
    ctxTracker.inCtxOf(b):
      // b.isym.traverse
      b.methods.foreach(applyFunDefn)
      // b.privateFields.foreach(_.traverse)
      // b.publicFields.foreach: f =>
      //   f._1.traverse; f._2.traverse
      applyBlock(b.ctor)


class DeforestConstraintsCollector(val preAnalyzer: DeforestPreAnalyzer):
  given stratVarUidState: Uid.StratVar.State = preAnalyzer.stratVarUidState
  given elabState: Elaborator.State = preAnalyzer.elabState
  given DeforestPreAnalyzer = preAnalyzer
  given dState: Deforest.State = preAnalyzer.dState
  import StratVarState.freshVar
  
  object res:
    val constraints = ???


