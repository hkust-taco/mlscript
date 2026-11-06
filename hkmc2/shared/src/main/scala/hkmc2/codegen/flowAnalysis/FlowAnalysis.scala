package hkmc2
package codegen
package flowAnalysis

import scala.jdk.CollectionConverters.MapHasAsScala
import utils.*
import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import semantics.*
import syntax.Tree
import scala.collection.mutable
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, LinkedHashSet}


object FlowAnalysis:
  object TraceScope:
    val NonAffineSyms = "flow-analysis/non-affine"
    val AccumulatorSym = "flow-analysis/accumulator"
    val Effects = "flow-analysis/effects"

  class State(using val eState: Elaborator.State):
    val resultToResultId = new java.util.IdentityHashMap[Result, ResultId].asScala
    
    /** This buffer is currently only used internally for logging (`logNonAffineSyms` and `logAccumulatorSyms`) */
    val stratVars = mutable.Buffer.empty[StratVar]

    private def resultIdName(result: Result): Str = result match
      case FunRef(fun, _) => fun.nme
      case Lambda(_, _) => "lambda"
      case Value.SimpleRef(sym) => sym.nme
      case Value.MemberRef(sym, _) => sym.nme
      case Value.This(sym) => sym.nme
      case _ => "result"
  
    extension (instId: InstantiationId)
      def mkFunName(using Elaborator.State): String =
        instId
          .map: i =>
            i.getReferredFun.get.name
          .mkString("_")
      def showInstId(using SymbolPrinter, Raise, ShowCfg): Str =
        if instId.isEmpty then "<root>" else instId.map(_.showRefSite).mkString(".")
    
    extension (resultId: ResultId)
      def getResult = resultId.result
      def getReferredSym: Symbol =
        resultId.getReferredSymOpt.getOrElse(lastWords(s"assumption failed: ${resultId.getResult} is not a SimpleRef, MemberRef, or ThisRef"))
      def getReferredSymOpt: Opt[Symbol] =
        resultId.getResult match
        case Value.SimpleRef(s) => S(s)
        case Value.MemberRef(bms, _) => S(bms)
        case Value.This(sym) => S(sym)
        case e => N
      def getReferredFun(using Elaborator.State): Option[TermSymbol] =
        resultId.getResult match
        case FunRef(f, _) => Some(f)
        case _ => None
      def showRefSite(using SymbolPrinter, Raise, ShowCfg): Str =
        summon[SymbolPrinter].printSymbol(resultId)
    
    extension (id: ConcreteFunId)
      def showConcreteFunId(using SymbolPrinter, Raise, ShowCfg): Str =
        val funStr = id.exprId match
          case (funSym: TermSymbol, whichParamList) => s"${summon[SymbolPrinter].printSymbol(funSym)}#$whichParamList"
          case lamId: ResultId => lamId.showRefSite
        s"$funStr @ ${id.instId.showInstId}"
    
    extension (r: Result)
      def uid = resultToResultId.get(r) match
        case None =>
          val id = ResultId(r, resultIdName(r))
          resultToResultId(r) = id
          id
        case Some(id) => id
  
  
  def apply(
    pgrm: Program,
    mono: Bool,
    nonAffineTracking: Bool,
    accumulatorTracking: Bool,
    logEffects: Bool,
  )(using Config, TraceLogger, Elaborator.State, Raise, SymbolPrinter) =
    given State = new State
    val pre = new FlowPreAnalyzer(pgrm)
    val collector = new FlowConstraintsCollector(
      pre,
      mono,
      nonAffineTracking,
      accumulatorTracking,
    )
    val solver = new FlowConstraintSolver(collector)(collector.globalScope)
    solver.solve()
    solver.log()
    if config.checkInvariants then solver.assertConcrete()
    val tl = summon[TraceLogger]
    if logEffects then tl.scoped(TraceScope.Effects):
      if tl.isTracing then EffectAnalysis.logResults(solver)
    solver
  
  // * FIXME: not all symbols have irDefn; add and look up an irHeader instead
  def hasPureAnnotation(call: Call, whichArgList: Int): Bool = call.fun match
    case Value.SimpleRef(b: BuiltinSymbol) => whichArgList == 0 && b.isPure
    case p => p.targetSymbol.exists:
      case s: TermSymbol => s.irFunDefn match
        case S(fun) => whichArgList < fun.params.size && fun.annotations.exists(_.isInstanceOf[Annot.Pure])
        case N => s.defn.exists: fun =>
          whichArgList < fun.params.size && fun.annotations.exists(_.isInstanceOf[Annot.Pure])
      case _ => false

  def mkTraceLogger(
    cfg: Config.FlowAnalysisConfig,
    prefix: Str,
    sink: DebugSink,
  )(using printer: DebugPrinter): TraceLogger =
    val debug = new DebugContext:
      override protected def forceUids: Bool = printer.showUids
    new TraceLogger(debug, sink, indentWhenDisabled = true, prefix = prefix):
      protected def phaseEnabled(config: Config.Debug): Bool = false
      protected def forceTrace(scope: Opt[Str]): Bool = scope match
        case S(TraceScope.NonAffineSyms) => cfg.logNonAffine
        case S(TraceScope.AccumulatorSym) => cfg.logAccumulator
        case S(TraceScope.Effects) => cfg.logEffects
        case _ => cfg.debug
    
end FlowAnalysis


class ResultId(val result: Result, name: Str)(using eState: Elaborator.State) extends Symbol(using eState):
  def nme: Str = name
  def subst(using SymbolSubst): ResultId = this
  def toLoc: Opt[Loc] = result.toLoc

type InstantiationId = Ls[ResultId]
type CtorCls = ClassLikeSymbol | Int
type SelField = TermSymbol | Int
type FunId = (funSym: TermSymbol, whichParamList: Int) | ResultId
type CallId = (exprId: ResultId, whichArgList: Int)
type OriginId = ResultId | FunId | CallId
type ConcreteFunId = ConcreteId[FunId]


object TrackableFieldSelect:
  def unapply(s: Select): Opt[Path -> (field: TermSymbol, owner: ClassSymbol)] =
    s.symbol match
    case S(sSym) if sSym.asTrm.exists(_.decl.exists(_.isInstanceOf[Param])) =>
      val tSym = sSym.asTrm.get
      for
        owner <- tSym.owner
        cls <- owner.asCls
        if cls.tree.clsParams.size === 1
        // The fields of external classes are not initialized from constructor arguments
        // visible in the IR. For instance, `Array`'s `length` field is also read on tuples,
        // which are not constructed as `Array` instances.
        if !cls.defn.exists(Inheritance.isExternal)
      yield s.qual -> (tSym, cls)
    case _ => N

object PossibleTrackableTupleSelect:
  def unapply(s: Result)(using eState: Elaborator.State): Opt[Value.SimpleRef -> Int] =
    s match
    case Call(
      p,
      (Arg(N, ref@Value.SimpleRef(scrut)) :: Arg(N, Value.Lit(Tree.IntLit(n))) :: Nil) :: Nil
    ) if p.targetSymbol.contains(eState.tupleGetSymbol) => S(ref -> n.toInt)
    case _ => N

object TrackableSelect:
  def unapply(s: Result)(using pre: FlowPreAnalyzer, eState: Elaborator.State): Opt[(from: Path, field: SelField, owner: CtorCls)] =
    given fState: FlowAnalysis.State = pre.fState
    s match
    case sel@PossibleTrackableTupleSelect((ref@Value.SimpleRef(scrut)) -> ith) =>
      pre.res.getEnclosingMatchesForSel(sel.uid).find(_._1.getReferredSymOpt.contains(scrut)).flatMap:
        case (_, Some(tupSize: Int)) => S(ref, ith, tupSize)
        case _ => N
    case TrackableFieldSelect(qual, field -> owner) =>
      Some((qual, field, owner))
    case _ => N

object MemberRefTo:
  def unapply(p: Path): Opt[(targetSymbol: DefinitionSymbol[?], selectedFrom: Opt[Path])] =
    p.targetSymbol.map: target =>
      target -> p.match
        case Select(qual, _) => S(qual)
        case DynSelect(qual, _, DynSelectKind.Member(_)) => S(qual)
        case SuperSelect(qual, _, _) => S(qual)
        case _ => N

object CtorProducer:
  /** Extracts result forms that produce a concrete `Ctor` flow strategy. */
  def unapply(r: Result)(using Elaborator.State): Opt[(ctorCls: CtorCls, args: Ls[Arg], selectedFrom: Opt[Path])] =
    r match
    case Instantiate(_, MemberRefTo(cls: ClassSymbol, qual), argss) => S(cls, argss.flatten, qual)
    case Call(MemberRefTo(cls: ClassCtorSymbol, qual), argss) => S(cls.associatedCls, argss.flatten, qual)
    case MemberRefTo(ctor: ModuleOrObjectSymbol, qual) => S(ctor, Nil, qual)
    case Tuple(_, args) => S(args.size, args, N)
    case _ => N

object FunRef:
  def unapply(s: Path)(using Elaborator.State): Option[TermSymbol -> Opt[Path]] = s match
    case MemberRefTo(tSym: TermSymbol, qual)
      if (tSym.k is syntax.Fun) && tSym.owner.forall(_.asMod.isDefined) => S(tSym -> qual)
    case _ => N


sealed trait Strat

sealed trait ProdStrat extends Strat
sealed trait ConsStrat extends Strat

type Constraint = ProdStrat -> ConsStrat

/** [[BottomEffect]] represents that an effect variable is known to be the
 * bottom type (no effect). This avoids allocating [[StratVar]]. */
case object BottomEffect

/** [[EffectVar]] represents an effect variable for some entities. 
 * 
 *  An [[EffectVar]]'s LB can only be [[UnsafeEta]].
 */
type EffectVar = StratVar | BottomEffect.type

extension (effect: EffectVar)
  inline def fold[A](ifBot: => A)(f: StratVar => A): A = effect match
    case BottomEffect => ifBot
    case variable: StratVar => f(variable)

  inline def map(f: StratVar => StratVar): EffectVar =
    effect.fold[EffectVar](BottomEffect)(f)

  inline def foreach(f: StratVar => Unit): Unit =
    effect.fold(())(f)

class StratVar(val name: Str, val sourceSymbol: Opt[Symbol], val generatedForFun: Opt[TermSymbol])(using eState: Elaborator.State)
  extends Symbol(using eState) with ProdStrat with ConsStrat:
  def nme: Str = name
  def subst(using SymbolSubst): StratVar = this
  def toLoc: Opt[Loc] = sourceSymbol.flatMap(_.toLoc)
  // Bounds belong to this analysis-local variable and are populated by FlowConstraintSolver.
  val upperBounds: mutable.Set[ConsStrat] = LinkedHashSet.empty
  val lowerBounds: mutable.Set[ProdStrat] = LinkedHashSet.empty
  lazy val asIntoParam = new StratVar.IntoParamImpl(this)
  lazy val asPossibleAccumulator = new StratVar.PossibleAccumulatorImpl(this)

object StratVar:
  final class IntoParamImpl private[StratVar] (val s: StratVar) extends ConsStrat:
    override def toString(): String = s"IntoParam($s)"
  final class PossibleAccumulatorImpl private[StratVar] (val s: StratVar) extends ConsStrat:
    override def toString(): String = s"PossibleAccumulator($s)"
  

  def freshVar(nme: String)(using fState: FlowAnalysis.State): StratVar =
    freshVar(nme, N, N)
  def freshVar(nme: String, generatedForFun: TermSymbol)(using fState: FlowAnalysis.State): StratVar =
    freshVar(nme, N, S(generatedForFun))
  def freshVar(nme: String, sourceSymbol: Opt[Symbol], generatedForFun: Opt[TermSymbol])(using fState: FlowAnalysis.State): StratVar =
    val ownName = if nme.isEmpty then "$stratvar" else nme
    val name = generatedForFun.fold(ownName)(fun => s"${ownName}_for_${fun.nme}")
    val stratVar = StratVar(name, sourceSymbol, generatedForFun)(using fState.eState)
    fState.stratVars += stratVar
    stratVar
  def freshVar(nme: String, forFunOpt: Opt[TermSymbol])(using fState: FlowAnalysis.State): StratVar =
    forFunOpt match
    case None => freshVar(nme)
    case Some(forFun) => freshVar(nme, forFun)

type IntoParam = StratVar.IntoParamImpl
type PossibleAccumulator = StratVar.PossibleAccumulatorImpl

sealed trait StratWithOrigin[A <: OriginId]:
  def exprId: A
  def instantiationId: Opt[InstantiationId]
  def concreteId: ConcreteId[A] = ConcreteId(exprId, instantiationId.get)

// strategies for constraint endpoints that do not represent real producer/consumer
// but mark some properties (unknown, non-affine, etc.) of the corresponding upper/lower bounds.
sealed trait MarkerProdStrat extends ProdStrat
sealed trait MarkerConsStrat extends ConsStrat

sealed trait ConcreteCtorConsumer extends ConsStrat with StratWithOrigin[ResultId]:
  val srcs: mutable.Set[Ctor | MarkerProdStrat] = MutSet.empty

class ProdFun(
  val exprId: FunId,
  val instantiationId: Opt[InstantiationId]
)(
  val params: Ls[ConsStrat],
  /** The number of leading `params` that are not optional (see `LoweredParamList.paramCountLB`). */
  val requiredParamCount: Int,
  val restParam: Opt[ConsStrat],
  val res: ProdStrat,
  val capturedVarUpperbound: StratVar,
  val effect: EffectVar,
) extends ProdStrat with StratWithOrigin[FunId]:
  def paramInfo: (Int, Int, Bool) = (params.size, requiredParamCount, restParam.isDefined)
  val dests: mutable.Set[ConsFun | MarkerConsStrat] = MutSet.empty
  override def toString(): String =
    s"(${params.map(_.toString()).mkString(", ")}) -> ${res.toString()}"

case object UnknownProd extends MarkerProdStrat

/** A coarse effect marker indicating that the variable is unsafe for eta-epansion. */
case object UnsafeEta extends MarkerProdStrat

class Ctor(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val ctor: CtorCls,
  val args: Ls[SelField -> ProdStrat]
) extends ProdStrat with StratWithOrigin[ResultId]:
  val dests: mutable.Set[ConcreteCtorConsumer | MarkerConsStrat] = MutSet.empty
  override def toString(): String =
    s"$ctor(${args.map(_.toString()).mkString(", ")})"


class ConsFun(
  val exprId: CallId,
  val instantiationId: Opt[InstantiationId],
)(
  val params: Ls[ProdStrat],
  val res: ConsStrat,
  val effect: EffectVar,
) extends ConsStrat with StratWithOrigin[CallId]:
  val srcs: mutable.Set[ProdFun | MarkerProdStrat] = MutSet.empty
  override def toString(): String =
    s"(${params.map(_.toString()).mkString(", ")}) -> ${res.toString()}"

case object UnknownCons extends MarkerConsStrat

case object NonAffine extends MarkerConsStrat

case object Accumulator extends MarkerConsStrat

class FieldSel(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val field: SelField,
  val selectsFrom: CtorCls,
  val consVar: StratVar
) extends ConsStrat with ConcreteCtorConsumer

class Dtor(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
) extends ConsStrat with ConcreteCtorConsumer

case class ConcreteId[A <: OriginId](exprId: A, instId: InstantiationId):
  def pp(using FlowAnalysis.State): Str = exprId match
    case (sym: TermSymbol, idx: Int) => s"${sym.nme}#$idx"
    case (r: ResultId, idx: Int) => s"${r.getResult}#$idx"
    case r: ResultId => s"${r.getResult}"


/** A solved strategy graph rooted at a strategy variable, reusable through
 *  polymorphic instantiation (see `Instantiator`).
 * 
 *  In practice, this is for instantiating a function producer ([[ProdFun]]),
 *  corresponding to function's polymorphic splitting. But [[StratScheme]]
 *  itself is general enough to represent a scheme for arbitrary strategies.
 *  
 *  Whenever in the scheme there is an (reference to an) external strategy
 *  variable that is not part of the scheme (e.g., a captured variable), the
 *  collector creates a proxy of that external strategy variable and uses it in
 *  place of the external strategy variable in [[strategies]] and the mapping is
 *  in [[environment]]. During instantiation, the collector replaces the proxy
 *  with the strategy variable for the current scope in appropriate bounds of
 *  the instantiated variables.
 * 
 *  @param s The "root" strategy variable that instantiation instantiates and
 *    returns.
 *  @param strategies The (solved) strategies, containing strategy variables,
 *    producers, or consumers, that need to be duplicated on instantiation.
 *  @param environment A list of environment entries (external strategy variable
 *    -> internal strategy variable).
 */
class StratScheme(
  val s: StratVar,
  val strategies: Ls[Strat],
  val environment: Ls[StratVar -> StratVar],
)

class FlowPreAnalyzer(val pgrm: Program)(using
  val tl: TraceLogger,
  val eState: Elaborator.State,
  val fState: FlowAnalysis.State,
  val raise: Raise,
  val symbolPrinter: SymbolPrinter
) extends BlockTraverser:
  import StratVar.freshVar
  val traceSymbolPrinter = SymbolPrinter(symbolPrinter.dbgScp.nest)
  
  // Records the local definitions and captured variables of the current
  // nested function/lambda.
  // This tracking of captured variables is needed for propagating non-affine
  // information through ProdFuns.
  private case class CaptureTrackingInfo(
    locallyDefined: MutSet[Symbol],
    captured: LinkedHashSet[Symbol]
  )
  private var currentCaptureInfo: Opt[CaptureTrackingInfo] = N
  private var currentAffinityCount = res.affinityCounts
  
  
  ctxTracker.inTopLvl:
    applyBlock(pgrm.main)
  
  object res:
    val primitiveStratVar = StratVar.freshVar("unknown")
    val rootFunDefns = LinkedHashMap.empty[TermSymbol, FunDefn]
    val rootValDefns = LinkedHashMap.empty[TermSymbol, ValDefn]
    val funSymToFunDefn = MutMap.empty[TermSymbol, FunDefn]
    val matchScrutToMatchBlock = MutMap.empty[ResultId, Match]
    val labelSymToLabelBlk = MutMap.empty[Symbol, Label]
    val matchScrutToCtxOfMatch = MutMap.empty[ResultId, Ls[InCtx]]
    val labelSymToCtxOfLabel = MutMap.empty[Symbol, Ls[InCtx]]
    val selToCtxOfSel = MutMap.empty[ResultId, Ls[InCtx]]
    val modSymToBms = MutMap.empty[Symbol, BlockMemberSymbol]
    val generatedVars = LinkedHashMap.empty[Symbol, StratVar] // TODO: tighten `Symbol` type!
    val generatedEffects = LinkedHashMap.empty[Symbol, EffectVar] // TODO: tighten `Symbol` type! // TODO: populate for getters!
    val capturedVars = LinkedHashMap.empty[FunId, LinkedHashSet[Symbol]]
    val affinityCounts = MutMap.empty[Symbol, Int].withDefaultValue(0)
    def getEnclosingMatchesForSel(selExprId: ResultId) =
      selToCtxOfSel.get(selExprId).fold(Iterator.empty):
        _.iterator
        .collect:
          case InCtx.MtchBody(m, cse) => m.scrut.uid -> cse
    lazy val nonAffineSyms: Set[Symbol] = affinityCounts
      .iterator
      .collect:
        case (sym, n) if n > 1 => sym
      .filterNot:
        case ts: TermSymbol => rootFunDefns.contains(ts)
        case _ => false
      .toSet

  end res
  
  enum InCtx:
    case TopLvl()
    case Mod(mod: ClsLikeBody)
    case ModCtor(mod: ClsLikeBody)
    case Cls(cls: ClsLikeDefn)
    case ClsPreCtor(cls: ClsLikeDefn)
    case ClsCtor(cls: ClsLikeDefn)
    case Fn(f: FunDefn)
    case Lam(lam: Lambda)
    case LblBody(l: Label)
    case MtchBody(m: Match, cse: Opt[CtorCls])
    case BegnBody(b: Begin)
    case Scped(s: Scoped)
  
  private object ctxTracker:
    private var ctx: Ls[InCtx] = Nil
    private def isTopLvlLikeFunCtx(ctx0: Ls[InCtx]): Boolean =
      ctx0.forall:
        case InCtx.TopLvl() => true
        case InCtx.Mod(_) => true
        case InCtx.ModCtor(_) => true
        case InCtx.BegnBody(_) => true
        case InCtx.Scped(_) => true
        case _ => false
  
    def getAllCtx = ctx
    def isTopLvlLikeModuleCtx: Boolean =
      ctx.forall:
        case InCtx.TopLvl() => true
        case InCtx.BegnBody(_) => true
        case InCtx.Scped(_) => true
        case _ => false
    def registerStratVar(sym: Symbol, nme: String): Unit =
      val currentRootFun = ctx.tails.collectFirst:
        case InCtx.Fn(fun) :: tl if isTopLvlLikeFunCtx(tl) => fun.dSym
      res.generatedVars.getOrElseUpdate(sym, freshVar(nme, S(sym), currentRootFun))
    
    private inline def withCtx(newCtx: InCtx)(inline body: => Any)(after: => Unit = ()): Unit =
      ctx = newCtx :: ctx
      body
      ctx = ctx.tail
      after
    
    inline def inMod(mod: ClsLikeBody)(inline body: => Any) =
      withCtx(InCtx.Mod(mod))(body)()
    
    inline def inFun(fun: FunDefn)(inline body: => Any) =
      // each param list is a closure over the params of the lists before it
      def withParamListCaptureInfo(paramLists: Iterator[(LoweredParamList, Int)]): Unit = paramLists.nextOption() match
        case N => body
        case S((pl, whichParamList)) =>
          val locallyDefined = MutSet.from[Symbol](pl.paramSyms)
          locallyDefined += fun.sym
          locallyDefined += fun.dSym
          withCaptureInfo((fun.dSym, whichParamList), locallyDefined):
            withParamListCaptureInfo(paramLists)
      withCtx(InCtx.Fn(fun))(withParamListCaptureInfo(fun.params.iterator.zipWithIndex)):
        res.funSymToFunDefn(fun.dSym) = fun
        if isTopLvlLikeFunCtx(ctx) then
          res.rootFunDefns.addOne(fun.dSym -> fun)
    
    inline def inLabelBody(label: Label)(inline body: => Any) =
      withCtx(InCtx.LblBody(label))(body):
        res.labelSymToLabelBlk.addOne(label.label -> label)
        res.labelSymToCtxOfLabel.addOne(label.label -> ctx)
    
    inline def inMatchBody(m: Match, cse: Opt[CtorCls])(inline body: => Any): Unit =
      withCtx(InCtx.MtchBody(m, cse))(body):
        res.matchScrutToMatchBlock.addOne(m.scrut.uid -> m)
        res.matchScrutToCtxOfMatch.addOne(m.scrut.uid -> ctx)
    
    def isEnclosingMatchScrutSym(sym: Symbol): Boolean =
      ctx.exists:
        case InCtx.MtchBody(m, _) => m.scrut match
          case Value.SimpleRef(s) => s is sym
          case Value.MemberRef(bms, disamb) => disamb is sym
          case _ => false
        case _ => false
    
    inline def inBeginBody(begin: Begin)(inline body: => Any) =
      withCtx(InCtx.BegnBody(begin))(body)()
    
    inline def inScoped(scpd: Scoped)(inline body: => Any) =
      withCtx(InCtx.Scped(scpd))(body)()
    
    inline def inLam(lam: Lambda)(inline body: => Any) =
      val locallyDefined = MutSet.empty[Symbol]
      lam.params.paramSyms.foreach(locallyDefined += _)
      withCtx(InCtx.Lam(lam))(withCaptureInfo(lam.uid, locallyDefined)(body))()
    
    inline def inTopLvl(inline body: => Any) =
      assert(ctx.isEmpty)
      withCtx(InCtx.TopLvl())(body):
        assert(ctx.isEmpty)
    
    inline def inModCtor(mod: ClsLikeBody)(inline body: => Any) =
      assert(ctx.head.matches{ case _: InCtx.Mod => true })
      withCtx(InCtx.ModCtor(mod))(body):
        assert(ctx.head.matches{ case _: InCtx.Mod => true })
    
    inline def inCls(cls: ClsLikeDefn)(inline body: => Any) =
      withCtx(InCtx.Cls(cls))(body)()
    
    inline def inClsPreCtor(cls: ClsLikeDefn)(inline body: => Any) =
      withCtx(InCtx.ClsPreCtor(cls))(body)()
    
    inline def inClsCtor(cls: ClsLikeDefn)(inline body: => Any) =
      withCtx(InCtx.ClsCtor(cls))(body)()
  
  end ctxTracker
  
  private def recordAffinityUse(s: LocalVarSymbol | TermSymbol): Unit =
    s match
    case _: ClassCtorSymbol => ()
    case _ => currentAffinityCount(s) += 1
  
  private def recordRefInCaptures(l: LocalVarSymbol | TermSymbol): Unit =
    (l, currentCaptureInfo) match
    case (_: ClassCtorSymbol, _) | (_, N) => ()
    case (_, S(capInfo)) =>
      if !capInfo.locallyDefined.contains(l) then
        capInfo.captured += l

  private def withCaptureInfo(owner: FunId, locallyDefined: MutSet[Symbol])(body: => Any): Unit =
    val outerCapInfo = currentCaptureInfo
    val newCapInfo = CaptureTrackingInfo(locallyDefined, LinkedHashSet.empty)
    currentCaptureInfo = S(newCapInfo)
    body
    currentCaptureInfo = outerCapInfo
    outerCapInfo.foreach: outer =>
      outer.captured ++= newCapInfo.captured.iterator.filterNot(outer.locallyDefined.contains)
    res.capturedVars(owner) = newCapInfo.captured
  
  override def applyBlock(b: Block): Unit = b match
    case scpd@Scoped(syms, body) =>
      for s <- syms do
        s match
        case s: BlockMemberSymbol => ()
        case _ => ctxTracker.registerStratVar(s, s.nme)
      currentCaptureInfo.foreach(_.locallyDefined ++= syms)
      ctxTracker.inScoped(scpd):
        applyBlock(body)
      currentCaptureInfo.foreach(_.locallyDefined --= syms)
    case m@Match(scrut, arms, dflt, rest) =>
      applyPath(scrut)
      val outerAffinityCount = currentAffinityCount
      val mergedBranchUsage = MutMap.empty[Symbol, Int].withDefaultValue(0)
      for (cse, body) <- arms do
        val cseCls = cse match
          case Case.Cls(cls, _) => S(cls)
          case Case.Tup(n, false) => S(n)
          case _ => N
        currentAffinityCount = MutMap.empty[Symbol, Int].withDefaultValue(0)
        ctxTracker.inMatchBody(m, cseCls):
          applyBlock(body)
        for (sym, n) <- currentAffinityCount do
          mergedBranchUsage(sym) = mergedBranchUsage(sym).max(n)
        currentAffinityCount = outerAffinityCount
      for dft <- dflt do
        currentAffinityCount = MutMap.empty[Symbol, Int].withDefaultValue(0)
        ctxTracker.inMatchBody(m, N):
          applyBlock(dft)
        for (sym, n) <- currentAffinityCount do
          mergedBranchUsage(sym) = mergedBranchUsage(sym).max(n)
        currentAffinityCount = outerAffinityCount
      for (sym, n) <- mergedBranchUsage do
        currentAffinityCount(sym) = currentAffinityCount(sym) + n
      applyBlock(rest)
    case Return(res) => applyResult(res)
    case lbl@Label(label, loop, body, rest) =>
      ctxTracker.inLabelBody(lbl):
        applyBlock(body)
      applyBlock(rest)
    case bgn@Begin(sub, rest) =>
      ctxTracker.inBeginBody(bgn):
        applyBlock(sub)
      applyBlock(rest)
    case Assign(lhs, rhs, rest) =>
      lhs match
        case l: (LocalVarSymbol | TermSymbol) => recordRefInCaptures(l)
        case _ => ()
      applyResult(rhs)
      applyBlock(rest)
    case Define(defn, rest) =>
      applyDefn(defn)
      applyBlock(rest)
    case Throw(exc, _) => applyResult(exc)
    case Break(label) => ()
    case Continue(label) => ()
    case TryBlock(sub, finallyDo, rest) =>
      applyBlock(sub)
      applyBlock(finallyDo)
      applyBlock(rest)
    case AssignField(lhs, nme, rhs, rest) =>
      applyPath(lhs)
      applyResult(rhs)
      applyBlock(rest)
    case AssignDynField(lhs, fld, kind, rhs, rest) =>
      applyPath(lhs)
      applyPath(fld)
      applyResult(rhs)
      applyBlock(rest)
    case End(_) => ()
    case Unreachable(_) => ()
  
  override def applyResult(r: Result): Unit = r match
    case tupSel@PossibleTrackableTupleSelect(_, _) =>
      res.selToCtxOfSel.addOne(tupSel.uid -> ctxTracker.getAllCtx)
    case Call(fun, argss) =>
      applyPath(fun)
      argss.foreach(_.foreach(applyArg))
    case Instantiate(mut, cls, argss) =>
      applyPath(cls)
      argss.foreach(_.foreach(applyArg))
    case l: Lambda =>
      applyLam(l)
    case Tuple(mut, elems) =>
      elems.foreach(applyArg)
    case Record(_, fields) =>
      fields.foreach:
        case RcdArg(idx, value) => idx.foreach(applyPath); applyPath(value)
    case Cast(value, _, _) =>
      applyResult(value)
    case p: Path => applyPath(p)
  
  private def applyValueSimpleRef(v: Value.SimpleRef, recordAffinity: Bool) =
    v.sym match
    case s: LocalVarSymbol =>
      recordRefInCaptures(s)
      if recordAffinity then recordAffinityUse(s)
    case _ => ()

  private def applyValueMemberRef(v: Value.MemberRef, recordAffinity: Bool) =
    val Value.MemberRef(_, disamb) = v
    disamb match
    case s: TermSymbol =>
      recordRefInCaptures(s)
      if recordAffinity then recordAffinityUse(s)
    case _ => ()
  
  override def applyPath(p: Path): Unit = p match
    case p@TrackableFieldSelect(qual, _ -> _) =>
      res.selToCtxOfSel.addOne(p.uid -> ctxTracker.getAllCtx)
      qual match
      case v@Value.SimpleRef(l)
        if ctxTracker.isEnclosingMatchScrutSym(l) =>
          applyValueSimpleRef(v, recordAffinity = false)
      case v@Value.MemberRef(bms, disamb)
        if ctxTracker.isEnclosingMatchScrutSym(disamb) =>
          applyValueMemberRef(v, recordAffinity = false)
      case _ => applyPath(qual)
    case p: (Select | SuperSelect | DynSelect) =>
      super.applyPath(p)
    case c: Cast => applyResult(c.value)
    case v: Value => applyValue(v)
  
  override def applyValue(v: Value): Unit = v match
    case v@Value.SimpleRef(l) => applyValueSimpleRef(v, recordAffinity = true)
    case v@Value.MemberRef(_, _) => applyValueMemberRef(v, recordAffinity = true)
    case Value.This(sym) => ()
    case Value.Lit(lit) => ()
  
  override def applyFunDefn(fun: FunDefn): Unit =
    ctxTracker.inFun(fun):
      ctxTracker.registerStratVar(fun.dSym, fun.sym.nme)
      currentCaptureInfo.foreach(_.locallyDefined += fun.dSym)
      fun.params.foreach(applyParamList)
      applyBlock(fun.body)
  
  override def applyLam(lam: Lambda): Unit =
    ctxTracker.inLam(lam):
      applyParamList(lam.params)
      applyBlock(lam.body)
  
  override def applyValDefn(defn: ValDefn): Unit =
    ctxTracker.registerStratVar(defn.tsym, defn.tsym.nme)
    if ctxTracker.isTopLvlLikeModuleCtx then
      res.rootValDefns.addOne(defn.tsym -> defn)
    currentCaptureInfo.foreach(_.locallyDefined += defn.tsym)
    applyPath(defn.rhs)
  
  override def applyParamList(pl: LoweredParamList): Unit =
    pl.allParams.foreach(p => ctxTracker.registerStratVar(p.sym, p.sym.nme))
  
  override def applyArg(arg: Arg): Unit =
    applyPath(arg.value)
  
  override def applyDefn(defn: Defn): Unit = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case defn: ValDefn => applyValDefn(defn)
    case cls@ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable, termCompanion, _)
    =>
      cls.methodKeys.valuesIterator.foreach(applyPath)
      mod.foreach(_.methodKeys.valuesIterator.foreach(applyPath))
      ctxTracker.inCls(cls):
        paramsOpt.foreach(applyParamList)
        auxParams.foreach(applyParamList)
        privateFields.foreach(tsym => ctxTracker.registerStratVar(tsym, tsym.nme))
        publicFields.foreach: (_, tsym) =>
          ctxTracker.registerStratVar(tsym, tsym.nme)
        methods.foreach(applyFunDefn)
        ctxTracker.inClsPreCtor(cls):
          applyBlock(preCtor)
        ctxTracker.inClsCtor(cls):
          applyBlock(ctor)
      for b: ClsLikeBody <- mod do
        if ctxTracker.isTopLvlLikeModuleCtx then
          res.modSymToBms(b.isym) = sym
        ctxTracker.inMod(b):
          b.privateFields.foreach(tsym => ctxTracker.registerStratVar(tsym, tsym.nme))
          b.publicFields.foreach: (_, tsym) =>
            ctxTracker.registerStratVar(tsym, tsym.nme)
          b.methods.foreach(applyFunDefn)
          ctxTracker.inModCtor(b):
            applyBlock(b.ctor)
      
  override def applyCompanionModule(b: ClsLikeBody): Unit =
    lastWords("handled inline in `applyDefn`")
  
end FlowPreAnalyzer

class FlowConstraintsCollector(
  val preAnalyzer: FlowPreAnalyzer,
  val mono: Bool,
  val nonAffineTracking: Bool,
  val accumulatorTracking: Bool,
):
  given FlowPreAnalyzer = preAnalyzer
  given Raise = preAnalyzer.raise
  given fState: FlowAnalysis.State = preAnalyzer.fState
  given eState: Elaborator.State = preAnalyzer.eState
  given tl: TraceLogger = preAnalyzer.tl
  import StratVar.freshVar
  
  
  private case class Ctx(
    fun: Opt[FunCtx],
    suppressEffect: Bool, // e.g., if @pure
  )
  
  private case class FunCtx(
    effect: EffectVar,
    paramLists: Ls[LoweredParamList],
  ):
    def isOwnParam(sym: Symbol): Bool =
      paramLists.exists(_.paramSyms.contains(sym))
  
  private object Ctx:
    val default = Ctx(fun = N, suppressEffect = false)
  
  
  /** [[ConstraintScope]] represents the current scope of constraints being
    * collected. There are four types of scopes (`forScc`, `forFun`): the global
    * scope `(N, N)`, the scope of an SCC in poly mode `(S, N)`, the scope of a
    * function in an SCC in poly mode `(S, S)`, and the scope of a function in
    * mono mode `(N, S)`. It contains the following information:
    *
    * @param forScc The symbol of the representative function of the SCC of the
    *   function being analyzed. 
    * @param forFun The symbol of the owning root function; (nested functions
    *   retain this).
    * @param constraints The constraints collected in this scope.
    * @param strategies The (solved) strategies from instantiation.
    *   [[constraints]] (endpoints) with [[strategies]] together contribute to
    *   [[StratScheme.strategies]].
    * @param environment The mapping from the environment strategy variables to
    *   the local strategy variables, correspdonding to
    *   [[StratScheme.environment]].
    * @param variables The mapping from the original strategy variables from the
    *   pre-analyzer to the strategy variables local to this SCC. This is used
    *   to ensure that each original strategy variable is not shared between
    *   different SCCs.
    */
  class ConstraintScope private (
    val forScc: Opt[TermSymbol],
    val forFun: Opt[TermSymbol],
    val constraints: mutable.Buffer[Constraint],
    val strategies: mutable.Buffer[Strat],
    val environment: mutable.Map[StratVar, StratVar],
    val variables: mutable.Map[StratVar, StratVar],
  ):
    val instId: Opt[InstantiationId] = forScc.fold(S(Nil))(_ => N)
    
    def constrain(p: ProdStrat, c: ConsStrat): Unit =
      constraints.append(p -> c)
    
    def constrainOpaque(v: StratVar): Unit =
      constrain(UnknownProd, v)
      constrain(v, UnknownCons)
    
    /** Query the strategy variable for this scope. 
     * 
     *  - If in mono mode or the global scope in poly mode, use `v`.
     *  - If in other scopes in poly mode,
     *    - If `v` belongs to the current SCC, create a local copy of `v` for
     *      this scope and cache it in [[variables]].
     *    - If `v` does not belong to the current SCC, create a local proxy of
     *      `v` for this scope and cache it in [[environment]].
     */
    def variable(v: StratVar): StratVar = forScc match
      case S(forScc) =>
        if v.generatedForFun.flatMap(funToSccRep).contains(forScc) then
          variables.getOrElseUpdate(v, locally:
            val vv = new StratVar(v.name, v.sourceSymbol, v.generatedForFun)
            fState.stratVars += vv
            vv
          )
        else 
          environment.getOrElseUpdate(v, locally:
            freshVar(s"env_${v.name}", N, S(forScc))
          )
      case N => v
    
    def forActualRootFun(forFun: TermSymbol): ConstraintScope =
      assert(preAnalyzer.res.rootFunDefns.contains(forFun))
      new ConstraintScope(forScc, S(forFun), constraints, strategies, environment, variables)
  
  object ConstraintScope:
    def apply(forScc: Opt[TermSymbol], forFun: Opt[TermSymbol]): ConstraintScope =
      new ConstraintScope(
        forScc, forFun, 
        constraints = mutable.Buffer.empty,
        strategies = mutable.Buffer.empty, 
        environment = LinkedHashMap.empty, 
        variables = LinkedHashMap.empty
      )
  
  val globalScope = ConstraintScope(N, N)
  
  val funToScc = MutMap.empty[TermSymbol, Ls[TermSymbol]]
  def funToSccRep(tSym: TermSymbol): Option[TermSymbol] = funToScc.get(tSym).map(_.head)
  
  // for fusing strictly internal parts of functions
  val synthesizedInstIdToFunSym = LinkedHashMap.empty[InstantiationId, TermSymbol]

  val allRealCtors = mutable.Buffer.empty[Ctor]
  private def registerCtor(c: Ctor)(using cc: ConstraintScope): Ctor =
    if cc.forScc.isEmpty then allRealCtors += c
    c
  
  private def generatedVars(sym: Symbol)(using cc: ConstraintScope): StratVar = // TODO: tighten `Symbol` type!
    cc.variable(preAnalyzer.res.generatedVars.getOrElse(sym, preAnalyzer.res.primitiveStratVar))
  
  // Unknown getter effects must not flow into primitiveStratVar: its bounds also
  // feed runtime value slots, where effect markers have no representation.
  private val unknownEffect = freshVar("unknown_effect")
  private def generatedEffects(sym: Symbol)(using cc: ConstraintScope): EffectVar = // TODO: tighten `Symbol` type! // TODO: use at access sites of getters!
    preAnalyzer.res.generatedEffects.getOrElse(sym, unknownEffect).map(cc.variable)

  // * This is for effect analysis. The nonlocal variables that are potentially shared. 
  // * If a function accesses a nonlocal, it is conservatively considered unsafe for eta-expansion. 
  private val nonlocals = preAnalyzer.res.capturedVars.valuesIterator.flatten
    .filterNot(_ == eState.runtimeSymbol).toSet
  
  /** [[Instantiator]] instantiates a strategy graph for a function producer
    * ([[ProdFun]]), represented by a polymorphic splitting scheme
    * ([[StratScheme]]).
    * 
    * @param referSite The reference site that is instantiating the scheme.
    * @param referringTo The symbol of the function being instantiated.
   */
  private class Instantiator(
    referSite: ResultId,
    referringTo: TermSymbol,
  )(using cc: ConstraintScope):
    
    // The representative of the SCC of the function being instantiated.
    private val groupRep: TermSymbol = funToSccRep(referringTo).get
    
    // Instantiation copies the strategy graph preserving shared nodes. The
    // following maps ensure that each original strategy is copied once only.
    private val copiesOfStratVar = MutMap.empty[StratVar, StratVar]
    private val copiesOfProdFun = MutMap.empty[ProdFun, ProdFun]
    private val copiesOfConsFun = MutMap.empty[ConsFun, ConsFun]
    private val copiesOfCtor = MutMap.empty[Ctor, Ctor]
    private val copiesOfDtor = MutMap.empty[Dtor, Dtor]
    private val copiesOfFieldSel = MutMap.empty[FieldSel, FieldSel]
    
    // A strategy graph may contain cycles so instantiation can't be done in one
    // pass. The following stack of callbacks stores the work to do in the
    // second pass, completing the bounds of copied strategies after the first.
    private type Callback = () => Unit
    private val callbacks = mutable.Stack.empty[Callback]

    private def newInstantiation(instId: Opt[InstantiationId]): InstantiationId =
      referSite :: instId.getOrElse(Nil)
    
    private def duplicateProdStrat[T <: ProdStrat](s: T): T = (s match
      case v: StratVar => duplicateStratVar(v)
      case p: ProdFun => duplicateProdFun(p)
      case c: Ctor => duplicateCtor(c)
      case s: MarkerProdStrat => s
    ).asInstanceOf[T]

    private def duplicateConsStrat[T <: ConsStrat](c: T): T = (c match
      case v: StratVar => duplicateStratVar(v)
      case c: ConsFun => duplicateConsFun(c)
      case d: Dtor => duplicateDtor(d)
      case s: FieldSel => duplicateFieldSel(s)
      case c: MarkerConsStrat => c
      case pAcc: PossibleAccumulator => duplicateStratVar(pAcc.s).asPossibleAccumulator
      case iPrm: IntoParam => duplicateStratVar(iPrm.s).asIntoParam
    ).asInstanceOf[T]

    private def duplicateStratVar(s: StratVar): StratVar =
      assert(s.generatedForFun.flatMap(funToSccRep).contains(groupRep))
      copiesOfStratVar.getOrElseUpdate(s, locally:
        val copy = freshVar(s.name, s.sourceSymbol, cc.forFun)
        callbacks.push: () =>
          for lower <- s.lowerBounds do copy.lowerBounds += duplicateProdStrat(lower)
          for upper <- s.upperBounds do copy.upperBounds += duplicateConsStrat(upper)
        copy
      )
    
    private def duplicateProdFun(p: ProdFun): ProdFun = copiesOfProdFun.getOrElseUpdate(p, locally:
      val copy = new ProdFun(p.exprId, S(newInstantiation(p.instantiationId)))(
        p.params.map(duplicateConsStrat),
        p.requiredParamCount,
        p.restParam.map(duplicateConsStrat),
        duplicateProdStrat(p.res),
        duplicateStratVar(p.capturedVarUpperbound),
        p.effect.map(duplicateStratVar)
      )
      cc.strategies += copy
      callbacks.push: () =>
        for dest <- p.dests do copy.dests += duplicateConsStrat(dest)
      copy
    )

    private def duplicateConsFun(c: ConsFun): ConsFun = copiesOfConsFun.getOrElseUpdate(c, locally:
      val copy = new ConsFun(c.exprId, S(newInstantiation(c.instantiationId)))(
        c.params.map(duplicateProdStrat), 
        duplicateConsStrat(c.res), 
        c.effect.map(duplicateStratVar)
      )
      cc.strategies += copy
      callbacks.push: () =>
        for src <- c.srcs do copy.srcs += duplicateProdStrat(src)
      copy
    )

    private def duplicateCtor(c: Ctor): Ctor = copiesOfCtor.getOrElseUpdate(c, locally:
      val copy = registerCtor(new Ctor(c.exprId, S(newInstantiation(c.instantiationId)))(
        c.ctor, 
        c.args.map((a, b) => a -> duplicateProdStrat(b))
      ))
      cc.strategies += copy
      callbacks.push: () =>
        for dest <- c.dests do copy.dests += duplicateConsStrat(dest)
      copy
    )

    private def duplicateDtor(c: Dtor): Dtor = copiesOfDtor.getOrElseUpdate(c, locally:
      val copy = new Dtor(c.exprId, S(newInstantiation(c.instantiationId)))
      cc.strategies += copy
      callbacks.push: () =>
        for src <- c.srcs do copy.srcs += duplicateProdStrat(src)
      copy
    )

    private def duplicateFieldSel(c: FieldSel): FieldSel = copiesOfFieldSel.getOrElseUpdate(c, locally:
      val copy = new FieldSel(c.exprId, S(newInstantiation(c.instantiationId)))(
        c.field, 
        c.selectsFrom, 
        duplicateStratVar(c.consVar)
      )
      cc.strategies += copy
      callbacks.push: () =>
        for src <- c.srcs do copy.srcs += duplicateProdStrat(src)
      copy
    )

    def instantiate(scheme: StratScheme): StratVar =
      // Establish mapping from the scheme's proxy strategy variables to the
      // environment strategy variables. See `StratScheme.environment`.
      for (external, proxy) <- scheme.environment do
        copiesOfStratVar(proxy) = cc.variable(external)
      
      val s = duplicateStratVar(scheme.s)
      scheme.strategies.foreach:
        case p: ProdStrat => duplicateProdStrat(p)
        case c: ConsStrat => duplicateConsStrat(c)
        
      // The bounds of environment, i.e., the boundary between the scheme's
      // internal and external strategy variables, need to be established again.
      for (external, proxy) <- scheme.environment do
        val internal = copiesOfStratVar(proxy)
        proxy.lowerBounds.foreach(p => cc.constrain(duplicateProdStrat(p), internal))
        proxy.upperBounds.foreach(c => cc.constrain(internal, duplicateConsStrat(c)))
      
      while callbacks.nonEmpty do
        val callback = callbacks.pop()
        callback()
      
      s
  
  end Instantiator
  
  private def instantiate(
    scheme: StratScheme,
    referSite: ResultId,
    referringTo: TermSymbol,
  )(using cc: ConstraintScope): StratVar =
    new Instantiator(referSite, referringTo).instantiate(scheme)
  
  /** Maps a function (symbol) to its corresponding polymorphic splitting scheme. */
  private val funToScheme = MutMap.empty[TermSymbol, StratScheme]

  /** Analyze and prepare reusable function schemes ([[StratScheme]]) and store
   *  them into [[funToScheme]].
   */
  // TODO: analyze in mono mode too!
  private def analyze(): Unit =
    if !mono then
      // Computing the StratScheme for each scc group, this way the sccs of the call graph is
      // never materialized
      object SccStratSchemeAnalysis extends SccAnalysis[TermSymbol]:
        protected def successors(f: TermSymbol): Ls[TermSymbol] =
          var callees = Ls.empty[TermSymbol]
          object CollectAllReferredFun extends BlockTraverser:
            override def applyPath(p: Path) = p match
              case FunRef(callee, _) =>
                if preAnalyzer.res.rootFunDefns.contains(callee) then
                  callees ::= callee
              case _ => ()
          CollectAllReferredFun.applyBlock(preAnalyzer.res.rootFunDefns(f).body)
          callees
        protected def isHandled(f: TermSymbol) = funToScheme.contains(f)
        protected def handleScc(groupedFuns: Ls[TermSymbol], sccId: Int): Unit =
          for f <- groupedFuns do funToScc(f) = groupedFuns
          val groupRep = groupedFuns.head
          ConstraintScope(Some(groupRep), N).givenIn: cc ?=>
            given Ctx = Ctx.default
            for funSym <- groupedFuns do
              given ConstraintScope = cc.forActualRootFun(funSym)
              processFunctionDefn(preAnalyzer.res.funSymToFunDefn(funSym))
            if nonAffineTracking then
              for
                sym <- preAnalyzer.res.nonAffineSyms
                stratVar <- preAnalyzer.res.generatedVars.get(sym)
                if stratVar.generatedForFun.flatMap(funToSccRep).contains(groupRep)
              do cc.constrain(cc.variable(stratVar), NonAffine)
            
            val solver = new FlowConstraintSolver(FlowConstraintsCollector.this)(cc)
            solver.solve()
            
            val strategies =
              (
                cc.constraints.iterator.flatMap((p, c) => Iterator(p, c)) ++ 
                cc.strategies.iterator
              ).distinct.toList
            val environment = cc.environment.toList
            for funSym <- groupedFuns do
              funToScheme(funSym) = StratScheme(generatedVars(funSym), strategies, environment)
      
      end SccStratSchemeAnalysis
      
      SccStratSchemeAnalysis.queryAll(preAnalyzer.res.rootFunDefns.keys)
    end if
  end analyze
  
  /** Collect the program's constraints by processing the program recursively,
   * and then assemble the program's global constraints.
   */
  private def collect(): Unit =
    // collect constraints from the top-level block
    globalScope.givenIn: cc ?=>
      cc.constrain(preAnalyzer.res.primitiveStratVar, UnknownCons)
      cc.constrain(UnknownProd, preAnalyzer.res.primitiveStratVar)
      cc.constrain(UnsafeEta, unknownEffect)
      processBlock(preAnalyzer.pgrm.main)(using cc, UnknownCons, Ctx.default)

      // this places non-affine constraints correctly:
      // - in mono mode there are no per-scc collectors,
      // so the global collector gets all the relevant non-affine constraints;
      // - in poly mode, non-affine constraints on scc-owned symbols are handled
      // in their scc strat scheme, and the global collector collects the remaining constriants
      if nonAffineTracking then
        for
          sym <- preAnalyzer.res.nonAffineSyms
          stratVar <- preAnalyzer.res.generatedVars.get(sym)
          if mono || stratVar.generatedForFun.isEmpty
        do cc.constrain(stratVar, NonAffine)

      for
        (tsym, defn) <- preAnalyzer.res.rootValDefns
        if defn.visibility is Visibility.Public
      do
        cc.constrain(generatedVars(tsym), UnknownCons)

      if mono then
        for
          (_, fun) <- preAnalyzer.res.rootFunDefns
          if fun.visibility is Visibility.Public
        do
          cc.constrain(generatedVars(fun.dSym), UnknownCons)
      else
        for (funSym, fun) <- preAnalyzer.res.rootFunDefns do
          val scheme = funToScheme(funSym)
          val synthesizedRefUid =
            preAnalyzer.res.funSymToFunDefn(funSym).sym.asMemberRef(funSym).uid
          val selfProd = instantiate(scheme, synthesizedRefUid, funSym)
          cc.constrain(selfProd, UnknownCons)
          val selfInstId = synthesizedRefUid :: Nil
          synthesizedInstIdToFunSym(selfInstId) = funSym
    
  end collect
    
  private def processFunctionBody(
    resName: String,
    params: NELs[LoweredParamList],
    body: Block,
    funLamId: FunId,
    annotations: Ls[Annot],
  )(using cc: ConstraintScope, ctx: Ctx): ProdStrat =
    def paramListFunId(whichParamList: Int): FunId =
      funLamId match
        case (sym: TermSymbol, -1) => (sym, whichParamList)
        case lambdaExprId: ResultId =>
          assert(whichParamList == 0)
          lambdaExprId
        case other => lastWords(s"unexpected funLamId shape: $other")
    val res = freshVar(resName, cc.forFun)
    val sourceSymbol = funLamId match
      case (sym: TermSymbol, _) => S(sym)
      case _: ResultId => N
    val effect =
      freshVar(s"effect_$funLamId", sourceSymbol, cc.forFun)
    params.foreach: ps =>
      ps.restParam.foreach: p =>
        cc.constrainOpaque(generatedVars(p.sym))
      // * The argument of an optional parameter may be omitted, in which case the parameter is
      // * `null`, a value that is not tracked by the analysis.
      ps.params.drop(ps.paramCountLB).foreach: p =>
        cc.constrain(UnknownProd, generatedVars(p.sym))
    val funValueStrat = params.zipWithIndex.foldRight[ProdStrat](res):
      case ((ps, whichParamList), acc) =>
        val plFunId = paramListFunId(whichParamList)
        // A declared curried function runs its body only at the final list.
        // Applying earlier parameter lists only captures arguments; each needs its own, initially pure summary.
        val effectParamList =
          if whichParamList == params.size - 1 then effect
          else freshVar(s"effect_$plFunId", cc.forFun)
        val capUB = freshVar(s"cap_ub_$plFunId", cc.forFun)
        for
          v <- preAnalyzer.res.capturedVars(plFunId)
          capturedSymStrat <- preAnalyzer.res.generatedVars.get(v)
        do
          cc.constrain(cc.variable(capturedSymStrat), capUB)
        new ProdFun(plFunId, cc.instId)(
          ps.params.map(p => generatedVars(p.sym)),
          ps.paramCountLB,
          ps.restParam.map(p => generatedVars(p.sym)),
          acc,
          capUB,
          effectParamList)
    
    given ctx: Ctx = Ctx(
      fun = S(FunCtx(effect, params)), 
      suppressEffect = annotations.exists(_.isInstanceOf[Annot.Pure])
    )
    processBlock(body)(using cc, res)
    funValueStrat

  private def processFunctionDefn(fun: FunDefn)(using cc: ConstraintScope, ctx: Ctx): Unit =
    val isRoot = preAnalyzer.res.rootFunDefns.contains(fun.dSym)
    val belongsToCurrentScope = !isRoot || cc.forFun.contains(fun.dSym)
    if mono || belongsToCurrentScope then
      given ConstraintScope = if belongsToCurrentScope 
        then cc // If belongs to the current scope: just reuse the scope
        else cc.forActualRootFun(fun.dSym) // If mono mode: create scope
      fun.params match
      case Nil =>
        given ctx: Ctx = Ctx(
          fun = S(FunCtx(generatedEffects(fun.dSym), Nil)), 
          suppressEffect = fun.annotations.exists(_.isInstanceOf[Annot.Pure])
        )
        processBlock(fun.body)(using cc, generatedVars(fun.dSym))
      case nel: NELs[?] =>
        val funProdStrat = processFunctionBody(
          s"${fun.dSym.nme}_res",
          nel,
          fun.body,
          (fun.dSym, -1),
          fun.annotations)
        cc.constrain(funProdStrat, generatedVars(fun.dSym))
    
  private def processClsLikeDefn(cls: ClsLikeDefn)(using cc: ConstraintScope, ctx: Ctx): Unit =
    cls.methodKeys.valuesIterator.foreach(constrainOpaqueResult)
    cls.privateFields.foreach: sym => 
      cc.constrainOpaque(generatedVars(sym))
    cls.publicFields.foreach: (_, tsym) => 
      cc.constrainOpaque(generatedVars(tsym))
    cls.methods.foreach: fun =>
      cc.constrainOpaque(generatedVars(fun.dSym))
      fun.params.foreach(_.allParams.foreach(p => cc.constrainOpaque(generatedVars(p.sym))))
      processBlock(fun.body)(using cc, UnknownCons, Ctx(S(FunCtx(cc.variable(unknownEffect), fun.params)), fun.annotations.exists(_.isInstanceOf[Annot.Pure])) /* methods are always considered impure; we don't track their effects */)
    processBlock(cls.preCtor)(using cc, UnknownCons, Ctx(S(FunCtx(cc.variable(unknownEffect), Nil)), suppressEffect = false) /* FIXME: ctor effects should NOT be discarded */)
    processBlock(cls.ctor)(using cc, UnknownCons, Ctx(S(FunCtx(cc.variable(unknownEffect), Nil)), suppressEffect = false) /* FIXME: ctor effects should NOT be discarded */)
    cls.companion.foreach: mod =>
      mod.methodKeys.valuesIterator.foreach(constrainOpaqueResult)
      mod.privateFields.foreach: sym => 
        cc.constrainOpaque(generatedVars(sym))
      mod.publicFields.foreach: (_, tsym) =>
        cc.constrainOpaque(generatedVars(tsym))
      mod.methods.foreach: fun =>
        processFunctionDefn(fun)
      processBlock(mod.ctor)(using cc, UnknownCons, Ctx(S(FunCtx(cc.variable(unknownEffect), Nil)), suppressEffect = false) /* FIXME: ctor effects should NOT be discarded */)
  
  private def constrainOpaqueResult(r: Result)(using cc: ConstraintScope, ctx: Ctx): Unit =
    cc.constrain(processResult(r), UnknownCons)

  private def constrainEffect(prod: ProdStrat)(using cc: ConstraintScope, ctx: Ctx): Unit =
    if !ctx.suppressEffect then
      ctx.fun.foreach: fun =>
        fun.effect.foreach(effect => cc.constrain(prod, effect))

  private def processBlock(b: Block)(using cc: ConstraintScope, blkRes: ConsStrat, ctx: Ctx): Unit =
    val instId = cc.instId
    b match
    case Return(res) => cc.constrain(processResult(res), blkRes)
    case Throw(exc, annotations) =>
      if annotations.exists(_.isInstanceOf[Annot.Pure]) then
        // TODO: the @pure annotation on throw also suppresses the effects of
        // the result. This is due to a limitation that constructors' effects
        // are not analyzed, so constructing an error object is always
        // effectful.
        constrainOpaqueResult(exc)(using cc, ctx.copy(suppressEffect = true))
      else
        constrainEffect(UnsafeEta)
        constrainOpaqueResult(exc)
    case Match(scrut, arms, dflt, rest) =>
      val scrutStrat = processResult(scrut)
      cc.constrain(scrutStrat, new Dtor(scrut.uid, instId))
      for case (Case.Cls(cls, path), _) <- arms do
        cc.constrain(processResult(path), UnknownCons)
      (arms.map(_._2) ++ dflt).foreach(processBlock)
      processBlock(rest)
    case Label(l, loop, body, rest) =>
      processBlock(body)
      processBlock(rest)
    case Break(label) => ()
    case Continue(label) => ()
    case Scoped(syms, body) => processBlock(body)
    case Begin(sub, rest) =>
      processBlock(sub)
      processBlock(rest)
    case Assign(lhs, rhs, rest) =>
      val rhsStrat = processResult(rhs)
      lhs.match
        case NoSymbol => ()
        case lhs: (LocalVarSymbol | TermSymbol) =>
          if nonlocals.contains(lhs) then constrainEffect(UnsafeEta)
          cc.constrain(rhsStrat, generatedVars(lhs))
      processBlock(rest)
    case TryBlock(sub, finallyDo, rest) =>
      processBlock(sub)
      processBlock(finallyDo)
      processBlock(rest)
    case AssignField(lhs, nme, rhs, rest) =>
      constrainEffect(UnsafeEta)
      constrainOpaqueResult(lhs)
      constrainOpaqueResult(rhs)
      processBlock(rest)
    case AssignDynField(lhs, fld, kind, rhs, rest) =>
      constrainEffect(UnsafeEta)
      constrainOpaqueResult(lhs)
      constrainOpaqueResult(fld)
      constrainOpaqueResult(rhs)
      processBlock(rest)
    case Define(defn, rest) =>
      defn match
      case ValDefn(tsym, sym, rhs) =>
        val rhsStrat = processResult(rhs)
        cc.constrain(rhsStrat, generatedVars(tsym))
      case fun: FunDefn =>
        // The eta optimizer requires lifting.
        // Other definitions are deliberately opaque.
        constrainEffect(UnsafeEta)
        processFunctionDefn(fun)
      case cls: ClsLikeDefn =>
        constrainEffect(UnsafeEta)
        processClsLikeDefn(cls)
      processBlock(rest)
    case End(msg) => ()
    case Unreachable(_) => ()
    
  private def processResult(r: Result)(using cc: ConstraintScope, ctx: Ctx): ProdStrat =
    val instId = cc.instId
    def freshCallEffect(): StratVar =
      val effect = freshVar("call_effect", cc.forFun)
      // A call's effect contributes to the enclosing function's latent effect.
      constrainEffect(effect)
      effect
    def constrainConstructorEffect(result: Result): Unit =
      val unsafeEta = result match
        case call: Call => !FlowAnalysis.hasPureAnnotation(call, call.argss.size - 1)
        case _: Instantiate => true
        case _ => false
      // Constructor bodies are not modeled here; instantiation may have effects.
      if unsafeEta then constrainEffect(UnsafeEta)
    def handleCallLike(callId: CallId, fStrat: ProdStrat, args: List[Arg]): ProdStrat =
      val argsStrat = args.map(a => processResult(a.value))
      if args.exists(_.spread.isDefined) then
        // TODO: preserve callee-effect precision for spread calls
        // * Needs to address [todo:effectful-spreads]
        constrainEffect(UnsafeEta)
        cc.constrain(fStrat, UnknownCons)
        argsStrat.foreach(arg => cc.constrain(arg, UnknownCons))
        UnknownProd
      else
        val callRes = freshVar("call_res", cc.forFun)
        val effect: EffectVar = callId.exprId.getResult match
          case call: Call if FlowAnalysis.hasPureAnnotation(call, callId.whichArgList) => BottomEffect
          case _ => freshCallEffect()
        cc.constrain(fStrat, new ConsFun(callId, instId)(
          argsStrat,
          callRes,
          effect,
        ))
        callRes
    r match
      case sel@TrackableSelect(from, field, owner) =>
        constrainEffect(UnsafeEta)
        val fromStrat = processResult(from)
        val selRes = freshVar("sel_res", cc.forFun)
        cc.constrain(
          fromStrat,
          new FieldSel(sel.uid, instId)(field, owner, selRes))
        selRes
      case c@CtorProducer(ctor, args, selectedFrom) if args.forall(_.spread.isEmpty) =>
        constrainConstructorEffect(c)
        for qual <- selectedFrom do
          cc.constrain(processResult(qual), UnknownCons)
        val argsStrat = args.map:
          case Arg(_, a) => processResult(a)
        ctor match
        case cls: ClassSymbol =>
          cls.tree.clsParams.size match
          case 1 =>
            val clsParams = cls.tree.clsParams.head // TODO use irDefn here and elsewhere
            // TODO: properly check the parameter lists, which may change after passes like lifting
            // softTODO(argsStrat.size === clsParams.size, s"mismatched ctor arg and cls param sizes")
            registerCtor(new Ctor(c.uid, instId)(ctor, clsParams.zip(argsStrat)))
          case _ =>
            // - the size of 0 means we don't know the cls param symbols,
            // so we constrain args with UnknownCons and this CtorProducer gives UnknownProd
            // - if size > 1, we cannot handle multiple parameter class flow now,
            //   constrain args with UnknownCons and this CtorProducer gives UnknownProd
            for a <- argsStrat do cc.constrain(a, UnknownCons)
            UnknownProd
        case _: ModuleOrObjectSymbol => registerCtor(new Ctor(c.uid, instId)(ctor, Nil))
        case tupSize: Int =>
          registerCtor(new Ctor(c.uid, instId)(tupSize, (0 until tupSize).zip(argsStrat).toList))
      case c@CtorProducer(_, args, selectedFrom) =>
        constrainEffect(UnsafeEta)
        for qual <- selectedFrom do
          cc.constrain(processResult(qual), UnknownCons)
        args.foreach(arg => cc.constrain(processResult(arg.value), UnknownCons))
        UnknownProd
      case c@Call(fun, argss) =>
        // each later arg list applies the result of the previous one
        argss.iterator.zipWithIndex.foldLeft(processResult(fun)):
          case (fStrat, (args, whichArgList)) => handleCallLike((c.uid, whichArgList), fStrat, args)
      case i@Instantiate(_, cls, argss) =>
        constrainConstructorEffect(i)
        constrainOpaqueResult(cls)
        argss.flatten.foreach(a => constrainOpaqueResult(a.value))
        UnknownProd
      case lam@Lambda(ps, body) =>
        processFunctionBody("lam_res", ps ne_:: Nil, body, lam.uid, Nil)
      case _: Tuple => lastWords("should be handled in CtorProducer")
      case Record(_, fields) =>
        if fields.exists(_.spread) then constrainEffect(UnsafeEta)
        fields.foreach:
          case RcdArg(idx, value) =>
            idx.foreach(p => cc.constrain(processResult(p), UnknownCons))
            cc.constrain(processResult(value), UnknownCons)
        UnknownProd
      case refSite @ FunRef(f, selectedFrom) =>
        // ? [todo:harry-0]
        // ? It's a special case for module getters but I'm not sure if
        // ? this is good enough. It just conservatively marks it unsafe.
        if f.irFunDefn.fold(!f.isAccessPure)(_.params.isEmpty) then constrainEffect(UnsafeEta)
        refSite match
          case DynSelect(_, key, DynSelectKind.Member(_)) => cc.constrain(processResult(key), UnknownCons)
          case SuperSelect(_, base, key) =>
            cc.constrain(processResult(base), UnknownCons)
            cc.constrain(processResult(key), UnknownCons)
          case _ => ()
        for qual <- selectedFrom do
          cc.constrain(processResult(qual), UnknownCons)
        funToScheme.get(f) match
        case Some(fScheme) =>
          instantiate(fScheme, refSite.uid, f)
        case None => generatedVars(f)
      case s @ SuperSelect(qual, base, key) =>
        constrainEffect(UnsafeEta)
        cc.constrain(processResult(key), UnknownCons)
        cc.constrain(processResult(qual), UnknownCons)
        cc.constrain(processResult(base), UnknownCons)
        generatedVars(s.symbol)
      case s @ Select(qual, name) =>
        constrainEffect(UnsafeEta)
        cc.constrain(processResult(qual), UnknownCons)
        s.symbol.fold(UnknownProd): selSym =>
          generatedVars(selSym)
      case DynSelect(qual, fld, kind) =>
        constrainEffect(UnsafeEta)
        cc.constrain(processResult(qual), UnknownCons)
        cc.constrain(processResult(fld), UnknownCons)
        kind match
          case DynSelectKind.Member(sym) => generatedVars(sym)
          case DynSelectKind.ArrayIdx | DynSelectKind.Unknown => UnknownProd
      // * A cast passes its operand through; a checked one may also throw.
      case Cast(value, _, check) =>
        if check then constrainEffect(UnsafeEta)
        val valueStrat = processResult(value)
        cc.constrain(valueStrat, UnknownCons)
        valueStrat
      case Value.MemberRef(_, disamb) =>
        disamb match
        case _: ClassSymbol | _: PatternSymbol =>
          // Just accessing the binding is pure.
          ()
        case sym: TermSymbol =>
          // (Accessing mutable fields is a Select)
          if !sym.isAccessPure then constrainEffect(UnsafeEta)
        case _: ModuleOrObjectSymbol =>
          lastWords("module/object references should be handled by CtorProducer")
        case _: TypeAliasSymbol =>
          lastWords("type aliases should not occur as runtime member references")
        generatedVars(disamb)
      case Value.SimpleRef(sym) =>
        if nonlocals.contains(sym) then
          if !ctx.fun.exists(_.isOwnParam(sym)) then
            constrainEffect(UnsafeEta)
        generatedVars(sym)
      case Value.This(_) => UnknownProd
      case Value.Lit(lit) => UnknownProd

  analyze()
  collect()
  
end FlowConstraintsCollector


/** The solver has to solve constraints from different scopes (either SCCs or
 *  the global scope) separately. [[collector]] specifies the states and options
 *  for the whole program, and [[scope]] specifies the actual set of constraints
 *  to be solved.
 */
class FlowConstraintSolver(
  val collector: FlowConstraintsCollector,
)(
  val scope: collector.ConstraintScope
):
  given tl: TraceLogger = collector.tl
  given fState: FlowAnalysis.State = collector.fState
  given eState: Elaborator.State = collector.eState
  given preAnalyzer: FlowPreAnalyzer = collector.preAnalyzer
  given Raise = preAnalyzer.raise
  given SymbolPrinter = preAnalyzer.traceSymbolPrinter
  
  
  val ctorsWithDests = mutable.Buffer.empty[Ctor]
  val consumersWithSrcs = mutable.Buffer.empty[ConcreteCtorConsumer]
  val prodFunsWithDests = mutable.Buffer.empty[ProdFun]
  val consFunsWithSrcs = mutable.Buffer.empty[ConsFun]
  
  val functionEffectVars = LinkedHashMap.empty[ConcreteId[FunId], EffectVar]
  val callEffectVars = LinkedHashMap.empty[ConcreteId[CallId], EffectVar]
  
  private val registered: mutable.Set[Strat] = MutSet.empty
  
  private def register(strat: Strat): Unit = strat match
    case p: ProdFun =>
      if p.instantiationId.isDefined then functionEffectVars(p.concreteId) = p.effect
      if p.dests.nonEmpty && registered.add(p) then prodFunsWithDests += p
      register(p.res) // for curried functions
    case c: ConsFun =>
      if c.instantiationId.isDefined then callEffectVars(c.concreteId) = c.effect
      if c.srcs.nonEmpty && registered.add(c) then consFunsWithSrcs += c
    case c: Ctor =>
      if c.dests.nonEmpty && registered.add(c) then ctorsWithDests += c
    case d: ConcreteCtorConsumer =>
      if d.srcs.nonEmpty && registered.add(d) then consumersWithSrcs += d
    case _ => ()
  
  private def addCtorDest(c: Ctor, d: ConcreteCtorConsumer | MarkerConsStrat): Unit =
    if c.dests.add(d) && c.dests.size == 1 then register(c)
  private def addDtorSrc(d: ConcreteCtorConsumer, p: Ctor | MarkerProdStrat): Unit =
    if d.srcs.add(p) && d.srcs.size == 1 then register(d)
  private def addFunDest(p: ProdFun, c: ConsFun | MarkerConsStrat): Unit =
    if p.dests.add(c) && p.dests.size == 1 then register(p)
  private def addFunSrc(c: ConsFun, p: ProdFun | MarkerProdStrat): Unit =
    if c.srcs.add(p) && c.srcs.size == 1 then register(c)
  
  /** Whether instances of `cls` may have the fields of `ancestor` through inheritance.
    * A class whose parent chain is not known is assumed to possibly inherit them.
    * TODO: cache inheritance set in header object to avoid retraversals, here and elsewhere (eg erased types). */
  private def mayInheritFields(cls: CtorCls, ancestor: CtorCls): Bool = (cls, ancestor) match
    case (cls: ClassLikeSymbol, ancestor: ClassLikeSymbol) =>
      def go(cur: ClassLikeSymbol, seen: Set[ClassLikeSymbol]): Bool =
        cur.irClassHeader.fold(ClassHeader.Parent.Unknown)(_.parent) match
          case ClassHeader.Parent.Unknown => true
          case ClassHeader.Parent.Root => false
          case ClassHeader.Parent.Known(parent) => parent.asClsOrMod match
            case S(parent) => (parent is ancestor) || !seen(parent) && go(parent, seen + parent)
            case N => true
      go(cls, Set(cls))
    case _ => false
  
  object AllUpperBounds extends
    SccAnalysis.NoopHandling[StratVar]
    with SccAnalysis.CachingComputedNodeValue[StratVar, collection.Set[ConsStrat]]:
      
      protected def successors(node: StratVar): IterableOnce[StratVar] =
        node.upperBounds.iterator.collect:
          case v: StratVar => v
      
      protected def computeValuePerScc(members: Ls[StratVar], sccId: Int): collection.Set[ConsStrat] =
        val res = MutSet.empty[ConsStrat]
        for
          m <- members
          ub <- m.upperBounds
        do ub match
          case v: StratVar => res.addAll(computed.getOrElse(v, Nil))
          case _ => res.add(ub)
        res
      
      def apply(lb: StratVar): collection.Set[ConsStrat] = computed.get(lb) match
        case S(res) => res
        case N =>
          query(lb)
          computed(lb)
    
  
  private def logNonAffineSyms(stratVars: => Iterable[StratVar]): Unit =
    tl.scoped(FlowAnalysis.TraceScope.NonAffineSyms):
      if tl.isTracing then
        given ShowCfg = ShowCfg.internal
        tl.log(">>> non-affine syms >>>")
        val outputRes =
          for
            stratVar <- stratVars
            if AllUpperBounds(stratVar).contains(NonAffine)
          yield summon[SymbolPrinter].printSymbol(stratVar)
        for nonAffine <- outputRes.toSortedSet do
          tl.log(nonAffine)
        tl.log("<<< non-affine syms <<<")
  
  private def logAccumulatorSyms(stratVars: => Iterable[StratVar]): Unit =
    tl.scoped(FlowAnalysis.TraceScope.AccumulatorSym):
      if tl.isTracing then
        given ShowCfg = ShowCfg.internal
        tl.log(">>> accumulator syms >>>")
        def showAccumulatorSym(stratVar: StratVar): Opt[Str] =
          AllUpperBounds(stratVar)
            .collectFirst:
              case pAcc: PossibleAccumulator if pAcc.s is stratVar => stratVar
              case iPrm: IntoParam if iPrm.s is stratVar => stratVar
            .map(summon[SymbolPrinter].printSymbol)
        val outputRes =
          for
            stratVar <- stratVars
            if AllUpperBounds(stratVar).contains(Accumulator)
            accumulatorSym <- showAccumulatorSym(stratVar)
          yield accumulatorSym
        for accumulator <- outputRes.toSortedSet do
          tl.log(accumulator)
        tl.log("<<< accumulator syms <<<")
  
  def solve(): Unit =
    scope.strategies.foreach(register)
    
    def handle(constraint: Constraint): Unit =
      val (prod, cons) = constraint
      register(prod)
      register(cons)
      constraint match
      case (c: Ctor, d: Dtor) =>
        addCtorDest(c, d)
        addDtorSrc(d, c)
      case (c: Ctor, d: FieldSel) =>
        if d.selectsFrom === c.ctor then
          addCtorDest(c, d)
          addDtorSrc(d, c)
          handle(
            c.args.find(_._1 is d.field).get._2,
            d.consVar)
        // An inherited field is initialized by a parent constructor, which can receive any
        // of the subclass constructor's arguments. This analysis does not relate them to
        // the field, so the instance and the selected value must be treated as unknown.
        // Otherwise, eg, dead-parameter elimination would drop the argument that the field holds.
        // TODO: Properly track value flows through class constructors (current and inherited)
        else if mayInheritFields(c.ctor, d.selectsFrom) then
          handle(c, UnknownCons)
          handle(UnknownProd, d)
      case (c: Ctor, UnknownCons) =>
        addCtorDest(c, UnknownCons)
        for (_, argProd) <- c.args do handle(argProd, UnknownCons)
      case (c: Ctor, x@(NonAffine | Accumulator)) =>
        addCtorDest(c, x)
        for (_, argProd) <- c.args do handle(argProd, x)
      case (c: Ctor, i: IntoParam) =>
        for (_, argProd) <- c.args do handle(argProd, i.s.asPossibleAccumulator)
      case (c: Ctor, p: PossibleAccumulator) =>
        for (_, argProd) <- c.args do handle(argProd, p)
      case (p: ProdFun, c: ConsFun) =>
        addFunDest(p, c)
        addFunSrc(c, p)
        val tracksAccumulator = collector.accumulatorTracking
        
        c.params.take(p.params.size).lazyZip(p.params).foreach: (argC, argP) =>
          handle(argC -> argP)
          if tracksAccumulator then argP match
            case v: StratVar => handle(argC, v.asIntoParam)
            case _ => ()
        for
          restCons <- p.restParam
          arg <- c.params.drop(p.params.size)
        do
          handle(arg, restCons)
          if tracksAccumulator then restCons match
            case v: StratVar => handle(arg, v.asIntoParam)
            case _ => ()
        handle(p.res, c.res)
        // propagate effects
        p.effect.foreach: pe =>
          c.effect.foreach: ce => 
            handle(pe, ce)
      case (p: ProdFun, UnknownCons) =>
        addFunDest(p, UnknownCons)
        for a <- p.params do handle(UnknownProd, a)
        p.restParam.foreach(r => handle(UnknownProd, r))
        handle(p.res, UnknownCons)
        // unknown code may call the function any number of times
        if collector.nonAffineTracking then handle(p.capturedVarUpperbound, NonAffine)
      case (p: ProdFun, x@(NonAffine | Accumulator)) =>
        addFunDest(p, x)
        handle(p.capturedVarUpperbound, x)
      case (p: ProdFun, i: IntoParam) =>
        handle(p.capturedVarUpperbound, i.s.asPossibleAccumulator)
      case (p: ProdFun, c: PossibleAccumulator) =>
        handle(p.capturedVarUpperbound, c)
      case (UnknownProd, d: Dtor) =>
        addDtorSrc(d, UnknownProd)
      case (UnknownProd, sel: FieldSel) =>
        addDtorSrc(sel, UnknownProd)
        handle(UnknownProd, sel.consVar)
      case (UnknownProd, c: ConsFun) =>
        addFunSrc(c, UnknownProd)
        for a <- c.params do handle(a, UnknownCons)
        handle(UnknownProd, c.res)
        // The conservative fallback.
        c.effect.foreach(ce => handle(UnsafeEta, ce))
      case (p: StratVar, c: StratVar) =>
        if p.upperBounds.add(c) then
          for l <- p.lowerBounds do handle(l, c)
          for u <- c.upperBounds do u match
            // ! given p <: c and c <: u, it follows that p <: u, 
            // ! so skip handling the case p <: u.
            // ! this is an important optimization...
            case u: StratVar if p.upperBounds.contains(u) => ()
            case u => handle(p, u)
      case (p: StratVar, c) => if p.upperBounds.add(c) then
        c match
          case pAcc: PossibleAccumulator if p is pAcc.s =>
            p.upperBounds.add(Accumulator)
            for l <- p.lowerBounds do handle(l, Accumulator)
          case _ => ()
        for l <- p.lowerBounds do handle(l, c)
      case (p, c: StratVar) => if c.lowerBounds.add(p) then
        for u <- c.upperBounds do handle(p, u)
      case _ => () // ignore other cases
    end handle
    
    for c <- scope.constraints do handle(c)
  end solve
  
  def log(): Unit =
    lazy val stratVars =
      val inScope = MutSet.empty[StratVar]
      foreachStrategy:
        case v: StratVar => inScope += v
        case _ => ()
      // Select from this solver's graph while preserving the existing order of names.
      fState.stratVars.view.filter(inScope)
    logNonAffineSyms(stratVars)
    logAccumulatorSyms(stratVars)
  
  private def foreachStrategy(f: Strat => Unit): Unit =
    val visited = mutable.Set.empty[Strat]
    def visit(strat: Strat): Unit = if visited.add(strat) then
      f(strat)
      strat match
        case v: StratVar =>
          v.lowerBounds.foreach(visit)
          v.upperBounds.foreach(visit)
        case p: ProdFun =>
          p.params.foreach(visit)
          p.restParam.foreach(visit)
          visit(p.res)
          visit(p.capturedVarUpperbound)
          p.effect.foreach(visit)
          p.dests.foreach(visit)
        case c: ConsFun =>
          c.params.foreach(visit)
          visit(c.res)
          c.effect.foreach(visit)
          c.srcs.foreach(visit)
        case c: Ctor =>
          c.args.foreach((_, prod) => visit(prod))
          c.dests.foreach(visit)
        case s: FieldSel =>
          visit(s.consVar)
          s.srcs.foreach(visit)
        case d: ConcreteCtorConsumer =>
          d.srcs.foreach(visit)
        case p: PossibleAccumulator => visit(p.s)
        case p: IntoParam => visit(p.s)
        case _: MarkerProdStrat | _: MarkerConsStrat => ()

    registered.foreach(visit)
    scope.strategies.foreach(visit)
    for (prod, cons) <- scope.constraints do
      visit(prod)
      visit(cons)
    
    if scope.forScc.isEmpty then
      collector.allRealCtors.foreach(visit)

  def assertConcrete(): Unit =
    foreachStrategy:
      case s: StratWithOrigin[?] =>
        assert(s.instantiationId.isDefined, "abstract strategy escaped its scheme")
      case _ => ()
    
  
end FlowConstraintSolver
