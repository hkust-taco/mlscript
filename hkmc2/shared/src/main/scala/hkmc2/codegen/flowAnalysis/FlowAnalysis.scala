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

  class State:
    val resultToResultId = new java.util.IdentityHashMap[Result, ResultId].asScala
    val resultIdToResult = mutable.Map.empty[ResultId, Result]
    val stratVars = mutable.Buffer.empty[StratVar]
    object ResultUidState extends Uid.Result.State
  
    extension (instId: InstantiationId)
      def mkFunName(using Elaborator.State): String =
        instId
          .map: i =>
            s"${i.getReferredFun.get.name}_$i"
          .mkString("_")
    
    extension (resultId: ResultId)
      def getResult = resultIdToResult(resultId)
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
    
    extension (r: Result)
      def uid = resultToResultId.get(r) match
        case None =>
          val id = ResultId(ResultUidState.nextUid)
          resultIdToResult(id) = r
          resultToResultId(r) = id
          id
        case Some(id) => id
  
  
  def apply(
    pgrm: Program,
    mono: Bool,
    nonAffineTracking: Bool,
    accumulatorTracking: Bool,
  )(using TraceLogger, Elaborator.State, Raise, SymbolPrinter) =
    given State = new State
    val pre = new FlowPreAnalyzer(pgrm)
    val constrCol = new FlowConstraintsCollector(pre, mono, nonAffineTracking, accumulatorTracking)
    new FlowConstraintSolver(constrCol)

  def mkTraceLogger(
    cfg: Config.FlowAnalysisConfig,
    prefix: Str,
    outerTl: TL,
  ): TraceLogger =
    new TraceLogger(using outerTl.debugPrinter):
      override def doTrace: Bool = scope match
        case S(TraceScope.NonAffineSyms) => cfg.logNonAffine
        case S(TraceScope.AccumulatorSym) => cfg.logAccumulator
        case _ => cfg.debug

      override def emitDbg(str: Str): Unit =
        outerTl.emitDbg(s"$prefix$str")
    
end FlowAnalysis


class ResultId(val uid: Uid[Result]):
  override def toString: String = uid.toString

type InstantiationId = Ls[ResultId]
type CtorCls = ClassLikeSymbol | Int
type SelField = TermSymbol | Int
type FunId = (funSym: TermSymbol, whichParamList: Int) | ResultId
type OriginId = ResultId | FunId


object TrackableFieldSelect:
  def unapply(s: Select): Opt[Path -> (field: TermSymbol, owner: ClassSymbol)] =
    s.symbol match
    case S(sSym) if sSym.asTrm.exists(_.decl.exists(_.isInstanceOf[Param])) =>
      val tSym = sSym.asTrm.get
      for
        owner <- tSym.owner
        cls <- owner.asCls
        if cls.tree.clsParams.size === 1
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
      target ->
      locally:
        p match
          case Select(qual, _) => S(qual)
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

type StratVarId = Uid[StratVar]

sealed trait ProdStrat
sealed trait ConsStrat

class StratVar(val uid: StratVarId, val name: Str, val generatedForFun: Opt[TermSymbol])
  extends ProdStrat with ConsStrat:
  val upperBounds = LinkedHashSet.empty[ConsStrat]
  val lowerBounds = LinkedHashSet.empty[ProdStrat]
  lazy val asIntoParam = new StratVar.IntoParamImpl(this)
  lazy val asPossibleAccumulator = new StratVar.PossibleAccumulatorImpl(this)
  override def toString(): String = s"${if name.isEmpty() then "$stratvar" else name}@${uid}@$generatedForFun"

object StratVar:
  final class IntoParamImpl private[StratVar] (val s: StratVar) extends ConsStrat:
    override def toString(): String = s"IntoParam($s)"
  final class PossibleAccumulatorImpl private[StratVar] (val s: StratVar) extends ConsStrat:
    override def toString(): String = s"PossibleAccumulator($s)"
  
  def freshVar(nme: String)(using vuid: Uid.StratVar.State, fState: FlowAnalysis.State): StratVar =
    val newId = vuid.nextUid
    val stratVar = StratVar(newId, nme, N)
    fState.stratVars += stratVar
    stratVar
  def freshVar(nme: String, generatedForFun: TermSymbol)(using vuid: Uid.StratVar.State, fState: FlowAnalysis.State): StratVar =
    val newId = vuid.nextUid
    val stratVar = StratVar(newId, s"${nme}_for_${generatedForFun.nme}", S(generatedForFun))
    fState.stratVars += stratVar
    stratVar
  def freshVar(nme: String, forFunOpt: Opt[TermSymbol])(using vuid: Uid.StratVar.State, fState: FlowAnalysis.State): StratVar =
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

sealed trait ConcreteCtorConsumer extends StratWithOrigin[ResultId]:
  val srcs = MutSet.empty[Ctor | MarkerProdStrat]

class ProdFun(
  val exprId: FunId,
  val instantiationId: Opt[InstantiationId]
)(
  val params: Ls[ConsStrat],
  val restParam: Opt[ConsStrat],
  val res: ProdStrat,
  val capturedVarUpperbound: StratVar
) extends ProdStrat with StratWithOrigin[FunId]:
  val dests = MutSet.empty[ConsFun | MarkerConsStrat]
  override def toString(): String =
    s"(${params.map(_.toString()).mkString(", ")}) -> ${res.toString()}"

case object UnknownProd extends MarkerProdStrat

class Ctor(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val ctor: CtorCls,
  val args: Ls[SelField -> ProdStrat]
) extends ProdStrat with StratWithOrigin[ResultId]:
  val dests = MutSet.empty[ConcreteCtorConsumer | MarkerConsStrat]
  override def toString(): String =
    s"$ctor(${args.map(_.toString()).mkString(", ")})"


class ConsFun(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val params: Ls[ProdStrat],
  val res: ConsStrat
) extends ConsStrat with StratWithOrigin[ResultId]:
  val srcs = MutSet.empty[ProdFun | MarkerProdStrat]
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
    case r: ResultId => s"${r.getResult}"



class ProdStratScheme(val s: StratVar, val constraints: Ls[ProdStrat -> ConsStrat])

class FlowPreAnalyzer(val pgrm: Program)(using
  val tl: TraceLogger,
  val eState: Elaborator.State,
  val fState: FlowAnalysis.State,
  val raise: Raise,
  val symbolPrinter: SymbolPrinter
) extends BlockTraverser:
  given stratVarUidState: Uid.StratVar.State = new Uid.StratVar.State
  import StratVar.freshVar
  
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
    val funSymToFunDefn = MutMap.empty[TermSymbol, FunDefn]
    val matchScrutToMatchBlock = MutMap.empty[ResultId, Match]
    val labelSymToLabelBlk = MutMap.empty[Symbol, Label]
    val matchScrutToCtxOfMatch = MutMap.empty[ResultId, Ls[InCtx]]
    val labelSymToCtxOfLabel = MutMap.empty[Symbol, Ls[InCtx]]
    val selToCtxOfSel = MutMap.empty[ResultId, Ls[InCtx]]
    val modSymToBms = MutMap.empty[Symbol, BlockMemberSymbol]
    val generatedVars = MutMap.empty[Symbol, StratVar]
    val capturedVars = MutMap.empty[TermSymbol | ResultId, LinkedHashSet[Symbol]]
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
      res.generatedVars.getOrElseUpdate(sym, freshVar(nme, currentRootFun))
    
    private inline def withCtx(newCtx: InCtx)(inline body: => Any)(after: => Unit = ()): Unit =
      ctx = newCtx :: ctx
      body
      ctx = ctx.tail
      after
    
    inline def inMod(mod: ClsLikeBody)(inline body: => Any) =
      withCtx(InCtx.Mod(mod))(body)()
    
    inline def inFun(fun: FunDefn)(inline body: => Any) =
      val locallyDefined = MutSet.empty[Symbol]
      locallyDefined += fun.sym
      locallyDefined += fun.dSym
      for pl <- fun.params do
        pl.params.foreach(p => locallyDefined += p.sym)
        pl.restParam.foreach(p => locallyDefined += p.sym)
      withCtx(InCtx.Fn(fun))(withCaptureInfo(fun.dSym, locallyDefined)(body)):
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
      lam.params.params.foreach(p => locallyDefined += p.sym)
      lam.params.restParam.foreach(p => locallyDefined += p.sym)
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

  private def withCaptureInfo(owner: TermSymbol | ResultId, locallyDefined: MutSet[Symbol])(body: => Any): Unit =
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
    case Throw(exc) => applyResult(exc)
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
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
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
    case DynSelect(qual, fld, arrayIdx) =>
      applyPath(qual); applyPath(fld)
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
    case p: Select =>
      super.applyPath(p)
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
    currentCaptureInfo.foreach(_.locallyDefined += defn.tsym)
    applyPath(defn.rhs)
  
  override def applyParamList(pl: ParamList): Unit =
    pl.params.foreach(p => ctxTracker.registerStratVar(p.sym, p.sym.nme))
    pl.restParam.foreach(p => ctxTracker.registerStratVar(p.sym, p.sym.nme))
  
  override def applyArg(arg: Arg): Unit =
    applyPath(arg.value)
  
  override def applyDefn(defn: Defn): Unit = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case defn: ValDefn => applyValDefn(defn)
    case cls@ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    =>
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
  given Uid.StratVar.State = preAnalyzer.stratVarUidState
  given Raise = preAnalyzer.raise
  given fState: FlowAnalysis.State = preAnalyzer.fState
  given eState: Elaborator.State = preAnalyzer.eState
  given tl: TraceLogger = preAnalyzer.tl
  import StratVar.freshVar
  
  private class ConstraintsCollector(val forFunGroup: Opt[TermSymbol]):
    var constraints = Ls.empty[ProdStrat -> ConsStrat]
    val instId: Opt[InstantiationId] = forFunGroup.fold(S(Nil))(_ => N)
    def constrain(p: ProdStrat, c: ConsStrat) = constraints ::= p -> c
    def constrain(cs: Iterable[ProdStrat -> ConsStrat]) = constraints :::= cs.toList
  
  private val globalCollector = new ConstraintsCollector(N)
  def allConstraints = globalCollector.constraints
  val funToSccGroups = MutMap.empty[TermSymbol, Ls[TermSymbol]]
  def funToSccRep(tSym: TermSymbol): Option[TermSymbol] = funToSccGroups.get(tSym).map(_.head)
  
  // for fusing strictly internal parts of functions
  val synthesizedInstIdToFunSym = LinkedHashMap.empty[InstantiationId, TermSymbol]
  private val generatedVars: collection.Map[Symbol, StratVar] =
    preAnalyzer.res.generatedVars.withDefaultValue(preAnalyzer.res.primitiveStratVar)
  
  locally {
    val funsToProdStratScheme = MutMap.empty[TermSymbol, ProdStratScheme]

    if !mono then
      // Computing the ProdStratScheme for each scc group, this way the sccs of the call graph is
      // never materialized
      object ProdStratSchemeAnalysisInScc extends SccAnalysis[TermSymbol]:
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
        protected def isHandled(f: TermSymbol) = funsToProdStratScheme.contains(f)
        protected def handleScc(groupedFuns: Ls[TermSymbol], sccId: Int): Unit =
          for f <- groupedFuns do funToSccGroups(f) = groupedFuns
          val groupRep = groupedFuns.head
          new ConstraintsCollector(Some(groupRep)).givenIn: cc ?=>
            for funSym <- groupedFuns do
              val fun = preAnalyzer.res.funSymToFunDefn(funSym)
              val thisFunVar = generatedVars(fun.dSym)
              val funProdStrat = mkFunProdStrat(
                s"${funSym.nme}_res",
                fun.params,
                fun.body,
                (fun.dSym, -1))
              cc.constrain(funProdStrat, thisFunVar)
            if nonAffineTracking then
              for
                sym <- preAnalyzer.res.nonAffineSyms
                stratVar <- preAnalyzer.res.generatedVars.get(sym)
                if stratVar.generatedForFun.flatMap(funToSccRep).contains(groupRep)
              do cc.constrain(stratVar, NonAffine)
            for funSym <- groupedFuns do
              funsToProdStratScheme(funSym) = ProdStratScheme(generatedVars(funSym), cc.constraints)
      end ProdStratSchemeAnalysisInScc
      
      ProdStratSchemeAnalysisInScc.queryAll(preAnalyzer.res.rootFunDefns.keys)
    end if

    // collect constraints from the top-level block
    globalCollector.givenIn: cc ?=>
      cc.constrain(preAnalyzer.res.primitiveStratVar, UnknownCons)
      cc.constrain(UnknownProd, preAnalyzer.res.primitiveStratVar)
      processBlock(preAnalyzer.pgrm.main)(using cc, UnknownCons)

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

      if mono then
        for
          (_, fun) <- preAnalyzer.res.rootFunDefns
          if fun.visibility is Visibility.Public
        do
          cc.constrain(generatedVars(fun.dSym), UnknownCons)
      else
        for (funSym, fun) <- preAnalyzer.res.rootFunDefns do
          val pScheme = funsToProdStratScheme(funSym)
          val synthesizedRefUid =
            preAnalyzer.res.funSymToFunDefn(funSym).sym.asMemberRef(funSym).uid
          val selfProd = pScheme.instantiate(synthesizedRefUid, funSym)
          cc.constrain(selfProd, UnknownCons)
          val selfInstId = synthesizedRefUid :: Nil
          synthesizedInstIdToFunSym(selfInstId) = funSym
    
    // =========================
    
    extension (pScheme: ProdStratScheme) def instantiate(
      referSite: ResultId,
      referringTo: TermSymbol
    )(using cc: ConstraintsCollector): StratVar =
      val groupRep: TermSymbol = funToSccRep(referringTo).get
      val stratVarMap = MutMap.empty[StratVar, StratVar]
      def updateInstantiationId(instId: Opt[InstantiationId]) =
        S(instId.fold(referSite :: Nil)(referSite :: _))
      def duplicateVarState(s: StratVar) =
        if s.generatedForFun.fold(false):
          forFun => funToSccRep(forFun).fold(false)(_ is groupRep)
        then stratVarMap.getOrElseUpdate(s, freshVar(s.name, cc.forFunGroup))
        else s
      def duplicateProdStrat(s: ProdStrat): ProdStrat = s match
        case v: StratVar => duplicateVarState(v)
        case p: ProdFun =>
          new ProdFun(p.exprId, updateInstantiationId(p.instantiationId))(
            p.params.map(duplicateConsStrat),
            p.restParam.map(duplicateConsStrat),
            duplicateProdStrat(p.res),
            duplicateVarState(p.capturedVarUpperbound))
        case UnknownProd => UnknownProd
        case c: Ctor => new Ctor(c.exprId, updateInstantiationId(c.instantiationId))(
          c.ctor,
          c.args.map((a, b) => a -> duplicateProdStrat(b)))
      def duplicateConsStrat(c: ConsStrat): ConsStrat = c match
        case v: StratVar => duplicateVarState(v)
        case c: ConsFun =>
          new ConsFun(c.exprId, updateInstantiationId(c.instantiationId))(
            c.params.map(duplicateProdStrat),
            duplicateConsStrat(c.res))
        case UnknownCons => UnknownCons
        case NonAffine => NonAffine
        case Accumulator => Accumulator
        case pAcc: PossibleAccumulator => duplicateVarState(pAcc.s).asPossibleAccumulator
        case iPrm: IntoParam => duplicateVarState(iPrm.s).asIntoParam
        case fSel: FieldSel =>
          new FieldSel(fSel.exprId, updateInstantiationId(fSel.instantiationId))(
            fSel.field,
            fSel.selectsFrom,
            duplicateVarState(fSel.consVar))
        case dtor: Dtor => new Dtor(dtor.exprId, updateInstantiationId(dtor.instantiationId))
      val newProd = duplicateVarState(pScheme.s)
      pScheme.constraints.foreach: (p, c) =>
        cc.constrain(duplicateProdStrat(p), duplicateConsStrat(c))
      newProd
    
    extension (v: StratVar)
      def constrainOpaque(using cc: ConstraintsCollector): Unit =
        cc.constrain(UnknownProd, v)
        cc.constrain(v, UnknownCons)
    
    def mkFunProdStrat(
      resName: String,
      params: Ls[ParamList],
      body: Block,
      funLamId: FunId
    )(using cc: ConstraintsCollector): ProdStrat =
      def paramListFunId(whichParamList: Int): FunId =
        funLamId match
          case (sym: TermSymbol, -1) => (sym, whichParamList)
          case lambdaExprId: ResultId =>
            assert(whichParamList == 0)
            lambdaExprId
          case other => lastWords(s"unexpected funLamId shape: $other")
      val capturedSyms = funLamId match
        case (sym: TermSymbol, _) => preAnalyzer.res.capturedVars(sym)
        case lamExprId: ResultId => preAnalyzer.res.capturedVars(lamExprId)
        case other => lastWords(s"unexpected funLamId shape: $other")
      val res = freshVar(resName, cc.forFunGroup)
      params.foreach:
        _.restParam.foreach: p =>
          generatedVars(p.sym).constrainOpaque
      val funValueStrat = params.zipWithIndex.foldRight[ProdStrat](res):
        case ((ps, whichParamList), acc) =>
          val plFunId = paramListFunId(whichParamList)
          val capUB = freshVar(s"cap_ub_$plFunId", cc.forFunGroup)
          for
            v <- capturedSyms
            capturedSymStrat <- generatedVars.get(v)
          do
            cc.constrain(capturedSymStrat, capUB)
          new ProdFun(plFunId, cc.instId)(
            ps.params.map(p => generatedVars(p.sym)),
            ps.restParam.map(p => generatedVars(p.sym)),
            acc,
            capUB)
      processBlock(body)(using cc, res)
      funValueStrat

    def processFunctionDefn(fun: FunDefn)(using cc: ConstraintsCollector): Unit =
      if mono || !preAnalyzer.res.rootFunDefns.contains(fun.dSym) then
        val funProdStrat = mkFunProdStrat(
          s"${fun.dSym.nme}_res",
          fun.params,
          fun.body,
          (fun.dSym, -1))
        cc.constrain(funProdStrat, generatedVars(fun.dSym))
    
    def processClsLikeDefn(cls: ClsLikeDefn)(using cc: ConstraintsCollector): Unit =
      cls.privateFields.foreach(sym => generatedVars(sym).constrainOpaque)
      cls.publicFields.foreach: (_, tsym) =>
        generatedVars(tsym).constrainOpaque
      cls.methods.foreach: fun =>
        processBlock(fun.body)(using cc, UnknownCons)
      processBlock(cls.preCtor)(using cc, UnknownCons)
      processBlock(cls.ctor)(using cc, UnknownCons)
      cls.companion.foreach: mod =>
        mod.privateFields.foreach(sym => generatedVars(sym).constrainOpaque)
        mod.publicFields.foreach: (_, tsym) =>
          generatedVars(tsym).constrainOpaque
        mod.methods.foreach: fun =>
          processFunctionDefn(fun)
        processBlock(mod.ctor)(using cc, UnknownCons)
    
    def constrainOpaqueResult(r: Result)(using cc: ConstraintsCollector): Unit =
      cc.constrain(processResult(r), UnknownCons)

    def processBlock(b: Block)(using cc: ConstraintsCollector, blkRes: ConsStrat): Unit =
      val instId = cc.instId
      b match
      case Return(res) => cc.constrain(processResult(res), blkRes)
      case Throw(exc) => constrainOpaqueResult(exc)
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
          case lhs: (LocalVarSymbol | TermSymbol) => cc.constrain(rhsStrat, generatedVars(lhs))
        processBlock(rest)
      case TryBlock(sub, finallyDo, rest) =>
        processBlock(sub)
        processBlock(finallyDo)
        processBlock(rest)
      case AssignField(lhs, nme, rhs, rest) =>
        constrainOpaqueResult(lhs)
        constrainOpaqueResult(rhs)
        processBlock(rest)
      case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
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
          processFunctionDefn(fun)
        case cls: ClsLikeDefn =>
          processClsLikeDefn(cls)
        processBlock(rest)
      case End(msg) => ()
      case Unreachable(_) => ()
    
    def processResult(r: Result)(using cc: ConstraintsCollector): ProdStrat =
      val instId = cc.instId
      def handleCallLike(callExprId: ResultId, f: Path, args: List[Arg]): ProdStrat =
        val fStrat = processResult(f)
        val argsStrat = args.map(a => processResult(a.value))
        if args.exists(_.spread.isDefined) then
          cc.constrain(fStrat, UnknownCons)
          argsStrat.foreach(arg => cc.constrain(arg, UnknownCons))
          UnknownProd
        else
          val callRes = freshVar("call_res", cc.forFunGroup)
          cc.constrain(fStrat, new ConsFun(callExprId, instId)(argsStrat, callRes))
          callRes
      r match
        case sel@TrackableSelect(from, field, owner) =>
          val fromStrat = processResult(from)
          val selRes = freshVar("sel_res", cc.forFunGroup)
          cc.constrain(
            fromStrat,
            new FieldSel(sel.uid, instId)(field, owner, selRes))
          selRes
        case c@CtorProducer(ctor, args, selectedFrom) if args.forall(_.spread.isEmpty) =>
          for qual <- selectedFrom do
            cc.constrain(processResult(qual), UnknownCons)
          val argsStrat = args.map:
            case Arg(_, a) => processResult(a)
          ctor match
          case cls: ClassSymbol =>
            cls.tree.clsParams.size match
            case 1 =>
              val clsParams = cls.tree.clsParams.head
              // TODO: properly check the parameter lists, which may change after passes like lifting
              // softTODO(argsStrat.size === clsParams.size, s"mismatched ctor arg and cls param sizes")
              new Ctor(c.uid, instId)(ctor, clsParams.zip(argsStrat))
            case _ =>
              // - the size of 0 means we don't know the cls param symbols,
              // so we constrain args with NoCons and this CtorProducer gives NoProd
              // - if size > 1, we cannot handle multiple parameter class flow now,
              //   constrain args with NoCons and this CtorProducer gives NoProd
              for a <- argsStrat do cc.constrain(a, UnknownCons)
              UnknownProd
          case _: ModuleOrObjectSymbol => new Ctor(c.uid, instId)(ctor, Nil)
          case tupSize: Int => new Ctor(c.uid, instId)(tupSize, (0 until tupSize).zip(argsStrat).toList)
        case c@CtorProducer(_, args, selectedFrom) =>
          for qual <- selectedFrom do
            cc.constrain(processResult(qual), UnknownCons)
          args.foreach(arg => cc.constrain(processResult(arg.value), UnknownCons))
          UnknownProd
        case c@Call(fun, argss) =>
          argss match
            case args :: Nil => handleCallLike(c.uid, fun, args)
            case args :: rest =>
              // For multi-arg-list calls, handle the first arg list normally for
              // dead-param-elim, then constrain subsequent arg lists opaquely.
              // We cannot reuse c.uid for subsequent ConsFuns because the
              // DeadParamElim rewriter only rewrites the first arg list,
              // and sharing the same exprId would cause conflicting eliminable sets.
              val firstResult = handleCallLike(c.uid, fun, args)
              cc.constrain(firstResult, UnknownCons)
              rest.foreach: nextArgs =>
                nextArgs.foreach(a => cc.constrain(processResult(a.value), UnknownCons))
              UnknownProd
        case i@Instantiate(_, cls, argss) => handleCallLike(i.uid, cls, argss.flatten)
        case lam@Lambda(ps, body) =>
          mkFunProdStrat("lam_res", ps :: Nil, body, lam.uid)
        case _: Tuple => lastWords("should be handled in CtorProducer")
        case Record(_, fields) =>
          fields.foreach:
            case RcdArg(idx, value) =>
              idx.foreach(p => cc.constrain(processResult(p), UnknownCons))
              cc.constrain(processResult(value), UnknownCons)
          UnknownProd
        case p: Path =>
          p match
          case refSite@FunRef(f, selectedFrom) =>
            for qual <- selectedFrom do
              cc.constrain(processResult(qual), UnknownCons)
            funsToProdStratScheme.get(f) match
            case Some(fScheme) =>
              fScheme.instantiate(refSite.uid, f)
            case None => generatedVars(f)
          case s@Select(qual, name) =>
            cc.constrain(processResult(qual), UnknownCons)
            s.symbol.fold(UnknownProd): selSym =>
              generatedVars(selSym)
          case DynSelect(qual, fld, arrayIdx) =>
            cc.constrain(processResult(qual), UnknownCons)
            cc.constrain(processResult(fld), UnknownCons)
            UnknownProd
          case Value.MemberRef(_, disamb) => generatedVars(disamb)
          case Value.SimpleRef(sym) => generatedVars(sym)
          case Value.This(_) => UnknownProd
          case Value.Lit(lit) => UnknownProd
  }
end FlowConstraintsCollector

class FlowConstraintSolver(val collector: FlowConstraintsCollector):
  given tl: TraceLogger = collector.tl
  given fState: FlowAnalysis.State = collector.fState
  given eState: Elaborator.State = collector.eState
  given preAnalyzer: FlowPreAnalyzer = collector.preAnalyzer
  given Raise = preAnalyzer.raise
  
  
  val ctorsWithDests = mutable.Buffer.empty[Ctor]
  val consumersWithSrcs = mutable.Buffer.empty[ConcreteCtorConsumer]
  val prodFunsWithDests = mutable.Buffer.empty[ProdFun]
  val consFunsWithSrcs = mutable.Buffer.empty[ConsFun]
  
  private def addCtorDest(c: Ctor, d: ConcreteCtorConsumer | MarkerConsStrat): Unit =
    if c.dests.isEmpty then ctorsWithDests += c
    c.dests += d
  private def addDtorSrc(d: ConcreteCtorConsumer, p: Ctor | MarkerProdStrat): Unit =
    if d.srcs.isEmpty then consumersWithSrcs += d
    d.srcs += p
  private def addFunDest(p: ProdFun, c: ConsFun | MarkerConsStrat): Unit =
    if p.dests.isEmpty then prodFunsWithDests += p
    p.dests += c
  private def addFunSrc(c: ConsFun, p: ProdFun | MarkerProdStrat): Unit =
    if c.srcs.isEmpty then consFunsWithSrcs += c
    c.srcs += p
  
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
    
  
  private def logNonAffineSyms: Unit =
    tl.scoped(FlowAnalysis.TraceScope.NonAffineSyms):
      tl.log(">>> non-affine syms >>>")
      val outputRes =
        for
          stratVar <- fState.stratVars
          if AllUpperBounds(stratVar).contains(NonAffine)
        yield s"${stratVar.name}@${stratVar.uid}"
      for nonAffine <- outputRes.toSortedSet do
        tl.log(nonAffine)
      tl.log("<<< non-affine syms <<<")
  
  private def logAccumulatorSyms: Unit =
    tl.scoped(FlowAnalysis.TraceScope.AccumulatorSym):
      tl.log(">>> accumulator syms >>>")
      def showAccumulatorSym(stratVar: StratVar): Opt[Str] =
        AllUpperBounds(stratVar)
          .collectFirst:
            case pAcc: PossibleAccumulator if pAcc.s is stratVar => s"${stratVar.name}@${stratVar.uid}"
            case iPrm: IntoParam if iPrm.s is stratVar => s"${stratVar.name}@${stratVar.uid}"
      val outputRes =
        for
          stratVar <- fState.stratVars
          if AllUpperBounds(stratVar).contains(Accumulator)
          accumulatorSym <- showAccumulatorSym(stratVar)
        yield accumulatorSym
      for accumulator <- outputRes.toSortedSet do
        tl.log(accumulator)
      tl.log("<<< accumulator syms <<<")
  
  locally {
    def hasConcreteInstantiationId(prodOrCons: ProdStrat | ConsStrat): Boolean = prodOrCons match
      case s: StratWithOrigin[?] => s.instantiationId.isDefined
      case _ => true
    def handle(constraint: ProdStrat -> ConsStrat): Unit =
      assert:
        val (prod, cons) = constraint
        hasConcreteInstantiationId(prod) &&
        hasConcreteInstantiationId(cons)
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
      case (p: ProdFun, UnknownCons) =>
        addFunDest(p, UnknownCons)
        for a <- p.params do handle(UnknownProd, a)
        p.restParam.foreach(r => handle(UnknownProd, r))
        handle(p.res, UnknownCons)
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
      case (p: StratVar, c: StratVar) =>
        if p.upperBounds.add(c) then
          for l <- p.lowerBounds do handle(l, c)
          for u <- c.upperBounds do handle(p, u)
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
    
    for c <- collector.allConstraints do handle(c)
  }
  
  logNonAffineSyms
  logAccumulatorSyms


end FlowConstraintSolver
