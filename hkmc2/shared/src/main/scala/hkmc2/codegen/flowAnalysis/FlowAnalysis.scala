package hkmc2
package codegen
package flowAnalysis

import scala.jdk.CollectionConverters.MapHasAsScala
import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, LinkedHashSet}


object FlowAnalysis:
  object TraceScope:
    val nonAffineSyms = "flow-analysis/non-affine"
    val accumulatorSyms = "flow-analysis/accumulator"

  class State:
    val resultToResultId = new java.util.IdentityHashMap[Result, Uid[Result]].asScala
    val resultIdToResult = mutable.Map.empty[Uid[Result], Result]
    val stratVarIdToState = mutable.Map.empty[StratVarId, StratVarState]
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
        resultId.getResult match
        case Value.Ref(s, _) => s
        case e => lastWords(s"assumption failed: $e is not a Value.Ref")
      def getReferredFun(using Elaborator.State): Option[TermSymbol] =
        resultId.getResult match
        case FunRef(f) => Some(f)
        case _ => None
    
    extension (r: Result)
      def uid = resultToResultId.get(r) match
        case None =>
          val id = ResultUidState.nextUid
          resultIdToResult(id) = r
          resultToResultId(r) = id
          id
        case Some(id) => id
  
  
  def apply(
    pgrm: Program,
    mono: Bool,
    nonAffineTracking: Bool,
    accumulatorTracking: Bool,
  )(using TraceLogger, Elaborator.State, Raise) =
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
        case S(TraceScope.nonAffineSyms) => cfg.logNonAffine
        case S(TraceScope.accumulatorSyms) => cfg.logAccumulator
        case _ => cfg.debug

      override def emitDbg(str: Str): Unit =
        outerTl.emitDbg(s"$prefix$str")
    
end FlowAnalysis


type ResultId = Uid[Result]
type InstantiationId = Ls[ResultId]
type CtorCls = ClassLikeSymbol | Int
type SelField = TermSymbol | Int
type FunId = (funSym: Symbol, whichParamList: Int) | ResultId
type OriginId = ResultId | FunId

object RefLike:
  private def classCtorSymbol(sym: Symbol)(using Elaborator.State): Opt[ClassSymbol | ModuleOrObjectSymbol] =
    sym.asObj orElse
    sym.asTrm.flatMap: tSym =>
      for
        cls <- tSym.owner.flatMap(_.asCls)
        clsDef <- cls.defn
        ctorSym <- clsDef.ctorSym
        if ctorSym is tSym
      yield
        cls
  
  def unapply(p: Value.Ref | Select)(using Elaborator.State): Opt[Symbol] =
    p match
      case Value.Ref(l, disamb) =>
        val sym = disamb.getOrElse(l)
        classCtorSymbol(sym) orElse S(sym)
      case s: Select =>
        s.symbol.flatMap: selSym =>
          classCtorSymbol(selSym) orElse
          locally:
            for
              selTermSym <- selSym.asTrm
              owner <- selTermSym.owner
              _ <- owner.asMod
            yield
              selTermSym

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
  def unapply(s: Result)(using eState: Elaborator.State): Opt[Value.Ref -> Int] =
    s match
    case Call(
      Select(Select(Value.Ref(runtimeSym, N), Tree.Ident("Tuple")), Tree.Ident("get")),
      Arg(N, ref@Value.Ref(scrut, N)) :: Arg(N, Value.Lit(Tree.IntLit(n))) :: Nil
    ) if runtimeSym is eState.runtimeSymbol => S(ref -> n.toInt)
    case _ => N

object TrackableSelect:
  def unapply(s: Result)(using pre: FlowPreAnalyzer, eState: Elaborator.State): Opt[(from: Path, field: SelField, owner: CtorCls)] =
    given fState: FlowAnalysis.State = pre.fState
    s match
    case sel@PossibleTrackableTupleSelect((ref@Value.Ref(scrut, N)) -> ith) =>
      pre.res.getEnclosingMatchesForSel(sel.uid).find(_._1.getReferredSym is scrut).flatMap:
        case (_, Some(tupSize: Int)) => S(ref, ith, tupSize)
        case _ => N
    case TrackableFieldSelect(qual, field -> owner) =>
      Some((qual, field, owner))
    case _ => N

object CtorRef:
  def unapply(s: Path)(using Elaborator.State): Option[ClassSymbol | ModuleOrObjectSymbol] =
    s match
      case RefLike(s) => s.asCls orElse s.asObj
      case _ => None

object CtorCall:
  def unapply(r: Result)(using Elaborator.State): Option[(ClassSymbol | ModuleOrObjectSymbol | Int) -> Ls[Arg]] =
    r match
    case Instantiate(_, CtorRef(ctor), args) => Some(ctor -> args)
    case Call(CtorRef(ctor), args) => Some(ctor -> args)
    case CtorRef(ctor) if ctor.asObj.isDefined => Some(ctor -> Nil)
    case Tuple(_, args) => Some(args.size, args)
    case _ => None

object FunRef:
  def unapply(s: Path)(using Elaborator.State): Option[TermSymbol] = s match
    case RefLike(tSym: TermSymbol) if tSym.k is syntax.Fun => Some(tSym)
    case _ => None

type StratVarId = Uid[StratVar]

class StratVarState(val uid: StratVarId, val name: Str, val generatedForFun: Opt[TermSymbol]):
  lazy val asProdStrat = ProdVar(this)
  lazy val asConsStrat = ConsVar(this)
  override def toString(): String = s"${if name.isEmpty() then "$stratvar" else name}@${uid}@$generatedForFun"

object StratVarState:
  def freshVar(nme: String)(using vuid: Uid.StratVar.State, fState: FlowAnalysis.State): StratVarState =
    val newId = vuid.nextUid
    val stratVar = StratVarState(newId, nme, N)
    fState.stratVarIdToState(newId) = stratVar
    stratVar
  def freshVar(nme: String, generatedForFun: TermSymbol)(using vuid: Uid.StratVar.State, fState: FlowAnalysis.State): StratVarState =
    val newId = vuid.nextUid
    val stratVar = StratVarState(newId, s"${nme}_for_${generatedForFun.nme}", S(generatedForFun))
    fState.stratVarIdToState(newId) = stratVar
    stratVar
  def freshVar(nme: String, forFunOpt: Opt[TermSymbol])(using vuid: Uid.StratVar.State, fState: FlowAnalysis.State): StratVarState =
    forFunOpt match
    case None => freshVar(nme)
    case Some(forFun) => freshVar(nme, forFun)

trait StratVar(s: StratVarState):
  this: ProdVar | ConsVar =>
  def asProdStrat = s.asProdStrat
  def asConsStrat = s.asConsStrat
  def uid = s.uid

sealed abstract class ProdStrat
sealed abstract class ConsStrat

sealed trait StratWithOrigin[A <: OriginId]:
  def exprId: A
  def instantiationId: Opt[InstantiationId]
  def concreteId: ConcreteId[A] = ConcreteId(exprId, instantiationId.get)

sealed trait MarkerProdStrat extends ProdStrat
sealed trait MarkerConsStrat extends ConsStrat

case class ProdVar(s: StratVarState) extends ProdStrat with StratVar(s)

class ProdFun(
  val exprId: FunId,
  val instantiationId: Opt[InstantiationId]
)(
  val params: Ls[ConsStrat],
  val restParam: Opt[ConsStrat],
  val res: ProdStrat,
  val capturedVarUpperbound: ProdVar
) extends ProdStrat with StratWithOrigin[FunId]:
  override def toString(): String =
    s"(${params.map(_.toString()).mkString(", ")}) -> ${res.toString()}"

case object NoProd extends MarkerProdStrat

class Ctor(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val ctor: CtorCls,
  val args: Ls[SelField -> ProdStrat]
) extends ProdStrat with StratWithOrigin[ResultId]:
  override def toString(): String =
    s"$ctor(${args.map(_.toString()).mkString(", ")})"


case class ConsVar(s: StratVarState) extends ConsStrat with StratVar(s)

class ConsFun(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val params: Ls[ProdStrat],
  val res: ConsStrat
) extends ConsStrat with StratWithOrigin[ResultId]:
  override def toString(): String =
    s"(${params.map(_.toString()).mkString(", ")}) -> ${res.toString()}"

case object NoCons extends MarkerConsStrat

case object NonAffine extends MarkerConsStrat

case object Accumulator extends MarkerConsStrat

case class IntoParam(s: StratVarState) extends ConsStrat

case class PossibleAccumulator(s: StratVarState) extends ConsStrat


class FieldSel(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val field: SelField,
  val selectsFrom: CtorCls,
  val consVar: ConsVar
) extends ConsStrat with StratWithOrigin[ResultId]

class Dtor(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
) extends ConsStrat with StratWithOrigin[ResultId]

case class ConcreteId[A <: OriginId](exprId: A, instId: InstantiationId):
  def pp(using FlowAnalysis.State): Str = exprId match
    case (sym: Symbol, idx: Int) => s"${sym.nme}#$idx"
    case r: ResultId => s"${r.getResult}"


type ConcreteProducer = Ctor
type ConcreteConsumer = Dtor | FieldSel

class ProdStratScheme(val s: StratVarState, val constraints: Ls[ProdStrat -> ConsStrat])

class FlowPreAnalyzer(val pgrm: Program)(using
  val tl: TraceLogger,
  val eState: Elaborator.State,
  val fState: FlowAnalysis.State,
  val raise: Raise
) extends BlockTraverser:
  given stratVarUidState: Uid.StratVar.State = new Uid.StratVar.State
  import StratVarState.freshVar
  
  private case class CaptureTrackingInfo(
    locallyDefined: MutSet[Symbol],
    captured: LinkedHashSet[Symbol],
    outer: Opt[CaptureTrackingInfo]
  )
  private var currentCaptureFrame: Opt[CaptureTrackingInfo] = N
  private var currentAffinityCount = res.affinityCounts
  
  
  ctxTracker.inTopLvl:
    applyBlock(pgrm.main)
  
  object res:
    val primitiveStratVar = StratVarState.freshVar("unknown")
    val rootFunDefns = LinkedHashMap.empty[TermSymbol, FunDefn]
    val funSymToFunDefn = MutMap.empty[TermSymbol, FunDefn]
    val matchScrutToMatchBlock = MutMap.empty[ResultId, Match]
    val labelSymToLabelBlk = MutMap.empty[Symbol, Label]
    val matchScrutToCtxOfMatch = MutMap.empty[ResultId, Ls[InCtx]]
    val labelSymToCtxOfLabel = MutMap.empty[Symbol, Ls[InCtx]]
    val selToCtxOfSel = MutMap.empty[ResultId, Ls[InCtx]]
    val modSymToBms = MutMap.empty[Symbol, BlockMemberSymbol]
    val generatedProdVars = MutMap.empty[Symbol, StratVarState]
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
      res.generatedProdVars.getOrElseUpdate(sym, freshVar(nme, currentRootFun))
    
    private inline def withCtx(newCtx: InCtx)(inline body: => Any)(after: => Unit = ()): Unit =
      ctx = newCtx :: ctx
      body
      ctx = ctx.tail
      after
    
    inline def inMod(mod: ClsLikeBody)(inline body: => Any) =
      withCtx(InCtx.Mod(mod))(body)()
    
    inline def inFun(fun: FunDefn)(inline body: => Any) =
      withCtx(InCtx.Fn(fun))(body):
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
          case Value.Ref(s, disamb) => disamb.getOrElse(s) is sym
          case _ => false
        case _ => false
    
    inline def inBeginBody(begin: Begin)(inline body: => Any) =
      withCtx(InCtx.BegnBody(begin))(body)()
    
    inline def inScoped(scpd: Scoped)(inline body: => Any) =
      withCtx(InCtx.Scped(scpd))(body)()
    
    inline def inLam(lam: Lambda)(inline body: => Any) =
      withCtx(InCtx.Lam(lam))(body)()
    
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
  
  private def recordAffinityUse(l: Symbol, disamb: Opt[DefinitionSymbol[?]]): Unit =
    def isClassCtorSym(sym: Symbol): Bool =
      sym.asTrm.exists: tSym =>
        tSym.owner
          .flatMap(_.asCls)
          .flatMap(_.defn)
          .flatMap(_.ctorSym)
          .exists(_ is tSym)
    val processedSymbol =
      disamb.getOrElse(l) match
      case _: NoSymbol | _: LabelSymbol | _: BuiltinSymbol => N
      case _: ClassSymbol | _: ModuleOrObjectSymbol | _: PatternSymbol | _: TypeAliasSymbol => N
      case _: TopLevelSymbol => N
      case sym: TermSymbol =>
        if isClassCtorSym(sym) then N else S(sym)
      case bms: BlockMemberSymbol =>
        if bms.asCls.nonEmpty || bms.asModOrObj.nonEmpty || bms.asPat.nonEmpty || bms.asAls.nonEmpty
        then N
        else
          val trmOrBms = bms.asTrm.getOrElse(bms)
          if isClassCtorSym(trmOrBms) then N else S(trmOrBms)
      case sym => S(sym)
    processedSymbol.foreach: sym =>
      currentAffinityCount(sym) = currentAffinityCount(sym) + 1

  private def recordRefInCaptures(l: Symbol): Unit =
    currentCaptureFrame.foreach: frame =>
      if !frame.locallyDefined.contains(l) then
        frame.captured += l

  private def inCaptureFrame(owner: TermSymbol | ResultId, locallyDefined: MutSet[Symbol])(body: => Unit): Unit =
    val frame = CaptureTrackingInfo(locallyDefined, LinkedHashSet.empty, currentCaptureFrame)
    currentCaptureFrame = S(frame)
    body
    currentCaptureFrame = frame.outer
    currentCaptureFrame.foreach: outer =>
      outer.captured ++= frame.captured.iterator.filterNot(outer.locallyDefined.contains)
    res.capturedVars(owner) = frame.captured
  
  override def applyBlock(b: Block): Unit = b match
    case scpd@Scoped(syms, body) =>
      for s <- syms do
        s match
        case s: BlockMemberSymbol => ()
        case _ => ctxTracker.registerStratVar(s, s.nme)
      val CaptureTrackingInfo = currentCaptureFrame
      CaptureTrackingInfo.foreach(_.locallyDefined ++= syms)
      ctxTracker.inScoped(scpd):
        applyBlock(body)
      CaptureTrackingInfo.foreach(_.locallyDefined --= syms)
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
    case Return(res, implct) => applyResult(res)
    case lbl@Label(label, loop, body, rest) =>
      ctxTracker.inLabelBody(lbl):
        applyBlock(body)
      applyBlock(rest)
    case bgn@Begin(sub, rest) =>
      ctxTracker.inBeginBody(bgn):
        applyBlock(sub)
      applyBlock(rest)
    case Assign(lhs, rhs, rest) =>
      recordRefInCaptures(lhs)
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
    case HandleBlock(local, res, par, args, cls, hdr, bod, rst) =>
      applyPath(par)
      args.foreach(applyPath)
      hdr.foreach(applyHandler)
      applyBlock(bod)
      applyBlock(rst)
    case End(_) => ()
    case Unreachable(_) => ()
  
  override def applyResult(r: Result): Unit = r match
    case tupSel@PossibleTrackableTupleSelect(_, _) =>
      res.selToCtxOfSel.addOne(tupSel.uid -> ctxTracker.getAllCtx)
    case Call(fun, args) =>
      applyPath(fun)
      args.foreach(applyArg)
    case Instantiate(mut, cls, args) =>
      applyPath(cls)
      args.foreach(applyArg)
    case l: Lambda =>
      applyLam(l)
    case Tuple(mut, elems) =>
      elems.foreach(applyArg)
    case Record(_, fields) =>
      fields.foreach:
        case RcdArg(idx, value) => idx.foreach(applyPath); applyPath(value)
    case p: Path => applyPath(p)
  
  override def applyPath(p: Path): Unit = p match
    case DynSelect(qual, fld, arrayIdx) =>
      applyPath(qual); applyPath(fld)
    case p@TrackableFieldSelect(qual, _ -> _) =>
        res.selToCtxOfSel.addOne(p.uid -> ctxTracker.getAllCtx)
        qual match
          case Value.Ref(l, disamb)
            if ctxTracker.isEnclosingMatchScrutSym(disamb.getOrElse(l)) =>
              recordRefInCaptures(disamb.getOrElse(l))
          case _ => applyPath(qual)
    case p: Select =>
      super.applyPath(p)
    case v: Value => applyValue(v)
  
  override def applyValue(v: Value): Unit = v match
    case Value.Ref(l, disamb) =>
      recordRefInCaptures(disamb.getOrElse(l))
      recordAffinityUse(l, disamb)
    case Value.This(sym) => ()
    case Value.Lit(lit) => ()
  
  override def applyFunDefn(fun: FunDefn): Unit =
    val scope = MutSet.empty[Symbol]
    scope += fun.sym
    scope += fun.dSym
    for pl <- fun.params do
      pl.params.foreach(p => scope += p.sym)
      pl.restParam.foreach(p => scope += p.sym)
    ctxTracker.inFun(fun):
      inCaptureFrame(fun.dSym, scope):
        ctxTracker.registerStratVar(fun.dSym, fun.sym.nme)
        fun.params.foreach(applyParamList)
        applyBlock(fun.body)
  
  override def applyLam(lam: Lambda): Unit =
    val scope = MutSet.empty[Symbol]
    lam.params.params.foreach(p => scope += p.sym)
    lam.params.restParam.foreach(p => scope += p.sym)
    ctxTracker.inLam(lam):
      inCaptureFrame(lam.uid, scope):
        applyParamList(lam.params)
        applyBlock(lam.body)
  
  override def applyValDefn(defn: ValDefn): Unit =
    ctxTracker.registerStratVar(defn.tsym, defn.tsym.nme)
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
  import StratVarState.freshVar
  
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
  private val generatedProdVars: collection.Map[Symbol, StratVarState] =
    preAnalyzer.res.generatedProdVars.withDefaultValue(preAnalyzer.res.primitiveStratVar)
  
  locally {
    val funsToProdStratScheme = MutMap.empty[TermSymbol, ProdStratScheme]

    if !mono then
      // compute scc
      val sccInOrder: Ls[Ls[TermSymbol]] =
        import algorithms.partitionScc
        var edges = Ls.empty[(TermSymbol, TermSymbol)]
        for (_, f) <- preAnalyzer.res.rootFunDefns do
          object CollectAllReferredFun extends BlockTraverser:
            override def applyPath(p: Path) = p match
              case FunRef(callee) =>
                if preAnalyzer.res.rootFunDefns.contains(callee) then
                  edges = (f.dSym -> callee) :: edges
              case _ => ()
          CollectAllReferredFun.applyBlock(f.body)
        partitionScc(
          edges,
          preAnalyzer.res.rootFunDefns.keys
        ).reverse
      end sccInOrder
      for
        group <- sccInOrder
        f <- group
      do funToSccGroups(f) = group

      // compute strat scheme for each scc group
      for groupedFuns <- sccInOrder do
        val groupRep = funToSccRep(groupedFuns.head).get
        (new ConstraintsCollector(Some(groupRep))).givenIn: cc ?=>
          for funSym <- groupedFuns do
            val fun = preAnalyzer.res.funSymToFunDefn(funSym)
            val thisFunVar = generatedProdVars(fun.dSym)
            val funProdStrat = processHandleableFun(
              s"${funSym.nme}_res",
              fun.params,
              fun.body,
              (fun.dSym, -1))
            cc.constrain(funProdStrat, thisFunVar.asConsStrat)
          if nonAffineTracking then
            for
              sym <- preAnalyzer.res.nonAffineSyms
              stratVar <- preAnalyzer.res.generatedProdVars.get(sym)
              if stratVar.generatedForFun.flatMap(funToSccRep).contains(groupRep)
            do cc.constrain(stratVar.asProdStrat, NonAffine)
          for funSym <- groupedFuns do
            funsToProdStratScheme(funSym) = ProdStratScheme(generatedProdVars(funSym), cc.constraints)
    end if

    // collect constraints from the top-level block
    globalCollector.givenIn: cc ?=>
      cc.constrain(preAnalyzer.res.primitiveStratVar.asProdStrat, NoCons)
      cc.constrain(NoProd, preAnalyzer.res.primitiveStratVar.asConsStrat)
      processBlock(preAnalyzer.pgrm.main)(using cc, NoCons)

      // emit NonAffine for non-affine syms that don't belong to any scc:
      // in mono mode there are no SCC collectors, so all go here;
      // in poly mode, only syms with no root fun are emitted here,
      // the rest were emitted inside their owning SCC's scheme collector above
      if nonAffineTracking then
        for
          sym <- preAnalyzer.res.nonAffineSyms
          stratVar <- preAnalyzer.res.generatedProdVars.get(sym)
          if mono || stratVar.generatedForFun.isEmpty
        do cc.constrain(stratVar.asProdStrat, NonAffine)

      if mono then
        for
          (_, fun) <- preAnalyzer.res.rootFunDefns
          if fun.visibility is Visibility.Public
        do
          cc.constrain(generatedProdVars(fun.dSym).asProdStrat, NoCons)
      else
        for (funSym, fun) <- preAnalyzer.res.rootFunDefns do
          val pScheme = funsToProdStratScheme(funSym)
          val synthesizedRefUid =
            Value.Ref(preAnalyzer.res.funSymToFunDefn(funSym).sym, S(funSym)).uid
          val selfProd = pScheme.instantiate(synthesizedRefUid, funSym)
          cc.constrain(selfProd, NoCons)
          val selfInstId = synthesizedRefUid :: Nil
          synthesizedInstIdToFunSym(selfInstId) = funSym
    
    // =========================
    
    extension (pScheme: ProdStratScheme) def instantiate(
      referSite: ResultId,
      referringTo: TermSymbol
    )(using cc: ConstraintsCollector): ProdVar =
      val groupRep: TermSymbol = funToSccRep(referringTo).get
      val stratVarMap = MutMap.empty[StratVarState, StratVarState]
      def updateInstantiationId(instId: Opt[InstantiationId]) =
        S(instId.fold(referSite :: Nil)(referSite :: _))
      def duplicateVarState(s: StratVarState) =
        if s.generatedForFun.fold(false):
          forFun => funToSccRep(forFun).fold(false)(_ is groupRep)
        then stratVarMap.getOrElseUpdate(s, freshVar(s.name, cc.forFunGroup))
        else s
      def duplicateProdStrat(s: ProdStrat): ProdStrat = s match
        case ProdVar(s) => duplicateVarState(s).asProdStrat
        case p: ProdFun =>
          new ProdFun(p.exprId, updateInstantiationId(p.instantiationId))(
            p.params.map(duplicateConsStrat),
            p.restParam.map(duplicateConsStrat),
            duplicateProdStrat(p.res),
            duplicateVarState(p.capturedVarUpperbound.s).asProdStrat)
        case NoProd => NoProd
        case c: Ctor => new Ctor(c.exprId, updateInstantiationId(c.instantiationId))(
          c.ctor,
          c.args.map((a, b) => a -> duplicateProdStrat(b)))
      def duplicateConsStrat(c: ConsStrat): ConsStrat = c match
        case ConsVar(s) => duplicateVarState(s).asConsStrat
        case c: ConsFun =>
          new ConsFun(c.exprId, updateInstantiationId(c.instantiationId))(
            c.params.map(duplicateProdStrat),
            duplicateConsStrat(c.res))
        case NoCons => NoCons
        case NonAffine => NonAffine
        case Accumulator => Accumulator
        case PossibleAccumulator(s) => PossibleAccumulator(duplicateVarState(s))
        case IntoParam(s) => IntoParam(duplicateVarState(s))
        case fSel: FieldSel =>
          new FieldSel(fSel.exprId, updateInstantiationId(fSel.instantiationId))(
            fSel.field,
            fSel.selectsFrom,
            duplicateVarState(fSel.consVar.s).asConsStrat)
        case dtor: Dtor => new Dtor(dtor.exprId, updateInstantiationId(dtor.instantiationId))
      val newProd = duplicateVarState(pScheme.s).asProdStrat
      pScheme.constraints.foreach: (p, c) =>
        cc.constrain(duplicateProdStrat(p), duplicateConsStrat(c))
      newProd
    
    extension (v: StratVarState)
      def constrainOpaque(using cc: ConstraintsCollector): Unit =
        cc.constrain(NoProd, v.asConsStrat)
        cc.constrain(v.asProdStrat, NoCons)
    
    def mkFunProdStrat(
      params: Ls[ParamList],
      funLamId: FunId,
      res: ProdStrat,
      capturedSyms: collection.Set[Symbol]
    )(using cc: ConstraintsCollector): ProdStrat =
      def paramListFunId(whichParamList: Int): FunId =
        funLamId match
          case (sym: Symbol, -1) => (sym, whichParamList)
          case lambdaExprId: ResultId =>
            assert(whichParamList == 0)
            lambdaExprId
      params.zipWithIndex.foldRight[ProdStrat](res):
        case ((ps, whichParamList), acc) =>
          val plFunId = paramListFunId(whichParamList)
          val capUB = freshVar(s"cap_ub_$plFunId", cc.forFunGroup).asProdStrat
          for
            v <- capturedSyms
            capturedSymStrat <- generatedProdVars.get(v)
          do
            cc.constrain(capturedSymStrat.asProdStrat, capUB.asConsStrat)
          new ProdFun(plFunId, cc.instId)(
            ps.params.map(p => generatedProdVars(p.sym).asConsStrat),
            ps.restParam.map(p => generatedProdVars(p.sym).asConsStrat),
            acc,
            capUB)
    
    def processHandleableFun(
      resName: String,
      params: Ls[ParamList],
      body: Block,
      funLamId: FunId
    )(using cc: ConstraintsCollector): ProdStrat =
      val res = freshVar(resName, cc.forFunGroup)
      params.foreach:
        _.restParam.foreach: p =>
          generatedProdVars(p.sym).constrainOpaque
      val capturedSyms = funLamId match
        case (sym: TermSymbol, _) => preAnalyzer.res.capturedVars(sym)
        case lamExprId: ResultId => preAnalyzer.res.capturedVars(lamExprId)
        case other => lastWords(s"unexpected funLamId shape: $other")
      val funProdStrat = mkFunProdStrat(params, funLamId, res.asProdStrat, capturedSyms)
      processBlock(body)(using cc, res.asConsStrat)
      funProdStrat
    
    def constrainOpaqueResult(r: Result)(using cc: ConstraintsCollector): Unit =
      cc.constrain(processResult(r), NoCons)
    
    def processHandleableFunDefn(fun: FunDefn)(using cc: ConstraintsCollector): Unit =
      if mono || !preAnalyzer.res.rootFunDefns.contains(fun.dSym) then
        val funProdStrat = processHandleableFun(
          s"${fun.dSym.nme}_res",
          fun.params,
          fun.body,
          (fun.dSym, -1))
        cc.constrain(funProdStrat, generatedProdVars(fun.dSym).asConsStrat)
    
    def processClsLikeDefn(cls: ClsLikeDefn)(using cc: ConstraintsCollector): Unit =
      cls.privateFields.foreach(sym => generatedProdVars(sym).constrainOpaque)
      cls.publicFields.foreach: (_, tsym) =>
        generatedProdVars(tsym).constrainOpaque
      cls.methods.foreach: fun =>
        processBlock(fun.body)(using cc, NoCons)
      processBlock(cls.preCtor)(using cc, NoCons)
      processBlock(cls.ctor)(using cc, NoCons)
      cls.companion.foreach: mod =>
        mod.privateFields.foreach(sym => generatedProdVars(sym).constrainOpaque)
        mod.publicFields.foreach: (_, tsym) =>
          generatedProdVars(tsym).constrainOpaque
        mod.methods.foreach: fun =>
          processHandleableFunDefn(fun)
        processBlock(mod.ctor)(using cc, NoCons)
    
    def processBlock(b: Block)(using cc: ConstraintsCollector, blkRes: ConsStrat): Unit =
      val instId = cc.instId
      b match
      case Return(res, implct) => cc.constrain(processResult(res), blkRes)
      case Throw(exc) => constrainOpaqueResult(exc)
      case Match(scrut, arms, dflt, rest) =>
        val scrutStrat = processResult(scrut)
        cc.constrain(scrutStrat, new Dtor(scrut.uid, instId))
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
          case _: NoSymbol => ()
          case _ => cc.constrain(rhsStrat, generatedProdVars(lhs).asConsStrat)
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
      case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
        constrainOpaqueResult(par)
        args.foreach: arg =>
          constrainOpaqueResult(arg)
        handlers.foreach: handler =>
          processBlock(handler.body)(using cc, NoCons)
        processBlock(body)
        processBlock(rest)
      case Define(defn, rest) =>
        defn match
        case ValDefn(tsym, sym, rhs) =>
          val rhsStrat = processResult(rhs)
          cc.constrain(rhsStrat, generatedProdVars(tsym).asConsStrat)
        case fun: FunDefn =>
          processHandleableFunDefn(fun)
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
          cc.constrain(fStrat, NoCons)
          argsStrat.foreach(arg => cc.constrain(arg, NoCons))
          NoProd
        else
          val callRes = freshVar("call_res", cc.forFunGroup)
          cc.constrain(fStrat, new ConsFun(callExprId, instId)(argsStrat, callRes.asConsStrat))
          callRes.asProdStrat
      r match
        case sel@TrackableSelect(from, field, owner) =>
          val fromStrat = processResult(from)
          val selRes = freshVar("sel_res", cc.forFunGroup)
          cc.constrain(
            fromStrat,
            new FieldSel(sel.uid, instId)(field, owner, selRes.asConsStrat))
          selRes.asProdStrat
        case c@CtorCall(ctor, args) if args.forall(_.spread.isEmpty) =>
          val argsStrat = args.map:
            case Arg(_, a) => processResult(a)
          ctor match
          case cls: ClassSymbol =>
            cls.tree.clsParams.size match
            case 1 =>
              val clsParams = cls.tree.clsParams.head
              softAssert(argsStrat.size == clsParams.size)
              new Ctor(c.uid, instId)(ctor, clsParams.zip(argsStrat))
            case _ =>
              // - the size of 0 means we don't know the cls param symbols,
              // so we constrain args with NoCons and this CtorCall gives NoProd
              // - if size > 1, we cannot handle multiple parameter class flow now,
              //   constrain args with NoCons and this CtorCall gives NoProd
              for a <- argsStrat do cc.constrain(a, NoCons)
              NoProd
          case _: ModuleOrObjectSymbol => new Ctor(c.uid, instId)(ctor, Nil)
          case tupSize: Int => new Ctor(c.uid, instId)(tupSize, (0 until tupSize).zip(argsStrat).toList)
        case c@CtorCall(_, args) =>
          args.foreach(arg => cc.constrain(processResult(arg.value), NoCons))
          NoProd
        case c@Call(fun, args) => handleCallLike(c.uid, fun, args)
        case i@Instantiate(_, cls, args) => handleCallLike(i.uid, cls, args)
        case lam@Lambda(ps, body) =>
          processHandleableFun("lam_res", ps :: Nil, body, lam.uid)
        case _: Tuple => lastWords("should be handled in CtorCall")
        case Record(_, fields) =>
          fields.foreach:
            case RcdArg(idx, value) =>
              idx.foreach(p => cc.constrain(processResult(p), NoCons))
              cc.constrain(processResult(value), NoCons)
          NoProd
        case p: Path =>
          p match
          case CtorRef(ctor) => NoProd
          case refSite@FunRef(f) =>
            funsToProdStratScheme.get(f) match
            case Some(fScheme) =>
              fScheme.instantiate(refSite.uid, f)
            case None => generatedProdVars(f).asProdStrat
          case refLk@RefLike(sym) =>
            refLk match
              case Select(p, _) => cc.constrain(processResult(p), NoCons)
              case _ => ()
            generatedProdVars(sym).asProdStrat
          case _: Value.Ref => lastWords("already handled in `RefLike` case")
          case Select(qual, name) =>
            cc.constrain(processResult(qual), NoCons)
            NoProd
          case DynSelect(qual, fld, arrayIdx) =>
            cc.constrain(processResult(qual), NoCons)
            cc.constrain(processResult(fld), NoCons)
            NoProd
          case Value.This(sym) => NoProd
          case Value.Lit(lit) => NoProd
  }
end FlowConstraintsCollector

class FlowConstraintSolver(val collector: FlowConstraintsCollector):
  given tl: TraceLogger = collector.tl
  given fState: FlowAnalysis.State = collector.fState
  given eState: Elaborator.State = collector.eState
  given preAnalyzer: FlowPreAnalyzer = collector.preAnalyzer
  given Raise = preAnalyzer.raise
  
  
  val ctorDests = LinkedHashMap.empty[ConcreteProducer, Set[ConcreteConsumer | MarkerConsStrat]].withDefaultValue(Set.empty)
  val dtorSrcs = LinkedHashMap.empty[ConcreteConsumer, Set[ConcreteProducer | MarkerProdStrat]].withDefaultValue(Set.empty)
  val funDests = LinkedHashMap.empty[ProdFun, Set[ConsFun | MarkerConsStrat]].withDefaultValue(Set.empty)
  val funSrcs = LinkedHashMap.empty[ConsFun, Set[ProdFun | MarkerProdStrat]].withDefaultValue(Set.empty)
  
  val upperBounds = MutMap.empty[StratVarId, Ls[ConsStrat]].withDefaultValue(Nil)
  val lowerBounds = MutMap.empty[StratVarId, Ls[ProdStrat]].withDefaultValue(Nil)
  
  private def logNonAffineSyms: Unit =
    tl.scoped(FlowAnalysis.TraceScope.nonAffineSyms):
      tl.log(">>> non-affine syms >>>")
      val outputRes =
        for
          case (uid, bounds) <- upperBounds
          if bounds.contains(NonAffine)
          stratVar <- fState.stratVarIdToState.get(uid)
        yield s"${stratVar.name}@$uid"
      for nonAffine <- outputRes.toSortedSet do
        tl.log(nonAffine)
      tl.log("<<< non-affine syms <<<")
  
  private def logAccumulatorSyms: Unit =
    tl.scoped(FlowAnalysis.TraceScope.accumulatorSyms):
      tl.log(">>> accumulator syms >>>")
      def showAccumulatorSym(uid: StratVarId, bounds: Ls[ConsStrat]): Opt[Str] =
        bounds
          .collectFirst:
            case PossibleAccumulator(s) if s.uid === uid => s.name
            case IntoParam(s) if s.uid === uid => s.name
          .map: nme =>
            s"$nme@$uid"
      val outputRes =
        for
          case (uid, bounds) <- upperBounds
          if bounds.contains(Accumulator)
          accumulatorSym <- showAccumulatorSym(uid, bounds)
        yield accumulatorSym
      for accumulator <- outputRes.toSortedSet do
        tl.log(accumulator)
      tl.log("<<< accumulator syms <<<")
  
  locally {
    val cache = MutSet.empty[ProdStrat -> ConsStrat]
    def hasConcreteInstantiationId(prodOrCons: ProdStrat | ConsStrat): Boolean = prodOrCons match
      case s: StratWithOrigin[?] => s.instantiationId.isDefined
      case _ => true
    def handle(constraint: ProdStrat -> ConsStrat): Unit = if cache.add(constraint) then
      assert:
        val (prod, cons) = constraint
        hasConcreteInstantiationId(prod) &&
        hasConcreteInstantiationId(cons)
      constraint match
      case (c: Ctor, d: Dtor) =>
        ctorDests(c) += d
        dtorSrcs(d) += c
      case (c: Ctor, d: FieldSel) =>
        if d.selectsFrom === c.ctor then
          ctorDests(c) += d
          dtorSrcs(d) += c
          handle(
            c.args.find(_._1 is d.field).get._2,
            d.consVar)
      case (c: Ctor, NoCons) =>
        ctorDests(c) += NoCons
        for (_, argProd) <- c.args do handle(argProd, NoCons)
      case (c: Ctor, x@(NonAffine | Accumulator)) =>
        ctorDests(c) += x
        for (_, argProd) <- c.args do handle(argProd, x)
      case (c: Ctor, i@IntoParam(s)) =>
        for (_, argProd) <- c.args do handle(argProd, PossibleAccumulator(s))
      case (c: Ctor, p@PossibleAccumulator(s)) =>
        for (_, argProd) <- c.args do handle(argProd, p)
      case (p: ProdFun, c: ConsFun) =>
        funDests(p) += c
        funSrcs(c) += p
        val tracksAccumulator = collector.accumulatorTracking
        
        c.params.take(p.params.size).lazyZip(p.params).foreach: (argC, argP) =>
          handle(argC -> argP)
          if tracksAccumulator then argP match
            case ConsVar(s) => handle(argC, IntoParam(s))
            case _ => ()
        for
          restCons <- p.restParam
          arg <- c.params.drop(p.params.size)
        do
          handle(arg, restCons)
          if tracksAccumulator then restCons match
            case ConsVar(s) => handle(arg, IntoParam(s))
            case _ => ()
        handle(p.res, c.res)
      case (p: ProdFun, NoCons) =>
        funDests(p) += NoCons
        for a <- p.params do handle(NoProd, a)
        p.restParam.foreach(r => handle(NoProd, r))
        handle(p.res, NoCons)
      case (p: ProdFun, x@(NonAffine | Accumulator)) =>
        funDests(p) += x
        handle(p.capturedVarUpperbound, x)
      case (p: ProdFun, i@IntoParam(s)) =>
        handle(p.capturedVarUpperbound, PossibleAccumulator(s))
      case (p: ProdFun, c@PossibleAccumulator(s)) =>
        handle(p.capturedVarUpperbound, c)
      case (NoProd, d: Dtor) =>
        dtorSrcs(d) += NoProd
      case (NoProd, sel: FieldSel) =>
        dtorSrcs(sel) += NoProd
        handle(NoProd, sel.consVar)
      case (NoProd, c: ConsFun) =>
        funSrcs(c) += NoProd
        for a <- c.params do handle(a, NoCons)
        handle(NoProd, c.res)
      case (p: ProdVar, c: ConsVar) =>
        upperBounds(p.s.uid) ::= c
        lowerBounds(c.s.uid) ::= p
        for l <- lowerBounds(p.s.uid) do handle(l, c)
        for u <- upperBounds(c.s.uid) do handle(p, u)
      case (p: ProdVar, c) =>
        upperBounds(p.s.uid) ::= c
        c match
          case PossibleAccumulator(s) if p.s === s =>
            upperBounds(p.s.uid) ::= Accumulator
            for l <- lowerBounds(p.s.uid) do handle(l, Accumulator)
          case _ => ()
        for l <- lowerBounds(p.s.uid) do handle(l, c)
      case (p, c: ConsVar) =>
        lowerBounds(c.s.uid) ::= p
        for u <- upperBounds(c.s.uid) do handle(p, u)
      case _ => () // ignore other cases
    end handle
    
    for c <- collector.allConstraints do handle(c)
  }
  
  logNonAffineSyms
  logAccumulatorSyms


end FlowConstraintSolver
