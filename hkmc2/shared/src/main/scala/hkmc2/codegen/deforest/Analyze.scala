package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap, LinkedHashSet}
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, Fun, Ins}

type StratVarId = Uid[StratVar]

class StratVarState(val uid: StratVarId, val name: Str, val generatedForFun: Opt[TermSymbol]):
  lazy val asProdStrat = ProdVar(this)
  lazy val asConsStrat = ConsVar(this)
  override def toString(): String = s"${if name.isEmpty() then "$stratvar" else name}@${uid}@$generatedForFun"
object StratVarState:
  def freshVar(nme: String)(using vuid: Uid.StratVar.State): StratVarState =
    val newId = vuid.nextUid
    StratVarState(newId, nme, N)
  def freshVar(nme: String, generatedForFun: TermSymbol)(using vuid: Uid.StratVar.State): StratVarState =
    val newId = vuid.nextUid
    StratVarState(newId, s"${nme}_for_${generatedForFun.nme}", S(generatedForFun))
  def freshVar(nme: String, forFunOpt: Opt[TermSymbol])(using vuid: Uid.StratVar.State): StratVarState =
    forFunOpt match
    case None => freshVar(nme)
    case Some(forFun) => freshVar(nme, forFun)

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
  val instantiationId: Opt[InstantiationId]
)(
  val ctor: CtorCls,
  val args: Ls[SelField -> ProdStrat]
) extends ProdStrat with ToCtorDtorId(exprId, instantiationId)
    

sealed abstract class ConsStrat
case class ConsVar(s: StratVarState) extends ConsStrat with StratVar(s)
case class ConsFun(params: Ls[ProdStrat], res: ConsStrat) extends ConsStrat
case object NoCons extends ConsStrat
class FieldSel(
  val exprId: ResultId,
  val instantiationId: Opt[InstantiationId]
)(
  val field: SelField,
  val consVar: ConsVar
) extends ConsStrat with ToCtorDtorId(exprId, instantiationId):
  def isSelFromCls(using dState: Deforest.State, eState: Elaborator.State, pre: DeforestPreAnalyzer) =
    field match
    case tSym: TermSymbol => tSym.owner.flatMap(_.asCls).get
    case _: Int =>
      exprId.getResult match
      case DeforestTupSelect(_, (_, size)) => size
      case other => lastWords(other.toString())

class Dtor(
  val scrutExprId: ResultId,
  val instantiationId: Opt[InstantiationId]
) extends ConsStrat with ToCtorDtorId(scrutExprId, instantiationId)

sealed trait ToCtorDtorId(exprId: ResultId, instId: Opt[InstantiationId]):
  def toCtorDtorId = CtorDtorId(exprId, instId.get)

case class CtorDtorId(exprId: ResultId, instId: InstantiationId):
  def pp(using dState: Deforest.State) = s"${exprId.getResult}"

type ConcreteProducer = Ctor
type ConcreteConsumer = Dtor | FieldSel


class ProdStratScheme(val s: StratVarState, val constraints: Ls[ProdStrat -> ConsStrat])




class DeforestPreAnalyzer(
  val importedInfo: ImportedInfo,
  val b: Block
)(using
  val tl: TraceLogger,
  val elabState: Elaborator.State,
  val dState: Deforest.State
) extends BlockTraverser:
  given stratVarUidState: Uid.StratVar.State = new Uid.StratVar.State
  import StratVarState.freshVar
  
  extension (s: Symbol) def isPrivateMem =
    s.asTrm.exists: tSym =>
      (tSym.k is LetBind) && tSym.owner.exists(_.asMod.isDefined)
  
  
  ctxTracker.inTopLvl(b):
    applyBlock(b)
  
  object res:
    val primitiveStratVar = StratVarState.freshVar("unknown")
    // this contains
    // - fundefs in toplvl/lone-modules(not necessarily toplvl ones) that
    //     - does not contain unsupported forms like while loops
    //     - does not contain nested class/modules (but nested functions are allowed)
    // - blocks
    //     - toplvl block if it does not contain unsupported forms
    // when traversing
    // - fundefs in the set: nothing should be skipped
    // - toplvl block in the set: skip all class/module/fun defs
    val toplvlFunAndBlkToAnalyze = LinkedHashSet.empty[FunDefn | Block]
    val matchScrutToMatchBlock = MutMap.empty[ResultId, Match]
    val labelSymToLabelBlk = MutMap.empty[Symbol, Label]
    val matchScrutToCtxOfMatch = MutMap.empty[ResultId, Ls[InCtx]]
    val labelSymToCtxOfLabel = MutMap.empty[Symbol, Ls[InCtx]]
    val selToCtxOfSel = MutMap.empty[ResultId, Ls[InCtx]]
    val modSymToBms = MutMap.empty[Symbol, BlockMemberSymbol]
    
    lazy val funSymToFunDefn: Map[TermSymbol, FunDefn] = toplvlFunAndBlkToAnalyze
      .collect:
        case f: FunDefn => f.dSym -> f
      .toMap
    def getEnclosingMatchesForSel(selExprId: ResultId) = selToCtxOfSel(selExprId)
      .iterator
      .collect:
        case InCtx.MtchBody(m, cse) => m.scrut.uid -> cse
    def getParentLabelOrMatchesAndRestBefore(matchOrLabelId: MatchOrLabelId): (Iterator[Label | Match], Block) =
      val ctx = matchOrLabelId match
        case label: Symbol => labelSymToCtxOfLabel(label)
        case dtorId: ResultId => matchScrutToCtxOfMatch(dtorId)
      val simpleRest = matchOrLabelId match
        case label: Symbol => labelSymToLabelBlk(label).rest
        case dtorId: ResultId => matchScrutToMatchBlock(dtorId).rest
      def it = ctx.iterator
        .takeWhile:
          case _: (InCtx.Fn | InCtx.Mod | InCtx.TopLvl) => false
          case _ => true
        .collect:
          case InCtx.LblBody(l) => l
          case InCtx.MtchBody(m, cse) => m
          case InCtx.BegnBody(b) => b
      val blockUntilParent = it
        .takeWhile(_.isInstanceOf[Begin])
        .collect:
          case b: Begin => b.rest
        .foldLeft(simpleRest)(Begin.apply)
      val parents = it
        .collect:
          case l: Label => l
          case m: Match => m
        .asInstanceOf[Iterator[Label | Match]]
      parents -> blockUntilParent
  end res
  
  
  enum InCtx:
    case TopLvl()
    case Mod(mod: ClsLikeBody)
    case ModCtor(b: Block)
    case Fn(f: FunDefn)
    case LblBody(l: Label)
    case MtchBody(m: Match, cse: Opt[CtorCls])
    case BegnBody(b: Begin)
    case Scped(s: Scoped)
    // non-handleable cases for now:
    // - while loop
    // - nested defined class/module in functions
    // - handler and other unsupported forms
    // - `this`
    // - tuple with spread
    // - vararg
    var handleable: Boolean = true
    
  private object ctxTracker:
    private var ctx: Ls[InCtx] = Nil
    
    def getAllCtx = ctx
    def isToplvl = ctx.matches:
      case init :+ InCtx.TopLvl() =>
        init.forall: i =>
          i.matches:
            case _: (InCtx.BegnBody | InCtx.Scped) => true
    def canHaveCls: Boolean =
      ctx.forall: c =>
        c match
          case InCtx.TopLvl() => true
          case InCtx.Mod(m) => true
          case InCtx.ModCtor(b) => true
          case InCtx.BegnBody(b) => true
          case InCtx.Scped(s) => true
          case _ => false
        
    
    inline def inCtxOf(
      c: (FunDefn | Label | (Match, Opt[CtorCls]) | ClsLikeBody | Begin | Scoped)
    )(inline body: => Any) =
      val newCtx = c match
        case c: ClsLikeBody => InCtx.Mod(c)
        case f: FunDefn => InCtx.Fn(f)
        case l: Label => InCtx.LblBody(l)
        case m: (Match, Opt[(CtorCls)]) => InCtx.MtchBody(m._1, m._2)
        case b: Begin => InCtx.BegnBody(b)
        case s: Scoped => InCtx.Scped(s)
      
      ctx = newCtx :: ctx
      body
      ctx = ctx.tail
      
      c match
        case f: FunDefn =>
          if newCtx.handleable && (isToplvl || ctx.head.isInstanceOf[InCtx.Mod]) then
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
        case c: ClsLikeBody => ()
        case s: Scoped => ()
      if isToplvl && c.matches { case _: (ClsLikeBody | FunDefn) => true } then ()
      else ctx.head.handleable &&= newCtx.handleable
    
    inline def inTopLvl(toplvlBlk: Block)(inline body: => Any) =
      assert(ctx.isEmpty)
      val newCtx = InCtx.TopLvl()
      ctx = newCtx :: ctx
      body
      if newCtx.handleable then
        res.toplvlFunAndBlkToAnalyze.add(toplvlBlk)
      ctx = ctx.tail
      assert(ctx.isEmpty)
    
    inline def inModCtor(ctor: Block)(inline body: => Any) =
      assert(ctx.head.matches{ case _: InCtx.Mod => true })
      val newCtx = InCtx.ModCtor(ctor)
      ctx = newCtx :: ctx
      body
      if newCtx.handleable then
        res.toplvlFunAndBlkToAnalyze.add(ctor)
      ctx = ctx.tail
      assert(ctx.head.matches{ case _: InCtx.Mod => true })
    
    def markAsNonHandleable() =
      ctx.head.handleable = false
      
  
  override def applyBlock(b: Block): Unit = b match
    case scpd@Scoped(syms, body) =>
      ctxTracker.inCtxOf(scpd):
        applyBlock(body)
    case m@Match(scrut, arms, dflt, rest) =>
      applyPath(scrut)
      for (cse, body) <- arms do
        val cseCls = cse match
          case Case.Cls(cls, _) => S(cls)
          case Case.Tup(n, false) => S(n)
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
      if lhs.isPrivateMem then ctxTracker.markAsNonHandleable()
      applyResult(rhs)
      applyBlock(rest)
    case Define(defn, rest) =>
      applyDefn(defn)
      applyBlock(rest)
    case Throw(exc) => applyResult(exc)
    case Break(label) => ()
    case End(msg) => ()
    case b: (TryBlock | AssignField | AssignDynField | HandleBlock | Label | Continue) =>
      ctxTracker.markAsNonHandleable()
      super.applyBlock(b)
  
  override def applyResult(r: Result): Unit = r match
    case tupSel@PossibleDeforestTupSelect(_, _) =>
      res.selToCtxOfSel.addOne(tupSel.uid -> ctxTracker.getAllCtx)
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
  
  override def applyPath(p: Path): Unit = p match
    case DynSelect(qual, fld, arrayIdx) =>
      ctxTracker.markAsNonHandleable()
      applyPath(qual); applyPath(fld)
    case p@Select(qual, name) => p match
      case DeforestableSelect(_) =>
        res.selToCtxOfSel.addOne(p.uid -> ctxTracker.getAllCtx)
        applyPath(qual)
      case _ =>
        ctxTracker.markAsNonHandleable()
        super.applyPath(p)
    case v: Value => applyValue(v)
  
  override def applyValue(v: Value): Unit = v match
    case Value.Ref(l, disamb) =>
      if l.isPrivateMem then ctxTracker.markAsNonHandleable()
    case Value.This(sym) => ctxTracker.markAsNonHandleable()
    case Value.Lit(lit) => ()
  
  override def applyFunDefn(fun: FunDefn): Unit =
    ctxTracker.inCtxOf(fun):
      fun.params.foreach(applyParamList)
      applyBlock(fun.body)
  
  override def applyParamList(pl: ParamList): Unit =
    if pl.restParam.isDefined then
      ctxTracker.markAsNonHandleable()
  
  override def applyArg(arg: Arg): Unit =
    if arg.spread.isDefined then ctxTracker.markAsNonHandleable()
    else applyPath(arg.value)
  
  override def applyDefn(defn: Defn): Unit = defn match
    case defn: FunDefn => applyFunDefn(defn)
    case defn: ValDefn => applyValDefn(defn)
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    =>
      if ctxTracker.canHaveCls then
        if ctorSym.isEmpty
          && paramsOpt.isEmpty
          && auxParams.isEmpty
          && parentPath.isEmpty
          && methods.isEmpty
          && privateFields.isEmpty
          && publicFields.isEmpty
          && preCtor.isEmpty
          && ctor.isEmpty
        then mod.foreach(applyCompanionModule)
      else
        ctxTracker.markAsNonHandleable()
  
  override def applyCompanionModule(b: ClsLikeBody): Unit =
    if ctxTracker.isToplvl then
      res.modSymToBms(b.isym.asMod.get) = b.isym.asBlkMember.get
      ctxTracker.inCtxOf(b):
        b.methods.foreach(applyFunDefn)
        ctxTracker.inModCtor(b.ctor):
          applyBlock(b.ctor)
    else ctxTracker.markAsNonHandleable()
end DeforestPreAnalyzer

class DeforestConstraintsCollector(val preAnalyzer: DeforestPreAnalyzer):
  given stratVarUidState: Uid.StratVar.State = preAnalyzer.stratVarUidState
  given elabState: Elaborator.State = preAnalyzer.elabState
  given dState: Deforest.State = preAnalyzer.dState
  given tl: TraceLogger = preAnalyzer.tl
  given DeforestPreAnalyzer = preAnalyzer
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
  
  // ===================================================
  
  locally {
    // generate strat vars needed
    val generatedProdVars: Map[Symbol, StratVarState] =
      // the keys could possibly be one of the following kinds:
      // - TermSymbol:
      //   - functions, let and val definitions in an module (with an owner)
      //   - functions and val definitions in top level or nested in function body (without an owner)
      // - TempSymbol
      // - VarSymbol: let bindings without an owner, function parameters, user declared pattern variables
      val store = MutMap.empty[Symbol, StratVarState]
      // for top level block
      if preAnalyzer.res.toplvlFunAndBlkToAnalyze.contains(preAnalyzer.b) then
        object AddStratForTopLvlSymbols extends BlockTraverserShallow:
          override def applyBlock(b: Block): Unit = b match
            case Scoped(syms, body) => for s <- syms do
              s match
              // top level immutable val defs
              case bms: BlockMemberSymbol if bms.tsym.exists(_.k is ImmutVal) =>
                val tsym = bms.tsym.get
                store(tsym) = freshVar(tsym.nme)
              // varsymbols for let binding
              case s: VarSymbol => store(s) = freshVar(s.nme)
              case s: TempSymbol => store(s) = freshVar(s.nme)
              case _ => ()
              applyBlock(body)
            case _ => super.applyBlock(b)
        AddStratForTopLvlSymbols.applyBlock(preAnalyzer.b)
      // for toplvl fundefns
      for case f: FunDefn <- preAnalyzer.res.toplvlFunAndBlkToAnalyze do
        val forFun = f.dSym
        // funs can only nest other funs
        object AddStratForToplvlFun extends BlockTraverser:
          override def applyFunDefn(fun: FunDefn): Unit =
            store(fun.dSym) = freshVar(fun.sym.nme, forFun)
            super.applyFunDefn(fun)
          override def applyParamList(pl: ParamList): Unit =
            for p <- pl do store(p.sym) = freshVar(p.sym.nme, forFun)
          override def applyBlock(b: Block): Unit = b match
            case Scoped(syms, body) => for s <- syms do
              s match
              // local vals
              case bms: BlockMemberSymbol if bms.tsym.exists(tsym => tsym.k is ImmutVal) =>
                val tsym = bms.tsym.get
                store(tsym) = freshVar(tsym.nme, forFun)
              // varsymbols for let binding
              case s: VarSymbol => store(s) = freshVar(s.nme, forFun)
              case s: TempSymbol => store(s) = freshVar(s.nme, forFun)
              case _ => ()
              applyBlock(body)
            case _ => super.applyBlock(b)
        AddStratForToplvlFun.applyFunDefn(f)
      store.toMap.withDefaultValue(preAnalyzer.res.primitiveStratVar)
    end generatedProdVars
    
    // compute scc
    val sccInOrder: Ls[Ls[TermSymbol]] =
      import algorithms.partitionScc
      var edges = Ls.empty[(TermSymbol, TermSymbol)]
      for case f: FunDefn <- preAnalyzer.res.toplvlFunAndBlkToAnalyze do
        object CollectAllReferredFun extends BlockTraverser:
          override def applyPath(p: Path) = p match
            case FunRef(callee) =>
              if preAnalyzer.res.funSymToFunDefn.contains(callee) then
                edges ::= f.dSym -> callee
            case _ => ()
        CollectAllReferredFun.applyBlock(f.body)
      partitionScc(
        edges,
        preAnalyzer.res.toplvlFunAndBlkToAnalyze.collect { case f: FunDefn => f.dSym }
      ).reverse
    end sccInOrder
    for
      group <- sccInOrder
      f <- group
    do funToSccGroups(f) = group
    
    
    enum ProcessMode:
      val blkRes: ConsVar
      case Fun(blkRes: ConsVar) // only expect nested functions
      case ToplvlBlk(blkRes: ConsVar) // skip functions/classes
    
    // compute strat scheme for each scc group
    val funsToProdStratScheme = MutMap.empty[TermSymbol, ProdStratScheme]
    for groupedFuns <- sccInOrder do
      (new ConstraintsCollector(Some(funToSccRep(groupedFuns.head).get))).givenIn: cc ?=>
        for funSym <- groupedFuns do
          val fun = preAnalyzer.res.funSymToFunDefn(funSym)
          val thisFunVar = generatedProdVars(fun.dSym)
          val res = freshVar(s"${funSym.nme}_res", cc.forFunGroup)
          val funProdStrat = fun.params.foldRight[ProdStrat](res.asProdStrat): (ps, acc) =>
            assert(ps.restParam.isEmpty)
            ProdFun(ps.params.map(p => generatedProdVars(p.sym).asConsStrat), acc)
          given ProcessMode = ProcessMode.Fun(res.asConsStrat)
          processBlock(fun.body)
          cc.constrain(funProdStrat, thisFunVar.asConsStrat)
        for funSym <- groupedFuns do
          funsToProdStratScheme(funSym) = ProdStratScheme(generatedProdVars(funSym), cc.constraints)
    
    // collect constraints from toplvl block
    globalCollector.givenIn: cc ?=>
      cc.constrain(preAnalyzer.res.primitiveStratVar.asProdStrat, NoCons)
      cc.constrain(NoProd, preAnalyzer.res.primitiveStratVar.asConsStrat)
      if preAnalyzer.res.toplvlFunAndBlkToAnalyze.contains(preAnalyzer.b) then
        val topLvlRes = freshVar("toplvl_res").asConsStrat
        given ProcessMode = ProcessMode.ToplvlBlk(topLvlRes)
        processBlock(preAnalyzer.b)
        cc.constrain(topLvlRes.asProdStrat, NoCons)

      for case fun: FunDefn <- preAnalyzer.res.toplvlFunAndBlkToAnalyze do
        val funSym = fun.dSym
        val pScheme = funsToProdStratScheme(funSym)
        val synthesizedRefUid =
          Value.Ref(preAnalyzer.res.funSymToFunDefn(funSym).sym, S(funSym)).uid
        val selfProd = pScheme.instantiate(synthesizedRefUid, funSym)
        cc.constrain(selfProd, NoCons)
        val selfInstId = synthesizedRefUid :: Nil
        synthesizedInstIdToFunSym(selfInstId) = funSym

    // ===================================================
    
    extension (pScheme: ProdStratScheme) def instantiate(
      referSite: ResultId,
      referringTo: TermSymbol
    )(using cc: ConstraintsCollector): ProdStrat =
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
        case ProdFun(params, res) => ProdFun(params.map(duplicateConsStrat), duplicateProdStrat(res))
        case NoProd => NoProd
        case c: Ctor => new Ctor(c.exprId, updateInstantiationId(c.instantiationId))(
          c.ctor,
          c.args.map((a, b) => a -> duplicateProdStrat(b)))
      def duplicateConsStrat(c: ConsStrat): ConsStrat = c match
        case ConsVar(s) => duplicateVarState(s).asConsStrat
        case ConsFun(params, res) => ConsFun(params.map(duplicateProdStrat), duplicateConsStrat(res))
        case NoCons => NoCons
        case fSel: FieldSel =>
          new FieldSel(fSel.exprId, updateInstantiationId(fSel.instantiationId))(
            fSel.field,
            duplicateVarState(fSel.consVar.s).asConsStrat)
        case dtor: Dtor => new Dtor(dtor.scrutExprId, updateInstantiationId(dtor.instantiationId))
      val newProd = duplicateVarState(pScheme.s).asProdStrat
      pScheme.constraints.foreach: (p, c) =>
        cc.constrain(duplicateProdStrat(p), duplicateConsStrat(c))
      newProd
    
    def processBlock(b: Block)(using cc: ConstraintsCollector, im: ProcessMode): Unit =
      val instId = cc.instId
      b match
      case Return(res, implct) => cc.constrain(processResult(res), im.blkRes)
      case Throw(exc) => processResult(exc)
      case Match(scrut, arms, dflt, rest) =>
        val scrutStrat = processResult(scrut)
        cc.constrain(
          scrutStrat,
          new Dtor(scrut.uid, instId))
        (arms.map(_._2) ++ dflt).foreach(processBlock)
        processBlock(rest)
      case Label(l, false, body, rest) =>
        processBlock(body)
        processBlock(rest)
      case Break(label) => ()
      case Scoped(syms, body) => processBlock(body)
      case Begin(sub, rest) =>
        processBlock(sub)
        processBlock(rest)
      case Assign(lhs, rhs, rest) =>
        val rhsStrat = processResult(rhs)
        cc.constrain(rhsStrat, generatedProdVars(lhs).asConsStrat)
        processBlock(rest)
      case Define(defn, rest) =>
        defn match
        case ValDefn(tsym, sym, rhs) =>
          cc.constrain(processResult(rhs), generatedProdVars(tsym).asConsStrat)
        case FunDefn(_, _, dSym, params, body) =>
          if im.matches { case _: ProcessMode.Fun => true } then
            val funRes = freshVar(s"${dSym.nme}_res", cc.forFunGroup)
            val funProdStrat = params.foldRight[ProdStrat](funRes.asProdStrat): (ps, acc) =>
              assert(ps.restParam.isEmpty)
              ProdFun(ps.params.map(p => generatedProdVars(p.sym).asConsStrat), acc)
            processBlock(body)(using cc, ProcessMode.Fun(funRes.asConsStrat))
            cc.constrain(funProdStrat, generatedProdVars(dSym).asConsStrat)
        case cls: ClsLikeDefn => im match
          case _: ProcessMode.Fun => die
          case _ => ()
        processBlock(rest)
      case End(msg) => ()
      case _ => die
    
    def processResult(r: Result)(using cc: ConstraintsCollector, im: ProcessMode): ProdStrat =
      val instId = cc.instId
      def handleCallLike(f: Path, args: List[Arg]): ProdStrat =
        val fStrat = processResult(f)
        val argsStrat = args.map(a => processResult(a.value))
        val callRes = freshVar("call_res", cc.forFunGroup)
        cc.constrain(fStrat, ConsFun(argsStrat, callRes.asConsStrat))
        callRes.asProdStrat
      r match
      case tupSel@DeforestTupSelect(from, ith -> size) =>
        val fromStrat = processResult(Value.Ref(from, N))
        val selRes = freshVar("sel_res", cc.forFunGroup)
        cc.constrain(
          fromStrat,
          new FieldSel(tupSel.uid, instId)(ith, selRes.asConsStrat))
        selRes.asProdStrat
      case c@CtorCall(ctor, args) =>
        val argsStrat = args.map:
          case Arg(_, a) => processResult(a)
        ctor match
        case cls: ClassSymbol => new Ctor(c.uid, instId)(ctor,
          cls.tree.clsParams.headOption.getOrElse(Nil)//FIXME? case when there are only aux parameter lists
          .zip(argsStrat))
        case _: ModuleOrObjectSymbol => new Ctor(c.uid, instId)(ctor, Nil)
        case tupSize: Int => new Ctor(c.uid, instId)(tupSize, (0 until tupSize).zip(argsStrat).toList)
      case Call(fun, args) => handleCallLike(fun, args)
      case Instantiate(false, cls, args) => handleCallLike(cls, args)
      case Lambda(ParamList(_, params, N), body) =>
        val res = freshVar("lam_res", cc.forFunGroup)
        val paramsStrat = params.map(p => generatedProdVars(p.sym).asConsStrat)
        processBlock(body)(using cc, ProcessMode.Fun(res.asConsStrat))
        ProdFun(paramsStrat, res.asProdStrat)
      case p: Path =>
        p match
        case CtorRef(ctor) => NoProd
        case refSite@FunRef(f) =>
          funsToProdStratScheme.get(f) match
          case Some(fScheme) => fScheme.instantiate(refSite.uid, f)
          case None => generatedProdVars(f).asProdStrat
        case sel@DeforestableSelect(s) => s match
          case _: TopLevelSymbol => NoProd
          case s: TermSymbol =>
            // only parambind and let/vals in modules are handled here
            s.k match
            case _ if s.decl.exists(_.isInstanceOf[Param]) =>
              val obj = processResult(sel.qual)
              val selRes = freshVar("sel_res", cc.forFunGroup)
              cc.constrain(
                obj,
                new FieldSel(sel.uid, instId)(s, selRes.asConsStrat))
              selRes.asProdStrat
            case (ImmutVal | LetBind) => generatedProdVars(s).asProdStrat
            case _ => die
          case _ => die
        case Value.Ref(l, disamb) =>
          disamb.fold(generatedProdVars(l))(generatedProdVars.apply).asProdStrat
        case Value.Lit(lit) => NoProd
        case other => lastWords(other.toString())
      case _ => die
  }
end DeforestConstraintsCollector


class DeforestConstrainSolver(val collector: DeforestConstraintsCollector):
  given tl: TraceLogger = collector.tl
  given dState: Deforest.State = collector.dState
  given eState: Elaborator.State = collector.elabState
  given preAnalyzer: DeforestPreAnalyzer = collector.preAnalyzer
  
  private def selAndDtorIsSameConsumer(dtor: CtorDtorId, sels: Iterable[CtorDtorId]): Boolean =
    sels.forall:
      case CtorDtorId(selExpr, instId) =>
        instId == dtor.instId &&
        preAnalyzer.res.getEnclosingMatchesForSel(selExpr).exists(_._1 == dtor.exprId) &&
        selExpr.getResult.matches:
          case Select(p, _) => p === dtor.exprId.getResult
          case DeforestTupSelect(s, _) => s === dtor.exprId.getReferredSym
  
  sealed abstract class FinalDest
  case class FinalDestMatch(dtor: CtorDtorId, sels: Set[CtorDtorId]) extends FinalDest
  case class FinalDestSel(dtors: Set[CtorDtorId], field: SelField) extends FinalDest
  private val ctorDests = LinkedHashMap.empty[ConcreteProducer, Set[ConcreteConsumer | NoCons.type]].withDefaultValue(Set.empty)
  private val dtorSrcs = LinkedHashMap.empty[ConcreteConsumer, Set[ConcreteProducer | NoProd.type]].withDefaultValue(Set.empty)
  
  val finalCtorDests = LinkedHashMap.empty[CtorDtorId, FinalDest]
  val finalDtorSrcs = LinkedHashMap.empty[CtorDtorId, Set[CtorDtorId]]
  val fusingCtorInfo = MutMap.empty[CtorDtorId, ConcreteProducer]
  val fusingDtorInfo = MutMap.empty[CtorDtorId, ConcreteConsumer]
  
  // propagate
  locally {
    val upperBounds = MutMap.empty[StratVarId, Ls[ConsStrat]].withDefaultValue(Nil)
    val lowerBounds = MutMap.empty[StratVarId, Ls[ProdStrat]].withDefaultValue(Nil)
    val cache = MutSet.empty[ProdStrat -> ConsStrat]
    def handle(constraint: ProdStrat -> ConsStrat): Unit = if cache.add(constraint) then
      assert:
        val (prod, cons) = constraint
        (!prod.isInstanceOf[Ctor] || prod.asInstanceOf[Ctor].instantiationId.isDefined) &&
        (!cons.isInstanceOf[Dtor] || cons.asInstanceOf[Dtor].instantiationId.isDefined) &&
        (!cons.isInstanceOf[FieldSel] || cons.asInstanceOf[FieldSel].instantiationId.isDefined)
      constraint match
      case (c: Ctor, d: Dtor) =>
        ctorDests(c) += d
        dtorSrcs(d) += c
      case (c: Ctor, d: FieldSel) =>
        if d.isSelFromCls === c.ctor then
          ctorDests(c) += d
          dtorSrcs(d) += c
          handle(
            c.args.find(_._1 is d.field).get._2,
            d.consVar)
      case (c: Ctor, NoCons) =>
        ctorDests(c) += NoCons
        for (_, argProd) <- c.args do handle(argProd, NoCons)
      case (ProdFun(argsP, resP), ConsFun(argsC, resC)) =>
        argsC.lazyZip(argsP).foreach(handle)
        handle(resP, resC)
      case (ProdFun(argsP, resP), NoCons) =>
        for a <- argsP do handle(NoProd, a)
        handle(resP, NoCons)
      case (NoProd, d: Dtor) =>
        dtorSrcs(d) += NoProd
      case (NoProd, sel: FieldSel) =>
        dtorSrcs(sel) += NoProd
        handle(NoProd, sel.consVar)
      case (NoProd, ConsFun(args, res)) =>
        for a <- args do handle(a, NoCons)
        handle(NoProd, res)
      case (p: ProdVar, c) =>
        upperBounds(p.s.uid) ::= c
        for l <- lowerBounds(p.s.uid) do handle(l, c)
      case (p, c: ConsVar) =>
        lowerBounds(c.s.uid) ::= p
        for u <- upperBounds(c.s.uid) do handle(p, u)
      case _ => () // ignore other cases
    end handle
    
    for c <- collector.allConstraints do handle(c)
  }
  
  // remove clashes
  locally {
    val toRemoveCtor = MutSet.empty[ConcreteProducer]
    val toRemoveDtor = MutSet.empty[ConcreteConsumer]
    def markCtorToBeRemoved(rm: ConcreteProducer): Unit = if toRemoveCtor.add(rm) then
      for case dtor: ConcreteConsumer <- ctorDests(rm) do markDtorToBeRemoved(dtor)
    def markDtorToBeRemoved(rm: ConcreteConsumer): Unit = if toRemoveDtor.add(rm) then
      for case ctor: ConcreteProducer <- dtorSrcs(rm) do markCtorToBeRemoved(ctor)
    def mergeDests(dests: Set[ConcreteConsumer | NoCons.type]): Opt[FinalDest] =
      def selsSelectingTheSameSymbol(sels: Set[FieldSel]) =
        sels.map(s => s.field).size == 1
      if dests.contains(NoCons) then N
      else
        val (dtors, sels) = dests.partitionMap:
          case d: Dtor => Left(d)
          case fs: FieldSel => Right(fs)
          case _ => die
        if dtors.size == 0 && selsSelectingTheSameSymbol(sels) then
          S(FinalDestSel(
            sels.map(_.toCtorDtorId),
            sels.head.field
          ))
        else if dtors.size != 1 then N
        else
          val dtor = dtors.head
          if selAndDtorIsSameConsumer(
            dtor.toCtorDtorId,
            sels.map(s => s.toCtorDtorId)
          ) then
            S(FinalDestMatch(
              CtorDtorId(dtor.scrutExprId, dtor.instantiationId.get),
              sels.map: s =>
                CtorDtorId(s.exprId, s.instantiationId.get)
            ))
          else N
    end mergeDests
    
    // mark ctors to be removed
    for
      (ctor, dests) <- ctorDests
      if mergeDests(dests).isEmpty
    do markCtorToBeRemoved(ctor)
    // mark dtors to be removed
    for
      (dtor, srcs) <- dtorSrcs
      if srcs.contains(NoProd)
    do markDtorToBeRemoved(dtor)
    
    toRemoveCtor.foreach(ctorDests.remove)
    toRemoveDtor.foreach(dtorSrcs.remove)
    
    for (ctor, dests) <- ctorDests do
      finalCtorDests(ctor.toCtorDtorId) = mergeDests(dests).get
      fusingCtorInfo(ctor.toCtorDtorId) = ctor
    for (dtor, srcs) <- dtorSrcs do
      finalDtorSrcs(dtor.toCtorDtorId) =
        // srcs are always ConcreteProducers after constraint solving
        srcs.map(_.asInstanceOf[ConcreteProducer].toCtorDtorId)
      fusingDtorInfo(dtor.toCtorDtorId) = dtor
    
  }
  
  tl.log(">>> fusing >>>")
  for case (c, dest) <- finalCtorDests do
    tl.log(s"${c.pp} ->")
    dest match
    case FinalDestMatch(dtor, sels) =>
      tl.log(s"\t${dtor.pp}")
      for s <- sels do tl.log(s"\t${s.pp}")
    case FinalDestSel(dtors, field) =>
      tl.log(s"\t${field}")
  tl.log("<<< fusing <<<")
  
end DeforestConstrainSolver
