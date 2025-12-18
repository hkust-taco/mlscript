package hkmc2
package codegen

import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.utils.SymbolSubst
import hkmc2.Message.MessageContext

import syntax.{Literal, Tree, ParamBind}
import semantics.*
import semantics.Elaborator.ctx
import semantics.Elaborator.State
import hkmc2.Config.EffectHandlers

import scala.collection.mutable
import scala.util.boundary
import hkmc2.codegen.js.JSBuilder


/** - For function bodies, fuse all shallowly-nested scopes into one top-level one,
  *   because handler lowering relies on knowing all local variables in the function.
  * - Assert the absence of Label(loop = true) blocks,
  *   because loops should be rewritten to functions first,
  *   otherwise we cannot fuse scopes correctly.
  */
class PreHandlerLowering extends BlockTransformer(new SymbolSubst):
  override def applyBlock(b: Block): Block = b match
    case Label(_, loop, _, _) =>
      assert(!loop)
      super.applyBlock(b)
    case _ => super.applyBlock(b)
  
  private var scopedSymForCurrentFun: Option[collection.mutable.Set[Symbol]] = None
  override def applyFunBodyLikeBlock(b: Block): Block =
    val prevScopedSymForCurrentFun = scopedSymForCurrentFun
    val resBlk = b match
      case Scoped(syms, body) =>
        scopedSymForCurrentFun = Some(collection.mutable.Set.from(syms))
        val newBody = applySubBlock(body)
        new Scoped(scopedSymForCurrentFun.get, newBody)
      case _ =>
        scopedSymForCurrentFun = Some(collection.mutable.Set.empty[Symbol])
        val newBlk = applySubBlock(b)
        Scoped(scopedSymForCurrentFun.get, newBlk)
    scopedSymForCurrentFun = prevScopedSymForCurrentFun
    resBlk
  
  override def applyScopedBlock(b: Block): Block = b match
    case Scoped(syms, body) =>
      scopedSymForCurrentFun match
        case None => super.applyScopedBlock(b)
        case Some(scopedForCurrentFun) =>
          scopedForCurrentFun.addAll(syms)
          applySubBlock(body)
    case _ => applySubBlock(b)
    

object HandlerLowering:
  private val pcIdent: Tree.Ident = Tree.Ident("pc")
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val lastIdent: Tree.Ident = Tree.Ident("last")
  private val contTraceIdent: Tree.Ident = Tree.Ident("contTrace")
  private def unit = Value.Lit(Tree.UnitLit(true))
  private def intLit(i: BigInt) = Value.Lit(Tree.IntLit(i))

  private def locToStr(loc: Loc) =
    val (line, _, col) = loc.origin.fph.getLineColAt(loc.spanStart)
    Value.Lit(Tree.StrLit(s"${loc.origin.fileName.last}:${line + loc.origin.startLineNum - 1}:$col"))
  
  extension (p: Path)
    def pc = p.selN(pcIdent)
    def value = p.selN(Tree.Ident("value"))
    def next = p.selN(nextIdent)
    def last = p.selN(lastIdent)
    def contTrace = p.selN(contTraceIdent)
  
  private case class LinkState(res: Local, cls: Path, uid: Path)
  
  type FnOrCls = Either[BlockMemberSymbol, DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol]

  private enum HandlerCtx:
    // currentFun: path to the current function for resumption
    // thisPath: path to `this` binding if the function is a method, `this` will be rebinded on resumption
    // plCnt: how many times to call this function for resumption, as we have arbitrary number of parameter lists
    // currentLocals: All locals to be saved and reloaded, this cannot include any variables in outer scopes
    // currentStackSafetySym: The symbol to be used for stack safety
    case FunctionLike(ctx: FunctionCtx)
    case Ctor
    case ModCtor
    case TopLevel

    def isCtor = this === Ctor || this === ModCtor
    def isTopLevel = this === TopLevel
    def allowDefn = isTopLevel || this === ModCtor
  
  private case class FunctionCtx(currentFun: Path, thisPath: Option[Path], resumeInfo: ResumeInfo, debugInfo: DebugInfo):
    def doUnwind(path: Path, loc: Value, stateId: BigInt, restoreList: List[Local])(using paths: HandlerPaths) =
      Return(Call(paths.unwindPath, (
        path ::
        intLit(resumeInfo.plCnt) ::
        currentFun ::
        debugInfo.debugInfoPath ::
        loc ::
        intLit(stateId) ::
        thisPath.getOrElse(unit) ::
        intLit(restoreList.length) ::
        restoreList.map(_.asPath)
      ).map(_.asArg))(true, true, false), false)
  
  private case class ResumeInfo(
    plCnt: Int,
    currentLocals: List[Local],
    currentStackSafetySym: Opt[FnOrCls],
  )
  
  private case class DebugInfo(
    debugNme: Str,
    debugInfoPath: Path,
  )
  
  type StateId = BigInt

import HandlerLowering.*

class HandlerPaths(using Elaborator.State):
  val runtimePath: Path = State.runtimeSymbol.asPath
  val effectSigPath: Path = runtimePath.selSN("EffectSig").selSN("class")
  val effectSigSym: ClassSymbol = State.effectSigSymbol
  val contClsPath: Path = runtimePath.selSN("FunctionContFrame").selSN("class")
  val mkEffectPath: Path = runtimePath.selSN("mkEffect")
  val handleBlockImplPath: Path = runtimePath.selSN("handleBlockImpl")
  val stackDelayClsPath: Path = runtimePath.selSN("StackDelay")
  val topLevelEffectPath: Path = runtimePath.selSN("topLevelEffect")
  val ctorEffectPath: Path = runtimePath.selSN("ctorEffect")
  val enterHandleBlockPath: Path = runtimePath.selSN("enterHandleBlock")
  val stackDepthIdent = new Tree.Ident("stackDepth")
  val stackDepthPath: Path = runtimePath.selN(stackDepthIdent)
  val fnLocalsPath: Path = runtimePath.selSN("FnLocalsInfo").selSN("class")
  val localVarInfoPath: Path = runtimePath.selSN("LocalVarInfo").selSN("class")
  val unwindPath: Path = runtimePath.selSN("unwind")
  val isResuming: Path = runtimePath.selSN("isResuming")
  val resumePc: Path = runtimePath.selSN("resumePc")
  val resumeValueIdent = new Tree.Ident("resumeValue")
  val resumeValue: Path = runtimePath.selN(resumeValueIdent)

class HandlerLowering(paths: HandlerPaths, opt: EffectHandlers)(using TL, Raise, Elaborator.State, Elaborator.Ctx):
  
  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(N, dbgNme)
  
  private def rtThrowMsg(msg: Str) = Throw(
    Instantiate(mut = false, State.globalThisSymbol.asPath.selN(Tree.Ident("Error")),
    Value.Lit(Tree.StrLit(msg)).asArg :: Nil)
  )
  
  object PureCall:
    def apply(fun: Path, args: List[Path]) = Call(fun, args.map(Arg(N, _)))(true, false, false)
    def unapply(res: Result) = res match
      case Call(fun, args) => args.foldRight[Opt[List[Path]]](S(Nil)): (arg, acc) =>
          acc.flatMap: acc =>
            arg match
              case Arg(N, p) => S(p :: acc)
              case _ => N
        .map((fun, _))
      case _ => N
  
  object StateTransition:
    private val transitionSymbol = freshTmp("transition")
    def apply(uid: StateId) =
      Return(PureCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.Ref(`transitionSymbol`, _), List(Value.Lit(Tree.IntLit(uid)))), false) =>
        S(uid)
      case _ => N

  object Unwind:
    private val unwindSymbol = freshTmp("unwind")
    def apply(uid: StateId, loc: Value) =
      Return(PureCall(Value.Ref(unwindSymbol), List(Value.Lit(Tree.IntLit(uid)), loc)), false)
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.Ref(`unwindSymbol`, _), List(Value.Lit(Tree.IntLit(uid)), loc: Value)), false) =>
        S(uid, loc)
      case _ => N

  abstract class LazyId:
    private var id: Opt[StateId] = N
    protected def getImpl: StateId
    def get: StateId = id match
      case S(value) => value
      case N =>
        val value = getImpl
        id = S(value)
        value
    def isUsed: Bool = id.isDefined
    def transitionOrBlk(blk: => Block) =
      if isUsed then StateTransition(get) else blk
  
  private class IdAllocator:
    var id: Int = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
  
  // blk: the block of code within this state
  case class BlockPartition(blk: Block, resumable: Bool)
  case class PartitionedBlock(entry: StateId, states: Map[StateId, BlockPartition])

  object EffectfulResult:
    def unapply(r: Result) = r match
      case c: Call if c.mayRaiseEffects => S(r)
      case _: Instantiate => S(r)
      case _ => N
  
  private def partitionBlock(blk: Block)(using h: FunctionCtx): PartitionedBlock =
    val result = mutable.HashMap.empty[StateId, BlockPartition]
    val allocId = new IdAllocator()

    // * blk: The block to transform
    // * partitioned: whether we are already in a partitioned state
    // *              if we are not partitioned, we do not need to jump to afterEnd,
    // *              this is because we are still in the original block, which shares
    // *              the same code path.
    // * labelIds: maps label IDs to the state at the start of the label and the state after the label
    // * afterEnd: what state End should jump to, if at all
    def go(blk: Block)(using labelIds: Map[Symbol, (LazyId, LazyId)], afterEnd: Option[LazyId], partitioned: Bool): Block = boundary:
      // First check if the current block contain any non trivial call, if so we need a partition

      def forceId(blk: Block, resumable: Bool): StateId = blk match
        case StateTransition(uid) =>
          if !result(uid).resumable && resumable then
            result(uid) = BlockPartition(result(uid).blk, true)
          uid
        case _ =>
          val id = allocId()
          result(id) = BlockPartition(blk, resumable)
          id

      // sym: the local that stores the result
      def doNewEffectPartition(res: Result, rst: Block) =
        val stateId = forceId(go(rst)(using partitioned = true), true)
        val newBlock = blockBuilder
          .assignFieldN(paths.runtimePath, paths.resumeValueIdent, res)
          .ifthen(
            paths.resumeValue,
            Case.Cls(paths.effectSigSym, paths.effectSigPath),
            Unwind(stateId, res.toLoc.fold(unit)(locToStr(_)))
          )
          .rest(StateTransition(stateId))
        boundary.break(newBlock)
      class RestLazyId(rst: Block) extends LazyId:
        def getImpl: StateId = forceId(go(rst)(using partitioned = true), false)
        def transitionSoft: Block = transitionOrBlk(go(rst))

      val nonTrivialBlockChecker = new BlockDataTransformer(SymbolSubst()):
        override def applyBlock(b: Block) = b match
          // Special handling for tail calls
          case Return(c @ Call(fun, args), false) => b // Prevents the recursion into applyResult
          case _ => super.applyBlock(b)
        override def applyResult(r: Result)(k: Result => Block) = r match
          case EffectfulResult(r) =>
            doNewEffectPartition(r, k(paths.resumeValue))
          case _ => super.applyResult(r)(k)
      
      // If current block contains direct effectful result the following call will early exit.
      nonTrivialBlockChecker.applyBlock(blk)

      blk match

      case Match(scrut, arms, dflt, rest) =>
        val restId = RestLazyId(rest)
        val newArms = arms.map((cse, blkk) => (cse, go(blkk)(using afterEnd = S(restId))))
        val newDflt = dflt.map(blkk => go(blkk)(using afterEnd = S(restId)))
        Match(scrut, newArms, newDflt, restId.transitionSoft)

      case Label(label, loop, body, rest) =>
        val restId = RestLazyId(rest)
        val startId = new LazyId:
          def getImpl = allocId()
        val newBody = go(body)(using labelIds + (label -> (startId, restId)), S(restId))
        if startId.isUsed then
          result(startId.get) = BlockPartition(Begin(newBody, restId.transitionSoft), false)
          StateTransition(startId.get)
        else
          Label(label, loop, newBody, restId.transitionSoft)

      case Break(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return blk
          case S(value) => value
        if partitioned then
          StateTransition(end.get)
        else
          Break(label)

      case Continue(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return blk
          case S(value) => value
        if partitioned then
          StateTransition(start.get)
        else
          Continue(label)

      case Begin(sub, rest) =>
        val restId = RestLazyId(rest)
        val newSub = go(sub)(using afterEnd = S(restId))
        Begin(newSub, restId.transitionSoft)

      case End(_) =>
        if partitioned then
          afterEnd.fold(blk)(id => StateTransition(id.get))
        else
          blk

      // Currently, implicit returns are only used in top level and tail call of constructor
      // The former case never enters the partitioning function, so it must be the later case here.
      // We no longer handle the later case, hence we can ignore this case.
      // case Return(_, true) => afterEnd match
      //   case None => End()
      //   case Some(id) => StateTransition(id)

      // identity cases

      case Define(defn, rest) => Define(defn, go(rest))
      case Assign(lhs, rhs, rest) => Assign(lhs, rhs, go(rest))
      case blk @ AssignField(lhs, nme, rhs, rest) => AssignField(lhs, nme, rhs, go(rest))(blk.symbol)
      case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => AssignDynField(lhs, fld, arrayIdx, rhs, go(rest))
      case _: Return => blk

      // ignored cases
      case TryBlock(sub, finallyDo, rest) => ??? // ignore
      case Throw(_) => blk
      case Scoped(_, body) => go(body)
      case _: HandleBlock => lastWords("unexpected handleBlock") // already translated at this point

    val initId = allocId()
    // Note: initial part will only be resumed if stack safety is on.
    val initPart = BlockPartition(go(blk)(using Map(), N, false), opt.stackSafety.isDefined)
    result(initId) = initPart
    PartitionedBlock(initId, Map.from(result))

  private def computeRestoreList(parts: PartitionedBlock)(using ctx: FunctionCtx): List[Local] =
    val localSet = ctx.resumeInfo.currentLocals.toSet
    val result = mutable.HashSet.empty[Local]

    def traverseEntry(stateId: StateId) =
      val traversed = mutable.HashSet.empty[StateId]
      var initialized = Set.empty[Local]

      new BlockTraverserShallow():
        traversed += stateId
        applyBlock(parts.states(stateId).blk)
        override def applyBlock(blk: Block): Unit = blk match
          case Unwind(uid, loc) => ()
          case StateTransition(uid) =>
            if !traversed.contains(uid) && !parts.states(uid).resumable then
              traversed += stateId
              applyBlock(parts.states(uid).blk)
          case Assign(lhs, rhs, rest) =>
            applyResult(rhs)
            val saved = initialized
            initialized += lhs
            applyBlock(rest)
            initialized = saved
          case Define(defn: ValDefn, rest) =>
            applyPath(defn.rhs)
            val saved = initialized
            initialized += defn.sym
            applyBlock(rest)
            initialized = saved
          case Define(defn, rest) =>
            val saved = initialized
            initialized += defn.sym
            applyBlock(rest)
            initialized = saved
          case _ => super.applyBlock(blk)
        override def applySymbol(l: Symbol): Unit =
          if localSet.contains(l) && !initialized.contains(l) then
            result += l

    parts.states.foreach: (stateId, part) =>
      if part.resumable then traverseEntry(stateId)

    result.toList

  val doUnwindMap: mutable.Map[FnOrCls, Path => Return] = mutable.HashMap.empty
    
  /**
   * The actual translation:
   * 1. rewrite handler blocks in terms of classes and functions
   * 2. class lifter
   * 3. state machine transformation of all functions
   */
  

  private def translateBlock(blk: Block, h: HandlerCtx, scopedVars: collection.Set[Local]): Block =
    given HandlerCtx = h

    def translateFunLike(fun: FunDefn, funcPath: Path, thisPath: Option[Path], debugNme: Str) =
      val scopedVars = fun.body match
        case Scoped(syms, body) => syms
        case _ => Set()
      val varList = (scopedVars ++ fun.params.flatMap(_.params.map(_.sym)))
        .toList.sortBy(_.uid)
      val debugInfo = Value.Lit(Tree.StrLit(debugNme)).asArg :: varList.zipWithIndex.filter(_._1.isInstanceOf[VarSymbol])
        .flatMap: (sym, idx) =>
          List(intLit(idx), Value.Lit(Tree.StrLit(sym.nme)))
        .map(_.asArg)
      val debugInfoSym = freshTmp(s"$debugNme$$debugInfo")
      val newCtx = HandlerCtx.FunctionLike(FunctionCtx(funcPath, thisPath, ResumeInfo(fun.params.length, varList, S(L(fun.sym))),
        DebugInfo(debugNme, if opt.debug then debugInfoSym.asPath else unit)))
      val bod2 = translateBlock(fun.body, newCtx, scopedVars)
      val fun2 = if fun.body is bod2 then fun else
        FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, bod2)(fun.forceTailRec)
      (debugInfoSym, debugInfo, fun2)

    val subblockTransform = new BlockTransformer(SymbolSubst()):
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case fun: FunDefn =>
          if !h.allowDefn then
            raise(WarningReport(msg"Unexpected nested function: lambdas may not function correctly." -> fun.sym.toLoc :: Nil, source = Diagnostic.Source.Compilation))
          val (debugInfoSym, debugInfo, fun2) = translateFunLike(fun, Value.Ref(fun.sym, S(fun.dSym)), N, fun.sym.nme)
          if opt.debug then Assign(debugInfoSym, Tuple(false, debugInfo), k(fun2)) else k(fun2)
        case ClsLikeDefn(owner, isym, sym, kind, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor, companion, bufferable) =>
          if !h.allowDefn then
            raise(WarningReport(msg"Unexpected nested class: lambdas may not function correctly." -> isym.toLoc :: Nil, source = Diagnostic.Source.Compilation))
          val debugInfos = mutable.ArrayBuffer.empty[(Local, List[Arg])]
          val newMtds = methods.map: f =>
            val (debugInfoSym, debugInfo, fun2) = translateFunLike(f, Value.Ref(isym).sel(new Tree.Ident(f.sym.nme), f.sym.asTrm.get),
              S(Value.Ref(isym)), s"${sym.nme}#${f.sym.nme}")
            debugInfos += debugInfoSym -> debugInfo
            fun2
          val companion2 = companion.map: bod =>
            val newMtds = bod.methods.map: f =>
              val (debugInfoSym, debugInfo, fun2) = translateFunLike(f, Value.Ref(bod.isym).sel(new Tree.Ident(f.sym.nme), f.sym.asTrm.get),
                S(Value.Ref(bod.isym)), s"${sym.nme}.${f.sym.nme}")
              debugInfos += debugInfoSym -> debugInfo
              fun2
            // We cannot use this bc there is no subblock transform...
            // val newCtor = translateTrivialOrTopLevel(bod.ctor)
            // TODO: Companion's ctor is more well behaved so it is possible to handle it
            // However, JSBuilder inserts extra statements between preCtor and ctor and it's not possible to replicate the exact behavior
            // without many special handling.
            val newCtor = translateCtorLike(bod.ctor, bod.isym.asPath, true)
            tl.log(s"companion name: ${bod.isym.nme}")
            ClsLikeBody(bod.isym, newMtds, bod.privateFields, bod.publicFields, newCtor)
          val c2 = ClsLikeDefn(owner, isym, sym, kind, paramsOpt, auxParams, parentPath, newMtds, privateFields, publicFields,
            translateCtorLike(preCtor, isym.asPath, false), translateCtorLike(ctor, isym.asPath, false), companion2, bufferable)
          if opt.debug then
            debugInfos.foldRight(k(c2)): (elem, blk) =>
              Assign(elem._1, Tuple(false, elem._2), blk)
          else k(c2)
        case _ => super.applyDefn(defn)(k)
    val b = subblockTransform.applyBlock(blk)
    if h.isCtor then
      return translateTopLevelOrCtor(b, res => Call(paths.ctorEffectPath, res.asArg :: Nil)(true, true, false))
    if h.isTopLevel then
      return translateTopLevelOrCtor(b, res => Call(paths.topLevelEffectPath, res.asArg :: Value.Lit(Tree.BoolLit(opt.debug)).asArg :: Nil)(true, false, false))
    val ctx = h.asInstanceOf[HandlerCtx.FunctionLike].ctx
    given FunctionCtx = ctx
    val parts = partitionBlock(b)
    if parts.states.size <= 1 && opt.stackSafety.isEmpty then
      return b
    val vars = if opt.debug then ctx.resumeInfo.currentLocals else computeRestoreList(parts)
    ctx.resumeInfo.currentStackSafetySym.foreach: fnOrCls =>
      doUnwindMap +=
        fnOrCls -> (res => ctx.doUnwind(res, fnOrCls.fold(_.toLoc, _.toLoc).fold(unit)(locToStr(_)), parts.entry, vars)(using paths))

    val pcVar = freshTmp("pc")
    val mainLoopLbl = freshTmp("main")

    val postTransform = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block) = b match
        case StateTransition(uid) =>
          Assign(pcVar, Value.Lit(Tree.IntLit(uid)), Continue(mainLoopLbl))
        case Unwind(uid, loc) =>
          ctx.doUnwind(paths.resumeValue, loc, uid, vars)(using paths)
        case _ => super.applyBlock(b)

    val arms = parts.states.toList.map: (id, part) =>
      Case.Lit(Tree.IntLit(id)) ->
        postTransform.applyBlock(part.blk)

    val mainLoop =
      if parts.states.size <= 1 then
        postTransform.applyBlock(parts.states.head._2.blk)
      else
        Label(mainLoopLbl, true, Match(Value.Ref(pcVar), arms, N, End()), End())

    val getSavedTmp = freshTmp("saveOffset")
    def getSaved(off: BigInt): (Block => Block, Path) =
      if off == 0 then
        return (id, DynSelect(paths.runtimePath.selSN("resumeArr"), paths.runtimePath.selSN("resumeIdx"), true))
      val computeOff = Assign(getSavedTmp, Call(State.builtinOpsMap("+").asPath, paths.runtimePath.selSN("resumeIdx").asArg :: intLit(off).asArg :: Nil)(false, false, false), _)
      (computeOff, DynSelect(paths.runtimePath.selSN("resumeArr"), getSavedTmp.asPath, true))

    val restoreVars = vars.zipWithIndex.foldLeft(blockBuilder.assign(pcVar, paths.resumePc).chain(Scoped(Set(getSavedTmp), _))):
      case (builder, (local, idx)) =>
        val (computeOff, savePath) = getSaved(idx)
        builder.chain(computeOff).assign(local, savePath)
    
    Scoped(
      scopedVars ++ Set(pcVar),
      Match(
        paths.isResuming,
        Case.Lit(Tree.BoolLit(true)) ->
          restoreVars
            .assignFieldN(paths.runtimePath, new Tree.Ident("isResuming"), Value.Lit(Tree.BoolLit(false))).end :: Nil,
        S(Assign(pcVar, intLit(parts.entry), End())),
        mainLoop))
  
  private def translateCtorLike(b: Block, thisPath: Path, isModCtor: Bool)(using h: HandlerCtx): Block =
    translateBlock(b, if isModCtor then HandlerCtx.ModCtor else HandlerCtx.Ctor, Set.empty)

  private def translateTopLevelOrCtor(b: Block, onEffect: Path => Call)(using HandlerCtx): Block =
    def topLevelCheck(l: Local, r: Result, rst: Block): Block =
      blockBuilder
        .assign(l, r)
        .ifthen(
          l.asPath,
          Case.Cls(paths.effectSigSym, paths.effectSigPath),
          Assign(l, onEffect(l.asPath), End()),
          N)
        .rest(rst)
    val topLevelTransform = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block) = b match
        case Assign(lhs, EffectfulResult(r), rest) =>
          // Optimization to reuse lhs instead of fresh local
          topLevelCheck(lhs, r, applyBlock(rest))
        case _ => super.applyBlock(b)
      override def applyResult(r: Result)(k: Result => Block) = r match
        case EffectfulResult(r) =>
          // Fallback case, this may lead to unnecessary assignments if it is assign-like
          val l = freshTmp()
          Scoped(Set(l), topLevelCheck(l, r, k(Value.Ref(l))))
        case _ => super.applyResult(r)(k)
    topLevelTransform.applyBlock(b)
  
  // Handle block is rewritten into:
  // 1. Instantiation of the handler
  // 2. An effectful call to enterHandleBlock
  private def translateHandleBlockShallow(h: HandleBlock): Block =
    val sym = new BlockMemberSymbol("handleBlock$", Nil, false)

    val bodyDefn = FunDefn.withFreshSymbol(N, sym, PlainParamList(Nil) :: Nil, h.body)(false)
    
    val handlerMtds = h.handlers.map: handler =>
      val sym = BlockMemberSymbol(h.cls.nme + handler.sym.nme, Nil, true)
      val fDef = FunDefn.withFreshSymbol(
        N, sym, PlainParamList(Param(FldFlags.empty, handler.resumeSym, N, Modulefulness.none) :: Nil) :: Nil,
        handler.body
        )(false)
      FunDefn.withFreshSymbol(
        S(h.cls),
        handler.sym,
        handler.params,
        Define(
          fDef,
          Return(PureCall(paths.mkEffectPath, h.cls.asPath :: Value.Ref(sym, S(fDef.dSym)) :: Nil), false)))(false)

    val clsDefn = ClsLikeDefn(
      N, // no owner
      h.cls,
      BlockMemberSymbol(h.cls.id.name, Nil),
      syntax.Cls,
      N, Nil,
      S(h.par), handlerMtds, Nil, Nil,
      // Apparently, the lifter is not happy with any assignment in the preCtor...
      Return(Call(Value.Ref(State.builtinOpsMap("super")), h.args.map(_.asArg))(true, true, false), true),
      End(),
      N,
      N,
    )

    blockBuilder
      .define(clsDefn)
      .assign(h.lhs, Instantiate(mut = true, Value.Ref(clsDefn.sym, S(h.cls)), Nil))
      .define(bodyDefn)
      .assign(h.res, Call(paths.enterHandleBlockPath, List(h.lhs.asPath.asArg, Value.Ref(sym, S(bodyDefn.dSym)).asArg))(true, true, false))
      .rest(h.rest)
  
  def translateHandleBlocks(b: Block): Block =

    val transform = new BlockTransformer(SymbolSubst()):
      override def applyBlock(b: Block) = b match
        case HandleBlock(lhs, res, par, args, cls, hdr, bod, rst) =>
          val hdr2 = hdr.map(applyHandler)
          val bod2 = applySubBlock(bod)
          val rst2 = applySubBlock(rst)
          translateHandleBlockShallow(new HandleBlock(lhs, res, par, args, cls, hdr2, bod2, rst2))
        case _ => super.applyBlock(b)
    transform.applyBlock(b)

  def translateTopLevel(b: Block): (Block, collection.Map[FnOrCls, Path => Return]) =
    doUnwindMap.clear()
    val preTransformed = new PreHandlerLowering().applyBlock(b)
    val ctx = HandlerCtx.TopLevel
    val transformed = translateBlock(preTransformed, ctx, Set.empty)
    (transformed, doUnwindMap)
    
