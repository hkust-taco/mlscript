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

object HandlerLowering:

  private val pcIdent: Tree.Ident = Tree.Ident("pc")
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val lastIdent: Tree.Ident = Tree.Ident("last")
  private val contTraceIdent: Tree.Ident = Tree.Ident("contTrace")
  
  extension (p: Path)
    def pc = p.selN(pcIdent)
    def value = p.selN(Tree.Ident("value"))
    def next = p.selN(nextIdent)
    def last = p.selN(lastIdent)
    def contTrace = p.selN(contTraceIdent)
    
  extension (b: Block) def userDefinedVars: Set[Local] = b.definedVars.collect:
    case s: VarSymbol => s
        
  private case class LinkState(res: Local, cls: Path, uid: Path)
  
  type FnOrCls = Either[BlockMemberSymbol, DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol]
  
  // TODO: Fix these comments
  // isTopLevel:
  // whether the current block is the top level block, as we do not emit code for continuation class on the top level
  // since we cannot return an effect signature on the top level (we are not in a function so return statement are invalid)
  // contName: the name of the continuation class
  // ctorThis: the path to `this` in the constructor, this is used to insert `return this;` at the end of constructor.
  // linkAndHandle:
  // a function that takes a LinkState and returns a block that links the continuation class and handles the effect
  // this is a convenience function which initializes the continuation class in function context or throw an error in top level
  private case class HandlerCtx(
      currentFun: Opt[Path],
      thisPath: Option[Path],
      debugInfo: DebugInfo,
  ):
    def nestDebugScope(locals: Set[Local], localsFn: Path) = copy(debugInfo = debugInfo.copy(inScopeLocals =
      debugInfo.inScopeLocals ++ locals, prevLocalsFn = S(localsFn)))
    def isTopLevel = currentFun.isEmpty
  
  // inScopeLocals: Local variables that are in scope.
  // prevLocalsFn: The function that gets the outer function's locals.
  private case class DebugInfo(
    debugNme: Str,
    inScopeLocals: Set[Local],
    prevLocalsFn: Opt[Path],
  )
  
  private object DebugInfo:
    def topLevel(debugNme: Str) = DebugInfo(debugNme, Set.empty, N)
  
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
  val enterHandleBlockPath: Path = runtimePath.selSN("enterHandleBlock")
  val stackDepthIdent = new Tree.Ident("stackDepth")
  val stackDepthPath: Path = runtimePath.selN(stackDepthIdent)
  val fnLocalsPath: Path = runtimePath.selSN("FnLocalsInfo").selSN("class")
  val localVarInfoPath: Path = runtimePath.selSN("LocalVarInfo").selSN("class")
  
  def isHandlerClsPath(p: Path) =
    (p eq contClsPath)  || (p eq stackDelayClsPath) || (p eq effectSigPath)

class HandlerLowering(paths: HandlerPaths, opt: EffectHandlers)(using TL, Raise, Elaborator.State, Elaborator.Ctx):

  private def funcLikeHandlerCtx(funcPath: Path, thisPath: Option[Path], debugNme: Str)(using h: HandlerCtx) =
    HandlerCtx(S(funcPath), thisPath, h.debugInfo.copy(debugNme))

  private def functionHandlerCtx(funcPath: Path, debugNme: Str)(using HandlerCtx) = funcLikeHandlerCtx(funcPath, N, debugNme)
  private def topLevelCall(state: LinkState) = Call(
      paths.topLevelEffectPath, 
      state.res.asPath.asArg :: Value.Lit(Tree.BoolLit(opt.debug)).asArg :: Nil
    )(true, false)
  private def topLevelCtx(nme: Str, debugNme: Str) = HandlerCtx(N, N, DebugInfo.topLevel(debugNme))
  private def ctorCtx(bms: BlockMemberSymbol, cls: ClassSymbol, debugNme: Str)(using HandlerCtx) = funcLikeHandlerCtx(Value.Ref(bms, S(cls)), S(Value.Ref(cls)), debugNme)
  
  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(N, dbgNme)
  
  private def rtThrowMsg(msg: Str) = Throw(
    Instantiate(mut = false, State.globalThisSymbol.asPath.selN(Tree.Ident("Error")),
    Value.Lit(Tree.StrLit(msg)).asArg :: Nil)
  )
  
  object PureCall:
    def apply(fun: Path, args: List[Path]) = Call(fun, args.map(Arg(N, _)))(true, false)
    def unapply(res: Result) = res match
      case Call(fun, args) => args.foldRight[Opt[List[Path]]](S(Nil)): (arg, acc) =>
          acc.flatMap: acc =>
            arg match
              case Arg(N, p) => S(p :: acc)
              case _ => N
        .map((fun, _))
      case _ => N
  
  object ReturnCont:
    private val returnContSymbol = freshTmp("returnCont")
    def apply(res: Local, uid: StateId) =
      Assign(res, PureCall(Value.Ref(returnContSymbol), List(Value.Lit(Tree.IntLit(uid)))), End(""))
    def unapply(blk: Block) = blk match
      case Assign(res, PureCall(Value.Ref(`returnContSymbol`, _), List(Value.Lit(Tree.IntLit(uid)))), _) =>
        Some(res, uid)
      case _ => None
  
  object StateTransition:
    private val transitionSymbol = freshTmp("transition")
    def apply(uid: StateId) =
      Return(PureCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.Ref(`transitionSymbol`, _), List(Value.Lit(Tree.IntLit(uid)))), false) =>
        S(uid)
      case _ => N
  
  private class FreshId:
    // IMPORTANT: this must be >= 1 otherwise we get state ID collions with the "entry" state 0.
    var id: Int = 1
    def apply() =
      val tmp = id
      id += 1
      tmp
  private val freshId = FreshId()
  
  // blk: the block of code within this state
  // sym: the variable to which the resumed value should set
  case class BlockPartition(blk: Block, sym: Opt[Local])
  type PartitionedBlock = Map[StateId, BlockPartition]
  
  // Tries to remove states that jump directly to other states
  // Note: Currently it doesn't seem to do anything, so it's not used. Maybe the states are already pretty optimal.
  /*
  def optParts(entryState: BlockState, states: Ls[BlockState]): (BlockState, Ls[BlockState]) =
    val statesMap = (entryState :: states).map(state => state.id -> state).toMap
    def findEdges(state: BlockState) =
      var edges: List[BlockState] = Nil
      new BlockTraverser:
        applyBlock(state.blk)
        override def applyBlock(b: Block): Unit = b match
          case StateTransition(id) => edges ::= statesMap(id)
          case _ => super.applyBlock(b)
      state.id -> edges
    // build edges
    val edges = (entryState :: states).map(findEdges).toMap
    // assume that all states are reachable from the entry point
    var dests: Map[StateId, StateId] = Map.empty
    var visited: Set[StateId] = Set.empty
    
    // whether a state purely jumps to another state, and if so, which state it jumps to
    def getJmp(state: BlockState): Opt[StateId] =
      if state.sym.isDefined then N
      else state.blk match
        case StateTransition(id) => S(id)
        case _ => N
    
    // build the `dests` map by doing a dfs from the entry state
    def dfs(state: BlockState): Unit =
      visited += state.id
      getJmp(state) match
        case None => ()
        case Some(value) =>
          dests += (state.id -> value)
      for e <- edges(state.id) do
        if !visited.contains(e.id) then
          dfs(e)
    dfs(entryState)
    
    // cycles should be impossible -- if there are, just don't bother
    val sorted = 
      try topologicalSort(dests).toList
      catch case c: CyclicGraphError => 
        return (entryState, states)
    
    var finalDests: Map[StateId, StateId] = Map.empty
    def dp(state: StateId): StateId = finalDests.get(state) match
      case Some(value) => value
      case None =>
        val ret = dests.get(state) match
          case None => state
          case Some(dest) => dp(dest)
        finalDests += (state -> ret)
        ret
    
    val transformer = new BlockTransformer(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case StateTransition(uid) => StateTransition(dp(uid))
        case _ => super.applyBlock(b)
    
    def rewriteState(s: BlockState) = s.copy(blk = transformer.applyBlock(s.blk))
    
    val rewrittenEntry = rewriteState(entryState)
    val rewrittenStates = states.map(rewriteState)
    
    (rewrittenEntry, rewrittenStates)
  */
  
  // removes states that are not reachable from any resumption point (no longer in use as we always include everything)
  // def removeUselessStates(states: PartitionedBlock): PartitionedBlock =
  //   def findEdges(part: BlockPartition) =
  //     val edges: mutable.Set[StateId] = mutable.Set.empty
  //     new BlockTraverser:
  //       applyBlock(part.blk)
  //       override def applyBlock(b: Block): Unit = b match
  //         case StateTransition(id) => edges += id
  //         case _ => super.applyBlock(b)
  //     edges
  //   // build edges
  //   val edges = states.map((id, part) => id -> findEdges(part))

  //   val visited: mutable.Set[StateId] = mutable.Set.empty
  //   val remaining: mutable.Set[StateId] = mutable.Set.from(states.flatMap(part => part._2.sym.fold(N)(_ => S(part._1))))

  //   def dfs(state: StateId): Unit =
  //     visited += state
  //     remaining -= state
  //     for e <- edges(state) do
  //       if !visited.contains(e) then dfs(e)

  //   while !remaining.isEmpty do
  //     dfs(remaining.head)

  //   states.filter(state => visited.contains(state._1))

  object EffectfulResult:
    def unapply(r: Result) = r match
      case c: Call if c.mayRaiseEffects => S(r)
      case _: Instantiate => S(r)
      case _ => N
  
  def partitionBlock(blk: Block): PartitionedBlock =
    val result = mutable.HashMap.empty[StateId, BlockPartition]
    val freshId = FreshId()

    // * returns (truncated input block, child block states)
    // * blk: The block to transform
    // * labelIds: maps label IDs to the state at the start of the label and the state after the label
    // * afterEnd: what state End should jump to, if at all 
    // TODO: don't split within Match, Begin and Labels when not needed, ideally keep it intact.
    // Need careful analysis for this.
    def go(blk: Block)(using labelIds: Map[Symbol, (StateId, StateId)], afterEnd: Option[StateId]): Block = boundary:
      // First check if the current block contain any non trivial call, if so we need a partition

      // sym: the local that stores the result
      def doNewPartition(sym: Local, res: Result, rst: Block) =
        val stateId = freshId()
        result(stateId) = BlockPartition(go(rst), S(sym))
        val newBlock = blockBuilder
          .assign(sym, res)
          .ifthen(
            sym.asPath,
            Case.Cls(paths.effectSigSym, paths.effectSigPath),
            // TODO: ReturnCont may be unnecessary if we pass down related variables information to here.
            ReturnCont(sym, stateId)
          )
          .rest(StateTransition(stateId))
        boundary.break(newBlock)
      val nonTrivialBlockChecker = new BlockDataTraverser():
        override def applyBlock(b: Block) = b match
          // Special handling for tail calls
          case Return(c @ Call(fun, args), false) => () // Prevents the recursion into applyResult
          case Assign(lhs, EffectfulResult(r), rest) =>
            // Optimization to reuse lhs instead of fresh local
            doNewPartition(lhs, r, rest)
        override def applyResult(r: Result)(k: Result => Block) = r match
          case EffectfulResult(r) =>
            // Fallback case, this may lead to unnecessary vars if it is assign-like
            // FIXME: This fall back case might be not needed at all.
            val l = freshTmp()
            doNewPartition(l, r, k(Value.Ref(l)))
      
      // If current block contains direct effectful result the following call will early exit.
      nonTrivialBlockChecker.applyBlock(blk)

      blk match

      case Match(scrut, arms, dflt, rest) =>
        val newRest = go(rest)
        val restId: StateId = newRest match
          case StateTransition(uid) => uid
          case _ =>
            val id = freshId()
            result(id) = BlockPartition(newRest, N)
            id
        val newArms = arms.map((cse, blkk) => (cse, go(blkk)(using afterEnd = S(restId))))
        val newDflt = dflt.map(blkk => go(blkk)(using afterEnd = S(restId)))
        Match(scrut, newArms, newDflt, StateTransition(restId))

      case Label(label, loop, body, rest) =>
        val startId = freshId() // start of body
        val newRest = go(rest)
        val endId: StateId = newRest match // start of rest
          case StateTransition(uid) => uid
          case _ =>
            val id = freshId()
            result(id) = BlockPartition(newRest, N)
            id
        val newBody = go(body)(using labelIds + (label -> (startId, endId)), S(endId))
        StateTransition(startId)

      case Break(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return blk
          case S(value) => value
        StateTransition(end)

      case Continue(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return blk
          case S(value) => value
        StateTransition(start)

      // An optimization to omit useless state
      case Begin(End(_), blk) => go(blk)

      case Begin(sub, rest) =>
        val newRest = go(rest)
        newRest match
          case StateTransition(uid) => go(sub)(using afterEnd = S(uid))
          case _ =>
            val id = freshId()
            result(id) = BlockPartition(newRest, N)
            go(sub)(using afterEnd = S(id))

      case End(_) => afterEnd match
        case None => blk
        case Some(id) => StateTransition(id)

      // Currently, implicit returns are only used in top level and tail call of constructor
      // The former case never enters the partitioning function, so it must be the later case here.
      // If the constructor is non-trivial, we will append `return thisVar;` afterwards.
      // Erasing the implicit return early here is sound since trivial constructor will
      // do the trivial transformation instead of continuing the instrumentation.
      case Return(_, true) => afterEnd match
        case None => End()
        case Some(id) => StateTransition(id)

      // identity cases

      case Define(defn, rest) => Define(defn, go(rest))
      case Assign(lhs, rhs, rest) => Assign(lhs, rhs, go(rest))
      case blk @ AssignField(lhs, nme, rhs, rest) => AssignField(lhs, nme, rhs, go(rest))(blk.symbol)
      case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => AssignDynField(lhs, fld, arrayIdx, rhs, go(rest))
      case _: Return => blk

      // ignored cases
      case TryBlock(sub, finallyDo, rest) => ??? // ignore
      case Throw(_) => blk
      case _: HandleBlock => lastWords("unexpected handleBlock") // already translated at this point

    val initId = freshId()
    result(initId) = BlockPartition(go(blk)(using Map(), N), N)
    Map.from(result)
  
  // extraLocals is used for things like immutable parameters, they are not mutated but they should still be added as locals for debugging
  private def createGetLocalsFn(b: Block, extraLocals: Set[Local] = Set.empty)(using h: HandlerCtx) =
    val locals = (b.userDefinedVars ++ extraLocals) -- h.debugInfo.inScopeLocals
    val localsInfo = locals.toList.sortBy(_.uid).map: s =>
      FlowSymbol(s.nme) -> Instantiate(mut = true, paths.localVarInfoPath,
        Value.Lit(Tree.StrLit(s.nme)).asArg :: s.asPath.asArg :: Nil
      )
    val startSym = FlowSymbol("prev")
    val thisInfo = FlowSymbol("thisInfo")
    val arrSym = TempSymbol(N, "arr")
    
    val body = blockBuilder
      .assign(startSym, h.debugInfo.prevLocalsFn match
          case None => Tuple(mut = true, Nil)
          case Some(value) => PureCall(value, Nil)
        )
      .foldLeft(localsInfo):
        case (acc, (sym, res)) => acc.assign(sym, res)
      .assign(arrSym, Tuple(mut = false, localsInfo.map(v => v._1.asPath.asArg)))
      .assign(thisInfo, Instantiate(mut = true, paths.fnLocalsPath,
          Value.Lit(Tree.StrLit(h.debugInfo.debugNme)).asArg
            :: Value.Ref(arrSym).asArg
            :: Nil
        ))
      .assign(TempSymbol(N, ""), Call(startSym.asPath.selSN("push"), thisInfo.asPath.asArg :: Nil)(false, false))
      .ret(startSym.asPath)

    FunDefn(N, BlockMemberSymbol("getLocals", Nil), PlainParamList(Nil) :: Nil, body)
    
  var doUnwindMap: Map[FnOrCls, Path] = Map.empty
    
  /**
   * The actual translation:
   * 1. add call markers. rewrite handler blocks in terms of classes and functions
   * 2. add debug methods
   * 3. class lifter
   * 4. state machine transformation of all functions. add unwind and resume state
   *    generate normal function body
   */
  

  private def translateBlock(blk: Block, h: HandlerCtx): Block =
    val subblockTransform = new BlockTransformer(SymbolSubst()):
      override def applyFunDefn(fun: FunDefn): FunDefn =
        val bod2 = translateBlock(fun.body, functionHandlerCtx(Value.Ref(fun.sym, N), fun.sym.nme))
        if fun.body is bod2 then fun else
        FunDefn(fun.owner, fun.sym, fun.params, bod2)
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case ClsLikeDefn(owner, isym, sym, kind, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor, companion, bufferable) =>
          val newMtds = methods.map: f =>
            val bod2 = translateBlock(f.body, funcLikeHandlerCtx(Value.Ref(isym).sel(new Tree.Ident(f.sym.nme), f.sym.asTrm.get), S(Value.Ref(isym)), s"${sym.nme}.${f.sym.nme}"))
            if f.body is bod2 then f else
            FunDefn(f.owner, f.sym, f.params, bod2)
          val newCtor = translateBlock(Begin(preCtor, ctor), ctorCtx(sym, sym.asCls.get, s"‹constructor of ${sym.nme}›"))
          k(ClsLikeDefn(owner, isym, sym, kind, paramsOpt, auxParams, parentPath, newMtds, privateFields, publicFields, End(), newCtor, companion, bufferable))
        case _ => super.applyDefn(defn)(k)
    val b = subblockTransform.applyBlock(blk)

    val getLocalsFn = createGetLocalsFn(b)(using h)
    // All the defined variables are masked away from the inner scope (TODO: Scoped)
    given HandlerCtx = h.nestDebugScope(b.definedVars, getLocalsFn.sym.asPath)
    if h.isTopLevel then
      return translateTrivialOrTopLevel(b)
    val parts = partitionBlock(b)
    if parts.size <= 1 then
      return translateTrivialOrTopLevel(b)

    val stage1 = firstPass(b)
    val stage1 = tl.trace("=>" + b.showAsTree):
      val t = firstPass(b)
      tl.log("=<" + t.showAsTree)
      t
    val stage2 = if opt.debug then Define(getLocalsFn, stage1) else stage1
    // val stage2 = secondPass(stage1, fnOrCls, callSelf, getLocalsFn)
    if h.isTopLevel then stage2 else thirdPass(stage2)
  
  private def translateTrivialOrTopLevel(b: Block)(using HandlerCtx): Block =
    // We shall add back the top level effect checks here
    // If said block is trivial, this function will still add the debug information, for in the case where the error
    // is raised in a tail call.
    b
  
  // private def firstPass(b: Block)(using HandlerCtx): Block =
  //   val getLocalsSym = ctx.builtins.debug.getLocals
  //   val transformer = new BlockTransformerShallow(SymbolSubst()):
  //     // FIXME: there is a HUGE amount of error-prone, maintenance-heavy manually duplicated code in there to refactor
  //     override def applyBlock(b: Block) = b match
  //       case b: HandleBlock =>
  //         die
  //       // This block optimizes tail-calls in the handler transformation. We do not optimize implicit returns.
  //       // Implicit returns are used in top level and constructor:
  //       // For top level, this correspond to the last statement which should also be checked for effect.
  //       // For constructor, we will append `return this;` after the implicit return so it is not a tail call.
  //       case Return(c @ Call(fun, args), false) if !handlerCtx.isHandlerBody =>
  //         applyPath(fun): fun2 =>
  //           applyArgs(args): args2 =>
  //             val c2 = if (fun2 is fun) && (args2 is args) then c else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects)
  //             if c2 is c then b else Return(c2, false)
  //       // Optimization to avoid generation of unnecessary variables
  //       case Assign(lhs, c @ Call(fun, args), rest) if c.mayRaiseEffects =>
  //         applyPath(fun): fun2 =>
  //           applyArgs(args): args2 =>
  //             val c2 = if (fun2 is fun) && (args2 is args) then c else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects)
  //             ResultPlaceholder(lhs, freshId(), c2, applyBlock(rest))
  //       case Assign(lhs, c @ Instantiate(mut, cls, args), rest) =>
  //         applyPath(cls): cls2 =>
  //           applyArgs(args): args2 =>
  //             val c2 = if (cls2 is cls) && (args2 is args) then c else Instantiate(mut, cls2, args2)
  //             ResultPlaceholder(lhs, freshId(), c2, applyBlock(rest))
  //       case _ => super.applyBlock(b)
  //     override def applyResult(r: Result)(k: Result => Block): Block = r match
  //       case c @ Call(fun, args) if c.mayRaiseEffects =>
  //         val res = freshTmp("res")
  //         applyPath(fun): fun2 =>
  //           applyArgs(args): args2 =>
  //             val c2 = if (fun2 is fun) && (args2 is args) then c else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects)
  //             ResultPlaceholder(res, freshId(), c2, k(Value.Ref(res)))
  //       case c @ Instantiate(mut, cls, args) =>
  //         val res = freshTmp("res")
  //         applyPath(cls): cls2 =>
  //           applyArgs(args): args2 =>
  //             val c2 = if (cls2 is cls) && (args2 is args) then c else Instantiate(mut, cls2, args2)
  //             ResultPlaceholder(res, freshId(), c2, k(Value.Ref(res)))
  //       case r => super.applyResult(r)(k)
  //     override def applyPath(p: Path)(k: Path => Block): Block = p match
  //       case Value.Ref(`getLocalsSym`, _) => k(handlerCtx.debugInfo.prevLocalsFn.get) // TODO: Port debug to new transformation
  //       case _ => super.applyPath(p)(k)
  //     override def applyLam(lam: Lambda): Lambda =
  //       // This should normally be unreachable due to prior desugaring of lambda
  //       raise(InternalError(msg"Unexpected lambda during handler lowering" -> lam.toLoc :: Nil,
  //         source = Diagnostic.Source.Compilation))
  //       Lambda(lam.params, translateBlock(lam.body, lam.params.paramSyms.toSet, N, L(BlockMemberSymbol("", Nil, false)), functionHandlerCtx(s"Cont$$lambda$$", "‹lambda›")))
  //     override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
  //       case f: FunDefn => k(translateFun(f))
  //       case c: ClsLikeDefn => k(translateCls(c))
  //       case _: ValDefn => super.applyDefn(defn)(k)
  //   transformer.applyBlock(b)
    
  private def secondPass(b: Block, fnOrCls: FnOrCls, callSelf: Opt[Result], getLocalsFn: FunDefn)(using h: HandlerCtx): Block =
    // val cls = if handlerCtx.isTopLevel then N else genContClass(b, callSelf)

    val ret =
      if handlerCtx.isTopLevel then genNormalBody(b, N)
      else
        // create the doUnwind function
        val doUnwindSym = BlockMemberSymbol("doUnwind", Nil, true)
        doUnwindMap += fnOrCls -> doUnwindSym.asPath
        val pcSym = VarSymbol(Tree.Ident("pc"))
        val resSym = VarSymbol(Tree.Ident("res"))
        val doUnwindBlk = h.linkAndHandle(
          LinkState(resSym, paths.contClsPath, pcSym.asPath)
        )
        val doUnwindDef = FunDefn(
          N, doUnwindSym,
          PlainParamList(Param.simple(resSym) :: Param.simple(pcSym) :: Nil) :: Nil,
          doUnwindBlk
        )
        val doUnwindLazy = Lazy(doUnwindSym.asPath)
        val rst = genNormalBody(b, S(doUnwindLazy))
        
        if doUnwindLazy.isEmpty && opt.stackSafety.isEmpty then rst
        else
          blockBuilder
          .define(doUnwindDef)
          .rest(rst)
    if opt.debug then
      Define(getLocalsFn, ret)
    else
      ret
  
  // moves definitions to the top level of the block
  private def thirdPass(b: Block): Block =
    // to ensure the fun and class references in the continuation class are properly scoped,
    // we move all function defns to the top level of the handler block
    val (blk, defns) = b.floatOutDefns()
    defns.foldLeft(blk)((acc, defn) => Define(defn, acc))
  
  private def locToStr(l: Loc): Str =
    Scope.replaceInvalidCharacters(l.origin.fileName.last + "_L" + l.origin.startLineNum + "_" + l.spanStart + "_" + l.spanEnd)
  
  private def symToStr(s: Symbol): Str =
      s"${Scope.replaceInvalidCharacters(s.nme)}"
  
  private def translateFun(f: FunDefn)(using HandlerCtx): FunDefn =
    val callSelf = f.params match
      case pList :: Nil => 
        val params = pList.params.map(p => p.sym.asPath.asArg)
        f.owner match
        case None => S(Call(f.sym.asPath, params)(true, true))
        case Some(owner) => 
          S(Call(Select(owner.asPath, Tree.Ident(f.sym.nme))(N), params)(true, true))
      case _ => None // TODO: more than one plist
    
    FunDefn(f.owner, f.sym, f.params, translateBlock(f.body,
      f.params.flatMap(_.paramSyms).toSet,
      callSelf,
      L(f.sym),
      functionHandlerCtx(s"Cont$$func$$${symToStr(f.sym)}$$", f.sym.nme))
    )
  
  private def translateBody(cls: ClsLikeBody, sym: BlockMemberSymbol)(using HandlerCtx): ClsLikeBody =
    val curCtorCtx =
      if handlerCtx.isTopLevel
      then 
        topLevelCtx(s"Cont$$modCtor$$${symToStr(sym)}$$", s"‹constructor of ${sym.nme}›")
      else ctorCtx(
        cls.isym.asPath,
        s"Cont$$ctor$$${symToStr(sym)}$$", s"‹constructor of ${sym.nme}›")
    ClsLikeBody(
      cls.isym,
      cls.methods.map(translateFun),
      cls.privateFields,
      cls.publicFields,
      translateBlock(cls.ctor, Set.empty, N, R(cls.isym), curCtorCtx),
    )
  
  private def translateCls(cls: ClsLikeDefn)(using HandlerCtx): ClsLikeDefn =
    val curCtorCtx = ctorCtx(
      cls.isym.asPath,
      s"Cont$$ctor$$${symToStr(cls.sym)}$$", s"‹constructor of ${cls.sym.nme}›")
    cls.copy(methods = cls.methods.map(translateFun),
      ctor = translateBlock(cls.ctor, Set.empty, N, R(cls.isym), curCtorCtx),
      companion = cls.companion.map(translateBody(_, cls.sym))) // TODO: callSelf
  
  // Handle block is rewritten into:
  // 1. Instantiation of the handler
  // 2. An effectful call to enterHandleBlock
  private def translateHandleBlockShallow(h: HandleBlock): Block =
    val sym = new BlockMemberSymbol("handleBlock$", Nil, false)

    val bodyDefn = FunDefn(N, sym, PlainParamList(Nil) :: Nil, h.body)
    
    val handlerMtds = h.handlers.map: handler =>
      val sym = BlockMemberSymbol(h.cls.nme + handler.sym.nme, Nil, true)
      val fDef = FunDefn(
        N, sym, PlainParamList(Param(FldFlags.empty, handler.resumeSym, N, Modulefulness.none) :: Nil) :: Nil,
        handler.body
        )
      FunDefn(
        S(h.cls),
        handler.sym, handler.params,
        Define(
          fDef,
          Return(PureCall(paths.mkEffectPath, h.cls.asPath :: Value.Ref(sym, N) :: Nil), false)))

    // Some limited handling of effects extending classes and having access to their fields.
    // Currently does not support super() raising effects.
    val tmp = freshTmp()
    val ctor = blockBuilder
      .assign(tmp, Call(Value.Ref(State.builtinOpsMap("super")), h.args.map(_.asArg))(true, true))
      .ret(h.cls.asPath)
    
    val clsDefn = ClsLikeDefn(
      N, // no owner
      h.cls,
      BlockMemberSymbol(h.cls.id.name, Nil),
      syntax.Cls,
      N, Nil,
      S(h.par), handlerMtds, Nil, Nil,
      End(),
      Assign(freshTmp(), Call(Value.Ref(State.builtinOpsMap("super")), h.args.map(_.asArg))(true, true), End()),
      N,
      N,
    )

    blockBuilder
      .define(clsDefn)
      .assign(h.lhs, Instantiate(mut = true, Value.Ref(clsDefn.sym, S(h.cls)), Nil))
      .define(bodyDefn)
      .assign(h.res, Call(paths.enterHandleBlockPath, List(h.lhs.asPath.asArg, Value.Ref(sym, N).asArg))(true, true))
      .rest(h.rest)
  
  def translateHandleBlocks(b: Block): Block =

    val transform = new BlockTransformer(SymbolSubst()):
      override def applyBlock(b: Block) = b match
        case HandleBlock(lhs, res, par, args, cls, hdr, bod, rst) =>
          val hdr2 = hdr.map(applyHandler)
          val bod2 = applyBlock(bod)
          val rst2 = applyBlock(rst)
          translateHandleBlockShallow(HandleBlock(lhs, res, par, args, cls, hdr2, bod2, rst2))
        case _ => super.applyBlock(b)
    transform.applyBlock(b)

  
  private def genContClass(b: Block, callSelf: Opt[Result])(using h: HandlerCtx): Opt[ClsLikeDefn] =
    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(handlerCtx.contName)
    )
    
    val pcVar = VarSymbol(pcIdent)
    
    val loopLbl = freshTmp("contLoop")
    val pcSymbol = TermSymbol(ParamBind, S(clsSym), pcIdent)

    // This maps each state id to an optional location
    // Note that the value is an Option, and None must be inserted even if the location is not known
    // so that we can use the same map to enumerate all possible state id and check if there is any state id
    val pcToLoc = collection.mutable.Map.empty[StateId, Option[Loc]]
    var containsCall = false
    
    // Create the DoUnwind function
    doUnwindMap += R(clsSym) -> Select(clsSym.asPath, Tree.Ident("doUnwind"))(
      N /* this refers to the method defined in Runtime.FunctionContFrame */
    )
    val newPcSym = VarSymbol(Tree.Ident("newPc"))
    val resSym = VarSymbol(Tree.Ident("res"))
    val doUnwindBlk = blockBuilder
      .assign(pcSymbol, newPcSym.asPath)
      .assignFieldN(resSym.asPath.contTrace.last, nextIdent, clsSym.asPath)
      .assignFieldN(resSym.asPath.contTrace, lastIdent, clsSym.asPath)
      .ret(resSym.asPath)
    
    // Replaces ResultPlaceholders to check for effects and link the effect trace
    def prepareBlock(b: Block): Block =
      val transform = new BlockTransformerShallow(SymbolSubst()):
        override def applyResult(r: Result)(k: Result => Block): Block = 
          r match
            case c @ Call(Value.Ref(s: BuiltinSymbol, _), _) => ()
            case c: Call if !c.mayRaiseEffects => ()
            case _: Call | _: Instantiate => containsCall = true
            case _ => ()
          super.applyResult(r)(k)
          
        override def applyBlock(b: Block): Block = b match
          case Define(_: (ClsLikeDefn | FunDefn), rst) => applyBlock(rst)
          case ResultPlaceholder(res, uid, c, rest) =>
            pcToLoc(uid) = c.toLoc
            containsCall = true
            blockBuilder
              .assign(res, c)
              .ifthen(
                res.asPath,
                Case.Cls(paths.effectSigSym, paths.effectSigPath),
                ReturnCont(res, uid)
              )
              .chain(ResumptionPoint(res, uid, _))
              .rest(applyBlock(rest))
          case _ => super.applyBlock(b)
      transform.applyBlock(b)
    val actualBlock = handlerCtx.ctorThis match
      case N => prepareBlock(b)
      case S(thisPath) => Begin(prepareBlock(b), Return(thisPath, false))
    // If there is no state id found during prepareBlock, the block is trivial.
    val trivial = pcToLoc.isEmpty
    
    // there are three types of functions:
    // (1) functions that have no calls, indicated by `containsCall`
    // (2) functions that have only tail calls, indicated by `trivial`
    // (3) all other functions
    //
    // Here, (2) and (3) need a continuation class when stack safety is enabled, otherwise only (3) needs it
    // If (2) and stack safety is enabled, we can just create a continuation class with one state
    
    if trivial && opt.stackSafety.isEmpty then return N // case (1) or (2) if no stack safety
    if !containsCall then return N // case (1)

    val depthSym = freshTmp("curDepth")
    val resumedVal = VarSymbol(Tree.Ident("value$"))
    
    def createResumeBod =
      val parts = 
        if opt.stackSafety.isDefined then callSelf match
          case None => partitionBlock(actualBlock, true)
          case Some(value) => 
            val someParts = partitionBlock(actualBlock, false)
            BlockPartition(0, Return(value, false), N) :: someParts
        else
          partitionBlock(actualBlock, false)
        
      def transformPart(blk: Block): Block = 
        val transform = new BlockTransformerShallow(SymbolSubst()):
          override def applyBlock(b: Block): Block = b match
            case ReturnCont(res, uid) => Return(Call(
                Select(clsSym.asPath, Tree.Ident("doUnwind"))(
                  N /* this refers to the method defined in Runtime.FunctionContFrame */
                ),
                res.asPath.asArg :: Value.Lit(Tree.IntLit(uid)).asArg :: Nil)(true, false),
                false
              )
            case StateTransition(uid) =>
              blockBuilder
                .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
                .continue(loopLbl)
            case FnEnd() =>
              blockBuilder.break(loopLbl)
            case _ => super.applyBlock(b)
        transform.applyBlock(blk)

      // match block representing the function body
      val mainMatchCases = parts.toList.map(b => (Case.Lit(Tree.IntLit(b.id)), transformPart(b.blk)))
      val mainMatchBlk = Match(
        pcSymbol.asPath,
        mainMatchCases,
        N,
        End() 
      )
      
      val tmp = freshTmp()
      val withResetDepth =
        if opt.stackSafety.isDefined && !trivial then
          AssignField(runtimePath, stackDepthIdent, depthSym.asPath, mainMatchBlk)(N)
        else mainMatchBlk

      val lbl = blockBuilder.label(loopLbl, loop = true, withResetDepth).rest(End())

      def createAssignment(sym: Local) = Assign(sym, resumedVal.asPath, End())
      
      val assignedResumedCases = for 
        b   <- parts
        sym <- b.sym
      yield Case.Lit(Tree.IntLit(b.id)) -> createAssignment(sym) // NOTE: assume sym is in localsMap

      // assigns the resumed value
      val body =
        if assignedResumedCases.isEmpty then
          lbl
        else
          Match(
            pcSymbol.asPath,
            assignedResumedCases,
            N,
            lbl
          )

      // assign cur depth
      if opt.stackSafety.isDefined && !trivial then 
        Assign(depthSym, stackDepthPath, body)
      else
        body
        
    val resumeBody = 
      if trivial then callSelf match
        case None => actualBlock
        case Some(value) => Return(value, false)
      else createResumeBod
      
    
    val resumeSym = BlockMemberSymbol("resume", List())
    val resumeFnDef = FunDefn(
      S(clsSym), // owner
      resumeSym,
      List(PlainParamList(List(Param(FldFlags.empty, resumedVal, N, Modulefulness.none)))),
      resumeBody
    )

    val debugMtds = if !opt.debug then Nil else
    
      val getLocalsSym = BlockMemberSymbol("getLocals", List())
      
      val localsRes = h.debugInfo.prevLocalsFn match
        case Some(value) => PureCall(value, Nil)
        case None => Tuple(mut = true, Nil)
      
      val getLocalsFnDef = FunDefn(
        S(clsSym),
        getLocalsSym,
        List(),
        Return(localsRes, false)
      )

      val getLocSym = BlockMemberSymbol("getLoc", List())
      val getLocFnDef = FunDefn(
        S(clsSym),
        getLocSym,
        List(),
        Match(pcSymbol.asPath, pcToLoc.toSortedMap.iterator.map: (stateId, loc) =>
          Case.Lit(Tree.IntLit(stateId)) -> Return(Value.Lit(loc.fold(Tree.UnitLit(true)): loc =>
            val (line, _, col) = loc.origin.fph.getLineColAt(loc.spanStart)
            Tree.StrLit(s"${loc.origin.fileName.last}:${line + loc.origin.startLineNum - 1}:$col")
          ), false)
        .toList, N, End()),
      )

      getLocalsFnDef :: getLocFnDef :: Nil
    
    val mtds = resumeFnDef :: debugMtds
    
    S(ClsLikeDefn(
      N, // no owner
      clsSym,
      BlockMemberSymbol(clsSym.nme, Nil),
      syntax.Cls,
      N,
      PlainParamList({
        val p = Param(FldFlags.empty.copy(isVal = true), pcVar, N, Modulefulness.none)
        pcVar.decl = S(p)
        p
      } :: Nil) :: Nil,
      S(paths.contClsPath),
      mtds,
      Nil,
      Nil,
      Assign(freshTmp(), PureCall(
        Value.Ref(State.builtinOpsMap("super")), // refers to runtime.FunctionContFrame which is pure
        Value.Lit(Tree.UnitLit(true)) :: Nil), End()),
      AssignField(
        clsSym.asPath,
        pcVar.id,
        Value.Ref(pcVar),
        End()
      )(S(pcSymbol)),
      N,
      N, // TODO: bufferable?
    ))
  
  // Rewriites ResultPlaceholder. Checks if the result in the placeholder is an effect.
  private def genNormalBody(b: Block, doUnwind: Opt[Lazy[Path]])(using HandlerCtx): Block =
    val transform = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case ResultPlaceholder(res, uid, c, rest) => 
          val doUnwindBlk = doUnwind match
            case None => Assign(res, topLevelCall(LinkState(res, paths.contClsPath, Value.Lit(Tree.IntLit(uid)))), End())
            case Some(doUnwind) => Return(PureCall(doUnwind.get_!, res.asPath :: Value.Lit(Tree.IntLit(uid)) :: Nil), false)
          blockBuilder
            .assign(res, c)
            .ifthen(
              res.asPath,
              Case.Cls(paths.effectSigSym, paths.effectSigPath),
              doUnwindBlk
            )
            .rest(applyBlock(rest))
        case _ => super.applyBlock(b)
    
    transform.applyBlock(b)
    
  

  def translateTopLevel(b: Block): (Block, Map[FnOrCls, Path]) =
    doUnwindMap = Map.empty
    val transformed = translateBlock(b, topLevelCtx(s"Cont$$topLevel$$BAD", "‹top level›"))
    (transformed, doUnwindMap)
    
