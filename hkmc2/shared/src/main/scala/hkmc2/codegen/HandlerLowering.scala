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
  
  private case class LinkState(res: Local, cls: Path, uid: StateId)
  
  // isTopLevel:
  // whether the current block is the top level block, as we do not emit code for continuation class on the top level
  // since we cannot return an effect signature on the top level (we are not in a function so return statement are invalid)
  // contName: the name of the continuation class
  // ctorThis: the path to `this` in the constructor, this is used to insert `return this;` at the end of constructor.
  // linkAndHandle:
  // a function that takes a LinkState and returns a block that links the continuation class and handles the effect
  // this is a convenience function which initializes the continuation class in function context or throw an error in top level
  private case class HandlerCtx(
      isTopLevel: Bool,
      isHandlerBody: Bool,
      contName: Str,
      ctorThis: Option[Path],
      debugInfo: DebugInfo,
      linkAndHandle: LinkState => Block,
  ):
    def nestDebugScope(locals: Set[Local], localsFn: Path) = copy(debugInfo = debugInfo.copy(inScopeLocals =
      debugInfo.inScopeLocals ++ locals, prevLocalsFn = S(localsFn)))
  
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
  
  def isHandlerClsPath(p: Path) =
    (p eq contClsPath)  || (p eq stackDelayClsPath) || (p eq effectSigPath)

class HandlerLowering(paths: HandlerPaths, opt: EffectHandlers)(using TL, Raise, Elaborator.State, Elaborator.Ctx):

  private def funcLikeHandlerCtx(ctorThis: Option[Path], isHandlerMtd: Bool, contNme: Str, debugNme: Str)(using h: HandlerCtx) =
    HandlerCtx(false, false, contNme, ctorThis, h.debugInfo.copy(debugNme), state =>
      blockBuilder
        .assignFieldN(state.res.asPath.contTrace.last, nextIdent, Instantiate(
          state.cls.selN(Tree.Ident("class")),
          Value.Lit(Tree.IntLit(state.uid)) :: Nil))
        .assignFieldN(state.res.asPath.contTrace, lastIdent, state.res.asPath.contTrace.last.next)
        .ret(state.res.asPath))
  private def functionHandlerCtx(nme: Str, debugNme: Str)(using HandlerCtx) = funcLikeHandlerCtx(N, false, nme, debugNme)
  private def topLevelCtx(nme: Str, debugNme: Str) = HandlerCtx(true, false, nme, N, DebugInfo.topLevel(debugNme), state => Assign(
      state.res,
      Call(paths.topLevelEffectPath, state.res.asPath.asArg :: Value.Lit(Tree.BoolLit(opt.debug)).asArg :: Nil)(true, false),
      End()))
  private def ctorCtx(ctorThis: Path, nme: Str, debugNme: Str)(using HandlerCtx) = funcLikeHandlerCtx(S(ctorThis), false, nme, debugNme)
  private def handlerMtdCtx(nme: Str, debugNme: Str)(using HandlerCtx) = funcLikeHandlerCtx(N, true, nme, debugNme)
  private def handlerCtx(using HandlerCtx): HandlerCtx = summon
  
  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(N, dbgNme)
  
  private def rtThrowMsg(msg: Str) = Throw(
    Instantiate(State.globalThisSymbol.asPath.selN(Tree.Ident("Error")),
    Value.Lit(Tree.StrLit(msg)) :: Nil)
  )
  
  object PureCall:
    def apply(fun: Path, args: List[Path]) = Call(fun, args.map(Arg(false, _)))(true, false)
    def unapply(res: Result) = res match
      case Call(fun, args) => args.foldRight[Opt[List[Path]]](S(Nil)): (arg, acc) =>
          acc.flatMap: acc =>
            arg match
              case Arg(false, p) => S(p :: acc)
              case _ => N
        .map((fun, _))
      case _ => N
  
  object ResumptionPoint:
    private val resumptionSymbol = freshTmp("resumptionPoint")
    def apply(res: Local, uid: StateId, rest: Block) =
      Assign(res, PureCall(Value.Ref(resumptionSymbol), List(Value.Lit(Tree.IntLit(uid)))), rest)
    def unapply(blk: Block) = blk match
      case Assign(res, PureCall(Value.Ref(`resumptionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), rest) =>
        Some(res, uid, rest)
      case _ => None
  
  object ReturnCont:
    private val returnContSymbol = freshTmp("returnCont")
    def apply(res: Local, uid: StateId) =
      Assign(res, PureCall(Value.Ref(returnContSymbol), List(Value.Lit(Tree.IntLit(uid)))), End(""))
    def unapply(blk: Block) = blk match
      case Assign(res, PureCall(Value.Ref(`returnContSymbol`), List(Value.Lit(Tree.IntLit(uid)))), _) =>
        Some(res, uid)
      case _ => None
  
  // placeholder for effectful Results, such as Call, Instantiate and anything else that could
  // return a continuation
  object ResultPlaceholder:
    private val callSymbol = freshTmp("resultPlaceholder")
    def apply(res: Local, uid: StateId, r: Result, rest: Block) =
      Assign(
        res,
        PureCall(Value.Ref(callSymbol), List(Value.Lit(Tree.IntLit(uid)))),
        Assign(res, r, rest))
    def unapply(blk: Block) = blk match
      case Assign(
          res,
          PureCall(Value.Ref(`callSymbol`), List(Value.Lit(Tree.IntLit(uid)))),
          Assign(_, c, rest)) =>
        Some(res, uid, c, rest)
      case _ => None
  
  object StateTransition:
    private val transitionSymbol = freshTmp("transition")
    def apply(uid: StateId) =
      Return(PureCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) =>
        S(uid)
      case _ => N
  
  object FnEnd:
    private val fnEndSymbol = freshTmp("fnEnd")
    def apply() = Return(PureCall(Value.Ref(fnEndSymbol), Nil), false)
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.Ref(`fnEndSymbol`), Nil), false) => true
      case _ => false
  
  private class FreshId:
    var id: Int = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
  private val freshId = FreshId()
  
  // id: the id of the current state
  // blk: the block of code within this state
  // sym: the variable to which the resumed value should set
  class BlockState(val id: StateId, val blk: Block, val sym: Opt[Local])
  
  // does not include the entry point
  def partitionBlock(blk: Block, labelIds: Map[Symbol, (StateId, StateId)] = Map.empty): Ls[BlockState] = 
    // for readability :)
    case class PartRet(head: Block, states: Ls[BlockState])

    // * returns (truncated input block, child block states)
    // * blk: The block to transform
    // * labelIds: maps label IDs to the state at the start of the label and the state after the label
    // * jumpTo: what state End should jump to, if at all 
    // * freshState: uid generator
    // TODO: don't split within Match, Begin and Labels when not needed, ideally keep it intact.
    // Need careful analysis for this.
    def go(blk: Block)(implicit labelIds: Map[Symbol, (StateId, StateId)], afterEnd: Option[StateId]): PartRet =
      blk match
      case ResumptionPoint(result, uid, rest) =>
        val PartRet(head, states) = go(rest)
        PartRet(StateTransition(uid), BlockState(uid, head, S(result)) :: states)

      case Match(scrut, arms, dflt, rest) => 
        val restParts = go(rest)
        val restId: StateId = restParts.head match
          case StateTransition(uid) => uid
          case _ => freshId()
        
        val armsParts = arms.map((cse, blkk) => (cse, go(blkk)(afterEnd = S(restId))))
        val dfltParts = dflt.map(blkk => go(blkk)(afterEnd = S(restId)))

        val states_ = restParts.states ::: armsParts.flatMap(_._2.states)
        val states = dfltParts match
          case N => states_
          case S(value) => value.states ::: states_

        val newArms = armsParts.map((cse, partRet) => (cse, partRet.head))
        
        restParts.head match
          case StateTransition(_) =>
            PartRet(
              Match(scrut, newArms, dfltParts.map(_.head), StateTransition(restId)),
              states
            )
          case _ =>
            PartRet(
              Match(scrut, newArms, dfltParts.map(_.head), StateTransition(restId)),
              BlockState(restId, restParts.head, N) :: states
            )
      case l @ Label(label, body, rest) =>
        val startId = freshId() // start of body

        val PartRet(restNew, restParts) = go(rest)

        val endId: StateId = restNew match // start of rest
          case StateTransition(uid) => uid 
          case _ => freshId()

        val PartRet(bodyNew, parts) = go(body)(using labelIds + (label -> (startId, endId)), S(endId))
        
        restNew match
          case StateTransition(_) =>
            PartRet(
              StateTransition(startId), 
              BlockState(startId, bodyNew, N) :: parts ::: restParts
            )
          case _ =>
            PartRet(
              StateTransition(startId), 
              BlockState(startId, bodyNew, N) :: BlockState(endId, restNew, N) :: parts ::: restParts
            )

      case Break(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return PartRet(blk, Nil)
          case S(value) => value
        PartRet(StateTransition(end), Nil)
      case Continue(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return PartRet(blk, Nil)
          case S(value) => value
        PartRet(StateTransition(start), Nil)

      case Begin(sub, rest) => 
        val PartRet(restNew, restParts) = go(rest)
        restNew match
          case StateTransition(uid) => 
            val PartRet(subNew, subParts) = go(sub)(afterEnd = S(uid))
            PartRet(subNew, subParts ::: restParts)
          case _ =>
            val restId = freshId()
            val PartRet(subNew, subParts) = go(sub)(afterEnd = S(restId))
            PartRet(subNew, BlockState(restId, restNew, N) :: subParts ::: restParts)

      case Define(defn, rest) => 
        val PartRet(head, parts) = go(rest)
        PartRet(Define(defn, head), parts)
      // implicit returns is used inside constructors when call occur in tail position,
      // which may transition to `return this;` (inserted in second pass) after the implicit return
      case End(_) | Return(_, true) => afterEnd match
        case None => PartRet(FnEnd(), Nil)
        case Some(value) => PartRet(StateTransition(value), Nil)
      // identity cases
      case Assign(lhs, rhs, rest) =>
        val PartRet(head, parts) = go(rest)
        PartRet(Assign(lhs, rhs, head), parts)
      case blk @ AssignField(lhs, nme, rhs, rest) =>
        val PartRet(head, parts) = go(rest)
        PartRet(AssignField(lhs, nme, rhs, head)(blk.symbol), parts)
      case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
        val PartRet(head, parts) = go(rest)
        PartRet(AssignDynField(lhs, fld, arrayIdx, rhs, head), parts)
      case Return(_, _) => PartRet(blk, Nil)
      // ignored cases
      case TryBlock(sub, finallyDo, rest) => ??? // ignore
      case Throw(_) => PartRet(blk, Nil)
      case _: HandleBlock => lastWords("unexpected handleBlock") // already translated at this point

    val result = go(blk)(using labelIds, N)
    result.states
  
  val runtimePath = State.runtimeSymbol.asPath
  val fnLocalsPath: Path = runtimePath.selSN("FnLocalsInfo").selSN("class")
  val localVarInfoPath: Path = runtimePath.selSN("LocalVarInfo").selSN("class")
  private def createGetLocalsFn(b: Block, extraLocals: Set[Local])(using h: HandlerCtx) =
    val locals = (b.userDefinedVars ++ extraLocals) -- h.debugInfo.inScopeLocals
    val localsInfo = locals.toList.sortBy(_.uid).map: s =>
      FlowSymbol(s.nme) -> Instantiate(localVarInfoPath,
        Value.Lit(Tree.StrLit(s.nme)) :: s.asPath :: Nil
      )
    val startSym = FlowSymbol("prev")
    val thisInfo = FlowSymbol("thisInfo")
    
    val body = blockBuilder
      .assign(startSym, h.debugInfo.prevLocalsFn match
          case None => Value.Arr(Nil)
          case Some(value) => PureCall(value, Nil)
        )
      .foldLeft(localsInfo):
        case (acc, (sym, res)) => acc.assign(sym, res)
      .assign(thisInfo, Instantiate(fnLocalsPath,
          Value.Lit(Tree.StrLit(h.debugInfo.debugNme))
            :: Value.Arr(localsInfo.map(v => v._1.asPath.asArg))
            :: Nil
        ))
      .assign(TempSymbol(N, ""), Call(startSym.asPath.selSN("push"), thisInfo.asPath.asArg :: Nil)(false, false))
      .ret(startSym.asPath)

    FunDefn(N, BlockMemberSymbol("getLocals", Nil), PlainParamList(Nil) :: Nil, body)
    
  /**
   * The actual translation:
   * 1. add call markers, transform class, function, lambda and sub handler blocks
   * 2.
   *   a) generate continuation class
   *   b) generate normal function body
   * 3. float out definitions
   */
  
  private def translateBlock(b: Block, extraLocals: Set[Local], h: HandlerCtx): Block =
    val getLocalsFn = createGetLocalsFn(b, extraLocals)(using h)
    given HandlerCtx = h.nestDebugScope(b.userDefinedVars ++ extraLocals, getLocalsFn.sym.asPath)
    
    val stage1 = firstPass(b)
    val stage2 = secondPass(stage1, getLocalsFn)
    if h.isTopLevel then stage2 else thirdPass(stage2)
  
  private def firstPass(b: Block)(using HandlerCtx): Block =
    val getLocalsSym = ctx.builtins.debug.getLocals
    val transformer = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block) = b match
        case b: HandleBlock =>
          val rest = applyBlock(b.rest)
          translateHandleBlock(b.copy(rest = rest))
        // This block optimizes tail-calls in the handler transformation. We do not optimize implicit returns.
        // Implicit returns are used in top level and constructor:
        // For top level, this correspond to the last statement which should also be checked for effect.
        // For constructor, we will append `return this;` after the implicit return so it is not a tail call.
        case Return(c @ Call(fun, args), false) if !handlerCtx.isHandlerBody =>
          val fun2 = applyPath(fun)
          val args2 = args.mapConserve(applyArg)
          val c2 = if (fun2 is fun) && (args2 is args) then c else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects)
          if c2 is c then b else Return(c2, false)
        // Optimization to avoid generation of unnecessary variables
        case Assign(lhs, c @ Call(fun, args), rest) if c.mayRaiseEffects =>
          val fun2 = applyPath(fun)
          val args2 = args.mapConserve(applyArg)
          val c2 = if (fun2 is fun) && (args2 is args) then c else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects)
          ResultPlaceholder(lhs, freshId(), c2, applyBlock(rest))
        case Assign(lhs, c @ Instantiate(cls, args), rest) =>
          val cls2 = applyPath(cls)
          val args2 = args.mapConserve(applyPath)
          val c2 = if (cls2 is cls) && (args2 is args) then c else Instantiate(cls2, args2)
          ResultPlaceholder(lhs, freshId(), c2, applyBlock(rest))
        case _ => super.applyBlock(b)
      override def applyResult2(r: Result)(k: Result => Block): Block = r match
        case c @ Call(fun, args) if c.mayRaiseEffects =>
          val res = freshTmp("res")
          val fun2 = applyPath(fun)
          val args2 = args.mapConserve(applyArg)
          val c2 = if (fun2 is fun) && (args2 is args) then c else Call(fun2, args2)(c.isMlsFun, c.mayRaiseEffects)
          ResultPlaceholder(res, freshId(), c2, k(Value.Ref(res)))
        case c @ Instantiate(cls, args) =>
          val res = freshTmp("res")
          val cls2 = applyPath(cls)
          val args2 = args.mapConserve(applyPath)
          val c2 = if (cls2 is cls) && (args2 is args) then c else Instantiate(cls2, args2)
          ResultPlaceholder(res, freshId(), c2, k(Value.Ref(res)))
        case r => super.applyResult2(r)(k)
      override def applyPath(p: Path): Path = p match
        case Value.Ref(`getLocalsSym`) => handlerCtx.debugInfo.prevLocalsFn.get
        case _ => super.applyPath(p)
      override def applyLam(lam: Value.Lam): Value.Lam =
        // This should normally be unreachable due to prior desugaring of lambda
        raise(InternalError(msg"Unexpected lambda during handler lowering" -> lam.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        Value.Lam(lam.params, translateBlock(lam.body, lam.params.paramSyms.toSet, functionHandlerCtx(s"Cont$$lambda$$", "‹lambda›")))
      override def applyDefn(defn: Defn): Defn = defn match
        case f: FunDefn => translateFun(f)
        case c: ClsLikeDefn => translateCls(c)
        case _: ValDefn => super.applyDefn(defn)
    transformer.applyBlock(b)
  
  private def secondPass(b: Block, getLocalsFn: FunDefn)(using HandlerCtx): Block =
    val cls = if handlerCtx.isTopLevel then N else genContClass(b)
    val ret = cls match
      case None => genNormalBody(b, BlockMemberSymbol("", Nil))
      case Some(cls) => Define(cls, genNormalBody(b, cls.sym))
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
    FunDefn(f.owner, f.sym, f.params, translateBlock(f.body,
      f.params.flatMap(_.paramSyms).toSet,
      functionHandlerCtx(s"Cont$$func$$${symToStr(f.sym)}$$", f.sym.nme))
    )
  
  private def translateCls(cls: ClsLikeDefn)(using HandlerCtx): ClsLikeDefn =
    val curCtorCtx = if handlerCtx.isTopLevel && (cls.k is syntax.Mod)
      then topLevelCtx(s"Cont$$modCtor$$${symToStr(cls.sym)}$$", s"‹constructor of ${cls.sym.nme}›")
      else ctorCtx(
        cls.isym.asPath,
        s"Cont$$ctor$$${symToStr(cls.sym)}$$", s"‹constructor of ${cls.sym.nme}›")
    cls.copy(methods = cls.methods.map(translateFun),
      ctor = translateBlock(cls.ctor, Set.empty, curCtorCtx))
  
  // Handle block becomes a FunDefn and CallPlaceholder
  private def translateHandleBlock(h: HandleBlock)(using HandlerCtx): Block =
    val sym = BlockMemberSymbol(s"handleBlock$$", Nil)
    val lbl = freshTmp("handlerBody")
    val lblLoop = freshTmp("handlerLoop")
    
    val handlerBody = translateBlock(h.body, Set.empty, HandlerCtx(false, true,
      s"Cont$$handleBlock$$${symToStr(h.lhs)}$$", N, handlerCtx.debugInfo.copy(debugNme = s"‹handler body of ${h.lhs.nme}›"), state => blockBuilder
        .assignFieldN(state.res.asPath.contTrace.last, nextIdent, PureCall(state.cls, Value.Lit(Tree.IntLit(state.uid)) :: Nil))
        .ret(PureCall(paths.handleBlockImplPath, state.res.asPath :: h.lhs.asPath :: Nil))))
    
    val handlerMtds = h.handlers.map: handler =>
      val lam = Value.Lam(
        PlainParamList(Param(FldFlags.empty, handler.resumeSym, N) :: Nil),
        translateBlock(handler.body,
          handler.params.flatMap(_.paramSyms).toSet,
          handlerMtdCtx(s"Cont$$handler$$${symToStr(h.lhs)}$$${symToStr(handler.sym)}$$", handler.sym.nme)))
      FunDefn(
        S(h.cls),
        handler.sym, handler.params, Return(PureCall(paths.mkEffectPath, h.cls.asPath :: lam :: Nil), false))
    
    val clsDefn = ClsLikeDefn(
      N, // no owner
      h.cls,
      BlockMemberSymbol(h.cls.id.name, Nil),
      syntax.Cls,
      N, Nil,
      S(h.par), handlerMtds, Nil, Nil,
      Assign(freshTmp(), Call(Value.Ref(State.builtinOpsMap("super")), h.args.map(_.asArg))(true, true), End()), End()) // TODO: handle effect in super call
    // NOTE: the super call is inside the preCtor
    // during resumption we need to resume both the this.x = x bindings done in JSBuilder and the ctor
    
    val body = blockBuilder
      .define(clsDefn)
      .assign(h.lhs, Instantiate(Value.Ref(clsDefn.sym), Nil))
      .rest(handlerBody)
    
    val defn = FunDefn(
      N, // no owner
      sym, PlainParamList(Nil) :: Nil, body)
    
    val result = Define(defn, ResultPlaceholder(h.res, freshId(), Call(sym.asPath, Nil)(true, true), h.rest))
    result
  
  private def genContClass(b: Block)(using h: HandlerCtx): Opt[ClsLikeDefn] =
    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(handlerCtx.contName)
    )
    
    val pcVar = VarSymbol(pcIdent)

    // This maps each state id to an optional location
    // Note that the value is an Option, and None must be inserted even if the location is not known
    // so that we can use the same map to enumerate all possible state id and check if there is any state id
    val pcToLoc = collection.mutable.Map.empty[StateId, Option[Loc]]
    
    def prepareBlock(b: Block): Block =
      val transform = new BlockTransformerShallow(SymbolSubst()):
        override def applyBlock(b: Block): Block = b match
          case Define(_: (ClsLikeDefn | FunDefn), rst) => applyBlock(rst)
          case ResultPlaceholder(res, uid, c, rest) =>
            pcToLoc(uid) = c.toLoc
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
    if pcToLoc.isEmpty then return N
    
    val parts = partitionBlock(actualBlock)
    val loopLbl = freshTmp("contLoop")
    val pcSymbol = TermSymbol(ParamBind, S(clsSym), pcIdent)
    
    def transformPart(blk: Block): Block = 
      val transform = new BlockTransformerShallow(SymbolSubst()):
        override def applyBlock(b: Block): Block = b match
          case ReturnCont(res, uid) =>
            blockBuilder
              .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
              .assignFieldN(res.asPath.contTrace.last, nextIdent, clsSym.asPath)
              .assignFieldN(res.asPath.contTrace, lastIdent, clsSym.asPath)
              .ret(res.asPath)
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

    val lbl = blockBuilder.label(loopLbl, mainMatchBlk).rest(End())
    
    val resumedVal = VarSymbol(Tree.Ident("value$"))

    def createAssignment(sym: Local) = Assign(sym, resumedVal.asPath, End())
    
    val assignedResumedCases = for 
      b   <- parts
      sym <- b.sym
    yield Case.Lit(Tree.IntLit(b.id)) -> createAssignment(sym) // NOTE: assume sym is in localsMap

    // assigns the resumed value
    val resumeBody = 
      if assignedResumedCases.isEmpty then
        lbl
      else
        Match(
          pcSymbol.asPath,
          assignedResumedCases,
          N,
          lbl
        )
    
    val resumeSym = BlockMemberSymbol("resume", List())
    val resumeFnDef = FunDefn(
      S(clsSym), // owner
      resumeSym,
      List(PlainParamList(List(Param(FldFlags.empty, resumedVal, N)))),
      resumeBody
    )

    val debugMtds = if !opt.debug then Nil else
    
      val getLocalsSym = BlockMemberSymbol("getLocals", List())
      
      val localsRes = h.debugInfo.prevLocalsFn match
        case Some(value) => PureCall(value, Nil)
        case None => Value.Arr(Nil)
      
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
    
    S(ClsLikeDefn(
      N, // no owner
      clsSym,
      BlockMemberSymbol(clsSym.nme, Nil),
      syntax.Cls,
      S(PlainParamList({
        val p = Param(FldFlags.empty.copy(value = true), pcVar, N)
        pcVar.decl = S(p)
        p
      } :: Nil)),
      Nil,
      S(paths.contClsPath),
      resumeFnDef :: debugMtds,
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
      )(S(pcSymbol))))
  
  private def genNormalBody(b: Block, clsSym: BlockMemberSymbol)(using HandlerCtx): Block =
    val transform = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case ResultPlaceholder(res, uid, c, rest) =>
          blockBuilder
            .assign(res, c)
            .ifthen(
              res.asPath,
              Case.Cls(paths.effectSigSym, paths.effectSigPath),
              handlerCtx.linkAndHandle(LinkState(res, clsSym.asPath, uid))
            )
            .rest(applyBlock(rest))
        case _ => super.applyBlock(b)
    
    transform.applyBlock(b)

  def translateTopLevel(b: Block): Block =
    translateBlock(b, Set.empty, topLevelCtx(s"Cont$$topLevel$$BAD", "‹top level›"))
    
