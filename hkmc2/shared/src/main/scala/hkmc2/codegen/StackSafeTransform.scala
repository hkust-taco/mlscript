package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree
import hkmc2.codegen.HandlerLowering.FnOrCls

class StackSafeTransform(depthLimit: Int, paths: HandlerPaths, stackSafetyMap: StackSafetyMap)(using State, Config):
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("stackDepth")

  private val runtimePath: Path = State.runtimeSymbol.asPath
  private val checkDepthPath: Path = runtimePath.selN(Tree.Ident("checkDepth"))
  private val runStackSafePath: Path = runtimePath.selN(Tree.Ident("runStackSafe"))
  private val stackDepthPath: Path = runtimePath.selN(STACK_DEPTH_IDENT)

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, a.asArg :: b.asArg :: Nil)(true, false, false)

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, isTailCall: Bool, f: Result => Block, sym: Symbol, curDepth: => Symbol): Block =
    if isTailCall then Return(res, false)
    else
      blockBuilder
        .assign(sym, res)
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, curDepth.asPath)
        .rest(f(sym.asPath))
  
  def wrapStackSafe(body: Block, resSym: Local, rest: Block) =
    val bodSym = BlockMemberSymbol("‹stack safe body›", Nil, false)
    val bodFun = FunDefn.withFreshSymbol(N, bodSym, ParamList(ParamListFlags.empty, Nil, N) :: Nil, body)(forceTailRec = false, configOverride = N, visibility = Visibility.Public)
    Scoped(Set.single(bodSym),
      Define(bodFun, Assign(resSym, Call(runStackSafePath, intLit(depthLimit).asArg :: bodSym.asPath.asArg :: Nil)(true, true, false), rest))
    )

  def extractResTopLevel(res: Result, isTailCall: Bool, f: Result => Block, sym: Symbol, curDepth: => Symbol) =
    val resSym = sym
    wrapStackSafe(Ret(res), resSym, f(resSym.asPath))

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block, curDepth: => Symbol, isTopLevel: Bool = false): Block =
    def usesStack(r: Result) = r match
      case Call(Value.Ref(_: BuiltinSymbol, _), _) => false
      case c: Call if !c.mayRaiseEffects => false // a call can only trigger a stack delay if it can raise effects
      case _: Call | _: Instantiate => true
      case _ => false

    val extract = if isTopLevel then extractResTopLevel else extractRes
    
    val transform = new BlockTransformer(SymbolSubst.Id):

      override def applyFunDefn(fun: FunDefn): FunDefn = rewriteFn(fun)
      
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case defn: ClsLikeDefn => k(rewriteCls(defn, isTopLevel))
        case _: FunDefn | _: ValDefn => super.applyDefn(defn)(k)

      override def applyBlock(b: Block): Block = b match
        case Return(res, implct) if usesStack(res) =>
          val tmp = TempSymbol(N, "res")
          super.applyResult(res): res =>
            Scoped(Set.single(tmp), extract(res, true, Return(_, implct), tmp, curDepth))
        // Optimization to avoid generation of unnecessary variables
        case Assign(lhs, r, rest) =>
          if usesStack(r) then
            super.applyResult(r): r =>
              extract(r, false, _ => applyBlock(rest), lhs, curDepth)
          else
            super.applyBlock(b)
        
        case HandleBlock(l, res, par, args, cls, hdr, bod, rst) => lastWords("HandleBlock in stack safe transformation")
        
        case _ => super.applyBlock(b)
        
      override def applyHandler(hdr: Handler): Handler = lastWords("HandleBlock in stack safe transformation")
      
      override def applyResult(r: Result)(k: Result => Block): Block =
        if usesStack(r) then
          val tmp = TempSymbol(N, "res")
          Scoped(Set.single(tmp), extract(r, false, k, tmp, curDepth))
        else
          super.applyResult(r)(k)
      
      override def applyLam(lam: Lambda): Lambda = lastWords("Lambda in stack safe transformation")
  
    transform.applyBlock(b)
  
  def isTrivial(b: Block): Boolean =
    var trivial = true
    new BlockTraverserShallow:
      applyBlock(b)
      override def applyResult(r: Result): Unit = r match
        case Call(Value.Ref(_: BuiltinSymbol, _), _) => ()
        case _: Call | _: Instantiate => trivial = false
        case _ => ()
    trivial
  
  def rewriteCls(defn: ClsLikeDefn, isTopLevel: Bool): ClsLikeDefn = defn.parentPath match
    case Some(value) if value eq paths.contClsPath => defn
    case _ =>
      val ClsLikeDefn(owner, isym, sym, ctorSym, k, paramsOpt, auxParams,
        parentPath, methods, privateFields, publicFields, preCtor, ctor, mod, bufferable) = defn
      ClsLikeDefn(
        owner, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath,
        methods.map(rewriteFn),
        privateFields,
        publicFields, 
        preCtor,
        ctor,
        mod.map(rewriteObjBody(_, isTopLevel)),
        bufferable,
      )(defn.configOverride)
  
  def rewriteObjBody(defn: ClsLikeBody, isTopLevel: Bool): ClsLikeBody =
    ClsLikeBody(
      defn.isym,
      defn.methods.map(rewriteFn),
      defn.privateFields,
      defn.publicFields,
      if isTopLevel then
        if config.effectHandlers.exists(_.doNotInstrumentTopLevelModCtor) then defn.ctor else transformTopLevel(defn.ctor)
      else rewriteBlk(defn.ctor, R(defn.isym)),
    )

  // fnOrCls points us to the doUnwind function
  def rewriteBlk(blk: Block, fnOrCls: FnOrCls) =
    (stackSafetyMap.get(fnOrCls), isTrivial(blk)) match
    case (S((increment, doUnwindBlk)), false) =>
      var usedDepth = false
      lazy val curDepth =
        usedDepth = true
        TempSymbol(None, "curDepth")
      val newBody = transform(blk, curDepth)
      val resSym = TempSymbol(None, "stackDelayRes")
      val addStackSafeEffect = blk => blockBuilder
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(increment)))
        .staticif(usedDepth, _.assignScoped(curDepth, stackDepthPath))
        .assignScoped(resSym, Call(checkDepthPath, Nil)(true, true, false))
        .ifthen(
          paths.curEffect,
          Case.Lit(Tree.UnitLit(true)),
          End(),
          S(doUnwindBlk)
        )
        .rest(blk)
      addStackSafeEffect(newBody)
    case _ => blk



  def rewriteFn(defn: FunDefn) = 
    FunDefn(defn.owner, defn.sym, defn.dSym, defn.params, rewriteBlk(defn.body, L(defn.sym)))(defn.forceTailRec, defn.configOverride, defn.visibility)

  def transformTopLevel(b: Block) = transform(b, TempSymbol(N), true)
