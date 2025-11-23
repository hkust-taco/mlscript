package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree
import hkmc2.codegen.HandlerLowering.FnOrCls

class StackSafeTransform(depthLimit: Int, paths: HandlerPaths, doUnwindMap: Map[FnOrCls, Path])(using State):
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("stackDepth")
  
  val doUnwindFns = doUnwindMap.values.collect:
      case s: Select if s.symbol.isDefined => s.symbol.get
      case Value.Ref(sym) => sym
    .toSet

  private val runtimePath: Path = State.runtimeSymbol.asPath
  private val checkDepthPath: Path = runtimePath.selN(Tree.Ident("checkDepth"))
  private val runStackSafePath: Path = runtimePath.selN(Tree.Ident("runStackSafe"))
  private val stackDepthPath: Path = runtimePath.selN(STACK_DEPTH_IDENT)

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, a.asArg :: b.asArg :: Nil)(true, false)

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, isTailCall: Bool, f: Result => Block, sym: Option[Symbol], curDepth: => Symbol): Block =
    if isTailCall then Return(res, false)
    else
      val tmp = sym getOrElse TempSymbol(None, "tmp")
      blockBuilder
        .assign(tmp, res)
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, curDepth.asPath)
        .rest(f(tmp.asPath))
  
  def wrapStackSafe(body: Block, resSym: Local, rest: Block) =
    val bodSym = BlockMemberSymbol("‹stack safe body›", Nil, false)
    val bodFun = FunDefn(N, bodSym, ParamList(ParamListFlags.empty, Nil, N) :: Nil, body)
    Define(bodFun, Assign(resSym, Call(runStackSafePath, intLit(depthLimit).asArg :: bodSym.asPath.asArg :: Nil)(true, true), rest))

  def extractResTopLevel(res: Result, isTailCall: Bool, f: Result => Block, sym: Option[Symbol], curDepth: => Symbol) =
    val resSym = sym getOrElse TempSymbol(None, "res")
    wrapStackSafe(Ret(res), resSym, f(resSym.asPath))

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block, curDepth: => Symbol, isTopLevel: Bool = false): Block =
    def usesStack(r: Result) = r match
      case Call(Value.Ref(_: BuiltinSymbol), _) => false
      case c: Call if !c.mayRaiseEffects => false // a call can only trigger a stack delay if it can raise effects
      case _: Call | _: Instantiate => true
      case _ => false

    val extract = if isTopLevel then extractResTopLevel else extractRes
    
    val transform = new BlockTransformer(SymbolSubst()):

      override def applyFunDefn(fun: FunDefn): FunDefn = rewriteFn(fun)
      
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case defn: ClsLikeDefn => k(rewriteCls(defn, isTopLevel))
        case _: FunDefn | _: ValDefn => super.applyDefn(defn)(k)

      override def applyBlock(b: Block): Block = b match
        case Return(res, implct) if usesStack(res) =>
          super.applyResult(res): res =>
            extract(res, true, Return(_, implct), N, curDepth)
        // Optimization to avoid generation of unnecessary variables
        case Assign(lhs, r, rest) =>
          if usesStack(r) then
            super.applyResult(r): r =>
              extract(r, false, _ => applyBlock(rest), S(lhs), curDepth)
          else
            super.applyBlock(b)
        
        case HandleBlock(l, res, par, args, cls, hdr, bod, rst) => lastWords("HandleBlock in stack safe transformation")
        
        case _ => super.applyBlock(b)
        
        override def applyHandler(hdr: Handler): Handler = lastWords("HandleBlock in stack safe transformation")
      
      override def applyResult(r: Result)(k: Result => Block): Block =
        if usesStack(r) then
          extract(r, false, k, N, curDepth)
        else
          super.applyResult(r)(k)
      
      override def applyLam(lam: Lambda): Lambda = lastWords("Lambda in stack safe transformation")
  
    transform.applyBlock(b)
  
  def isTrivial(b: Block): Boolean =
    var trivial = true
    new BlockTraverserShallow:
      applyBlock(b)
      override def applyResult(r: Result): Unit = r match
        case Call(Value.Ref(_: BuiltinSymbol), _) => ()
        case _: Call | _: Instantiate => trivial = false
        case _ => ()
    trivial
  
  def rewriteCls(defn: ClsLikeDefn, isTopLevel: Bool): ClsLikeDefn = defn.parentPath match
    case Some(value) if value eq paths.contClsPath => defn
    case _ =>
      val ClsLikeDefn(owner, isym, sym, k, paramsOpt, auxParams,
        parentPath, methods, privateFields, publicFields, preCtor, ctor, mod, bufferable) = defn
      ClsLikeDefn(
        owner, isym, sym, k, paramsOpt, auxParams, parentPath,
        methods.map(rewriteFn),
        privateFields,
        publicFields, 
        rewriteBlk(preCtor, L(BlockMemberSymbol("TODO", Nil)), 1), // TODO: preCtor is not translated in handler lowering
        if isTopLevel && (defn.k is syntax.Mod) then transformTopLevel(ctor) else rewriteBlk(ctor, R(isym), 1),
        mod.map(rewriteObjBody(_, isTopLevel)),
        bufferable,
      )
  
  def rewriteObjBody(defn: ClsLikeBody, isTopLevel: Bool): ClsLikeBody =
    ClsLikeBody(
      defn.isym,
      defn.methods.map(rewriteFn),
      defn.privateFields,
      defn.publicFields,
      if isTopLevel then transformTopLevel(defn.ctor) else rewriteBlk(defn.ctor, R(defn.isym), 1),
    )

  // fnOrCls points us to the doUnwind function
  def rewriteBlk(blk: Block, fnOrCls: FnOrCls, increment: Int) =
    var usedDepth = false
    lazy val curDepth =
      usedDepth = true
      TempSymbol(None, "curDepth")
      
    val doUnwindPath = doUnwindMap.get(fnOrCls)
    val newBody = transform(blk, curDepth)
    
    if isTrivial(blk) then
      newBody
    else if doUnwindPath.isEmpty then
      val resSym = TempSymbol(None, "stackDelayRes")
      blockBuilder
        .staticif(usedDepth, _.assign(curDepth, stackDepthPath))
        .rest(newBody)
    else
      val resSym = TempSymbol(None, "stackDelayRes")
      val rewritten = blockBuilder
        .staticif(usedDepth, _.assign(curDepth, stackDepthPath))
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(increment)))
        .assign(resSym, Call(checkDepthPath, Nil)(true, true))
        .ifthen(
          resSym.asPath,
          Case.Cls(paths.effectSigSym, paths.effectSigPath),
          Return(
            Call(doUnwindPath.get, resSym.asPath.asArg :: intLit(0).asArg :: Nil)(true, false),
            false
          )
        )
        .rest(newBody)
      // Float out defns, including the doUnwind function, so that they appear at the top of the block
      // This is because the doUnwind function must appear before the checks inserted by the stack
      // safety pass.
      // However, due to how tightly coupled the stack safety and handler lowering are, it might be
      // better to simply merge the two passes in the future.
      val (blk, defns) = doUnwindPath.get match
        case Value.Ref(sym) => rewritten.floatOutDefns()
        case _ => (rewritten, Nil)
      defns.foldLeft(blk)((acc, defn) => Define(defn, acc))

     
  def rewriteFn(defn: FunDefn) = 
    if doUnwindFns.contains(defn.sym) then defn
    else FunDefn(defn.owner, defn.sym, defn.params, rewriteBlk(defn.body, L(defn.sym), 1))

  def transformTopLevel(b: Block) = transform(b, TempSymbol(N), true)
