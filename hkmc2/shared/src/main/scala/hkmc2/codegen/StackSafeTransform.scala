package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree

class StackSafeTransform(depthLimit: Int)(using State):
  private val STACK_LIMIT_IDENT: Tree.Ident = Tree.Ident("stackLimit")
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("stackDepth")
  private val STACK_OFFSET_IDENT: Tree.Ident = Tree.Ident("stackOffset")
  private val STACK_HANDLER_IDENT: Tree.Ident = Tree.Ident("stackHandler")

  private val runtimePath: Path = State.runtimeSymbol.asPath
  private val checkDepthPath: Path = runtimePath.selN(Tree.Ident("checkDepth"))
  private val resetDepthPath: Path = runtimePath.selN(Tree.Ident("resetDepth"))
  private val stackDelayClsPath: Path = runtimePath.selN(Tree.Ident("StackDelay"))
  private val stackLimitPath: Path = runtimePath.selN(STACK_LIMIT_IDENT)
  private val stackDepthPath: Path = runtimePath.selN(STACK_DEPTH_IDENT)
  private val stackOffsetPath: Path = runtimePath.selN(STACK_OFFSET_IDENT)
  private val stackHandlerPath: Path = runtimePath.selN(STACK_HANDLER_IDENT)

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, a.asArg :: b.asArg :: Nil)(true, false)

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, isTailCall: Bool, f: Result => Block, sym: Option[Symbol], curDepth: => Symbol) =
    if isTailCall then
      blockBuilder
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .ret(res)
    else
      val tmp = sym getOrElse TempSymbol(None, "tmp")
      val offsetGtDepth = TempSymbol(None, "offsetGtDepth")
      blockBuilder
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .assign(tmp, res)
        .assign(tmp, Call(resetDepthPath, tmp.asPath.asArg :: curDepth.asPath.asArg :: Nil)(true, false))
        .rest(f(tmp.asPath))
  
  def wrapStackSafe(body: Block, resSym: Local, rest: Block) =
    val resumeSym = VarSymbol(Tree.Ident("resume"))
    val handlerSym = TempSymbol(None, "stackHandler")
    
    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("StackDelay$")
    )

    // the global stack handler is created here
    HandleBlock(
      handlerSym, resSym,
      stackDelayClsPath, Nil, clsSym,
      Handler(
        BlockMemberSymbol("perform", Nil), resumeSym, ParamList(ParamListFlags.empty, Nil, N) :: Nil,
        /* 
          fun perform() =
            stackOffset = stackDepth
            resume()
        */
        blockBuilder
          .assignFieldN(runtimePath, STACK_OFFSET_IDENT, stackDepthPath)
          .ret(Call(Value.Ref(resumeSym), Nil)(true, true))
      ) :: Nil,
      blockBuilder
        .assignFieldN(runtimePath, STACK_LIMIT_IDENT, intLit(depthLimit)) // set stackLimit before call
        .assignFieldN(runtimePath, STACK_OFFSET_IDENT, intLit(0)) // set stackOffset = 0 before call
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, intLit(1)) // set stackDepth = 1 before call
        .assignFieldN(runtimePath, STACK_HANDLER_IDENT, handlerSym.asPath) // assign stack handler
        .rest(body),
      blockBuilder // reset the stack safety values
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0 after call
        .assignFieldN(runtimePath, STACK_HANDLER_IDENT, Value.Lit(Tree.UnitLit(true))) // set stackHandler = null
        .rest(rest)
    )

  def extractResTopLevel(res: Result, isTailCall: Bool, f: Result => Block, sym: Option[Symbol], curDepth: => Symbol) =
    val resSym = sym getOrElse TempSymbol(None, "res")
    wrapStackSafe(HandleBlockReturn(res), resSym, f(resSym.asPath))

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block, curDepth: => Symbol, isTopLevel: Bool = false): Block =
    def usesStack(r: Result) = r match
      case Call(Value.Ref(_: BuiltinSymbol), _) => false
      case _: Call | _: Instantiate => true
      case _ => false

    val extract = if isTopLevel then extractResTopLevel else extractRes
    
    val transform = new BlockTransformer(SymbolSubst()):

      override def applyFunDefn(fun: FunDefn): FunDefn = rewriteFn(fun)
      
      override def applyDefn(defn: Defn): Defn = defn match
        case defn: ClsLikeDefn => rewriteCls(defn, isTopLevel)
        case _: FunDefn | _: ValDefn => super.applyDefn(defn)

      override def applyBlock(b: Block): Block = b match
        case Return(res, implct) if usesStack(res) =>
          extract(applyResult(res), true, Return(_, implct), N, curDepth)
        // Optimization to avoid generation of unnecessary variables
        case Assign(lhs, r, rest) =>
          if usesStack(r) then
            extract(applyResult(r), false, _ => applyBlock(rest), S(lhs), curDepth)
          else
            super.applyBlock(b)
        case HandleBlock(l, res, par, args, cls, hdr, bod, rst) =>
          val l2 = applyLocal(l)
          val res2 = applyLocal(res)
          val par2 = applyPath(par)
          val args2 = args.mapConserve(applyPath)
          val cls2 = cls.subst
          val hdr2 = hdr.mapConserve(applyHandler)
          val bod2 = rewriteBlk(bod)
          val rst2 = applyBlock(rst)
          if isTopLevel then
            val newRes = TempSymbol(N, "res")
            val newHandler = HandleBlock(l2, newRes, par2, args2, cls2, hdr2, bod2, HandleBlockReturn(newRes.asPath))
            wrapStackSafe(newHandler, res2, rst2)
          else
            HandleBlock(l2, res2, par2, args2, cls2, hdr2, bod2, rst2)
        
        case _ => super.applyBlock(b)
        
        override def applyHandler(hdr: Handler): Handler =
          val sym2 = hdr.sym.subst
          val resumeSym2 = hdr.resumeSym.subst
          val params2 = hdr.params.mapConserve(applyParamList)
          val body2 = rewriteBlk(hdr.body)
          Handler(sym2, resumeSym2, params2, body2)
      
      override def applyResult2(r: Result)(k: Result => Block): Block =
        if usesStack(r) then
          extract(r, false, k, N, curDepth)
        else
          super.applyResult2(r)(k)
      
      override def applyLam(lam: Value.Lam): Value.Lam =
        Value.Lam(lam.params, rewriteBlk(lam.body))
  
    transform.applyBlock(b)
  
  def isTrivial(b: Block): Boolean =
    var trivial = true
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyResult(r: Result): Result = r match
        case Call(Value.Ref(_: BuiltinSymbol), _) => r
        case _: Call | _: Instantiate => trivial = false; r
        case _ => r
    walker.applyBlock(b)
    trivial

  def rewriteCls(defn: ClsLikeDefn, isTopLevel: Bool): ClsLikeDefn = 
    val ClsLikeDefn(owner, isym, sym, k, paramsOpt, 
      parentPath, methods, privateFields, publicFields, preCtor, ctor) = defn
    ClsLikeDefn(
      owner, isym, sym, k, paramsOpt, parentPath, methods.map(rewriteFn), privateFields,
      publicFields, rewriteBlk(preCtor),
      if isTopLevel && (defn.k is syntax.Mod) then transformTopLevel(ctor) else rewriteBlk(ctor)
    )

  def rewriteBlk(blk: Block) =
    var usedDepth = false
    lazy val curDepth =
      usedDepth = true
      TempSymbol(None, "curDepth")
    val newBody = transform(blk, curDepth)

    if isTrivial(blk) then
      newBody
    else
      val resSym = TempSymbol(None, "stackDelayRes")
      blockBuilder
        .staticif(usedDepth, _.assign(curDepth, stackDepthPath))
        .assign(resSym, Call(checkDepthPath, Nil)(true, true))
        .rest(newBody)
     
  def rewriteFn(defn: FunDefn) = FunDefn(defn.owner, defn.sym, defn.params, rewriteBlk(defn.body))

  def transformTopLevel(b: Block) = transform(b, TempSymbol(N), true)
