package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree

class StackSafeTransform(depthLimit: Int)(using State):
  private val STACK_LIMIT_IDENT: Tree.Ident = Tree.Ident("__stackLimit")
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("__stackDepth")
  private val STACK_OFFSET_IDENT: Tree.Ident = Tree.Ident("__stackOffset")
  private val STACK_HANDLER_IDENT: Tree.Ident = Tree.Ident("__stackHandler")

  private val predefPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef"))
  private val checkDepthPath: Path = predefPath.selN(Tree.Ident("checkDepth"))
  private val resetDepthPath: Path = predefPath.selN(Tree.Ident("resetDepth"))
  private val stackDelayClsPath: Path = predefPath.selN(Tree.Ident("__StackDelay"))
  private val stackLimitPath: Path = predefPath.selN(STACK_LIMIT_IDENT)
  private val stackDepthPath: Path = predefPath.selN(STACK_DEPTH_IDENT)
  private val stackOffsetPath: Path = predefPath.selN(STACK_OFFSET_IDENT)
  private val stackHandlerPath: Path = predefPath.selN(STACK_HANDLER_IDENT)

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, a.asArg :: b.asArg :: Nil)(true, false)

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, isTailCall: Bool, f: Result => Block, sym: Option[Symbol], curDepth: => Symbol) =
    if isTailCall then
      blockBuilder
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .ret(res)
    else
      val tmp = sym getOrElse TempSymbol(None, "tmp")
      val offsetGtDepth = TempSymbol(None, "offsetGtDepth")
      blockBuilder
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .assign(tmp, res)
        .assign(tmp, Call(resetDepthPath, tmp.asPath.asArg :: curDepth.asPath.asArg :: Nil)(true, false))
        .rest(f(tmp.asPath))

  def extractResTopLevel(res: Result, isTailCall: Bool, f: Result => Block, sym: Option[Symbol], curDepth: => Symbol) =
    val resumeSym = VarSymbol(Tree.Ident("resume"))
    val handlerSym = TempSymbol(None, "stackHandler")
    val resSym = sym getOrElse TempSymbol(None, "res")
    val handlerRes = TempSymbol(None, "res")
    
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
            let ret = resume()
            ret
        */
        blockBuilder
          .assignFieldN(predefPath, STACK_OFFSET_IDENT, stackDepthPath)
          .assign(handlerRes, Call(Value.Ref(resumeSym), Nil)(true, true))
          .ret(handlerRes.asPath)
      ) :: Nil,
      blockBuilder
        .assignFieldN(predefPath, STACK_LIMIT_IDENT, intLit(depthLimit)) // set stackLimit before call
        .assignFieldN(predefPath, STACK_OFFSET_IDENT, intLit(0)) // set stackOffset = 0 before call
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(1)) // set stackDepth = 1 before call
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, handlerSym.asPath) // assign stack handler
        .rest(HandleBlockReturn(res)),
      blockBuilder // reset the stack safety values
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0 after call
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, Value.Lit(Tree.UnitLit(true))) // set stackHandler = null
        .rest(f(resSym.asPath))
    )

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
        case defn: ClsLikeDefn => rewriteCls(defn)
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
          HandleBlock(l2, res2, par2, args2, cls2, hdr2, bod2, rst2)
        case _ => super.applyBlock(b)
      
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

  def rewriteCls(defn: ClsLikeDefn): ClsLikeDefn = 
    val ClsLikeDefn(owner, isym, sym, k, paramsOpt, 
      parentPath, methods, privateFields, publicFields, preCtor, ctor) = defn
    ClsLikeDefn(
      owner, isym, sym, k, paramsOpt, parentPath, methods.map(rewriteFn), privateFields,
      publicFields, rewriteBlk(preCtor), rewriteBlk(ctor)
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
