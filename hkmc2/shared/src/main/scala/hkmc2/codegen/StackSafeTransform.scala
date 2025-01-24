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
  private val stackDelayClsPath: Path = predefPath.selN(Tree.Ident("__StackDelay")).selN(Tree.Ident("class"))
  private val stackLimitPath: Path = predefPath.selN(STACK_LIMIT_IDENT)
  private val stackDepthPath: Path = predefPath.selN(STACK_DEPTH_IDENT)
  private val stackOffsetPath: Path = predefPath.selN(STACK_OFFSET_IDENT)
  private val stackHandlerPath: Path = predefPath.selN(STACK_HANDLER_IDENT)

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, a.asArg :: b.asArg :: Nil)(true)

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, isTailCall: Bool, f: Result => Block) =
    if isTailCall then
      blockBuilder
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .ret(res)
    else
      val tmp = TempSymbol(None, "tmp")
      val prevDepth = TempSymbol(None, "prevDepth")
      blockBuilder
        .assign(prevDepth, stackDepthPath)
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .assign(tmp, res)
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, prevDepth.asPath)
        .rest(f(tmp.asPath))

  def extractResTopLevel(res: Result, isTailCall: Bool, f: Result => Block) =
    val resumeSym = VarSymbol(Tree.Ident("resume"))
    val handlerSym = TempSymbol(None, "stackHandler")
    val resSym = TempSymbol(None, "res")
    val handlerRes = TempSymbol(None, "res")
    val curOffsetSym = TempSymbol(None, "curOffset")
    
    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("StackDelay$")
    )

    // the global stack handler is created here
    HandleBlock(
      handlerSym, resSym,
      stackDelayClsPath, clsSym,
      Handler(
        BlockMemberSymbol("perform", Nil), resumeSym, ParamList(ParamListFlags.empty, Nil, N) :: Nil,
        /* 
          fun perform() =
            let curOffset = stackOffset
            stackOffset = stackDepth
            let ret = resume()
            stackOffset = curOffset
            ret
        */
        blockBuilder
          .assign(curOffsetSym, stackOffsetPath)
          .assignFieldN(predefPath, STACK_OFFSET_IDENT, stackDepthPath)
          .assign(handlerRes, Call(Value.Ref(resumeSym), Nil)(true))
          .assignFieldN(predefPath, STACK_OFFSET_IDENT, curOffsetSym.asPath)
          .ret(handlerRes.asPath)
      ) :: Nil,
      blockBuilder
        .assignFieldN(predefPath, STACK_LIMIT_IDENT, intLit(depthLimit)) // set stackLimit before call
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(1)) // set stackDepth = 1 before call
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, handlerSym.asPath) // assign stack handler
        .rest(HandleBlockReturn(res)),
      blockBuilder // reset the stack safety values
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0 after call
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, Value.Lit(Tree.UnitLit(false))) // set stackHandler = null
        .rest(f(resSym.asPath))
    )

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block, isTopLevel: Bool = false): Block =
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
          extract(applyResult(res), true, Return(_, implct))
        case _ => super.applyBlock(b)
      
      override def applyResult2(r: Result)(k: Result => Block): Block =
        if usesStack(r) then
          extract(r, false, k)
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
    val newBody = transform(blk)

    if isTrivial(blk) then 
      newBody
    else
      val diffSym = TempSymbol(None, "diff")
      val diffGeqLimitSym = TempSymbol(None, "diffGeqLimit")
      val handlerExistsSym = TempSymbol(None, "handlerExists")
      val scrutSym = TempSymbol(None, "scrut")
      val diff = op("-", stackDepthPath, stackOffsetPath)
      val diffGeqLimit = op(">=", diffSym.asPath, stackLimitPath)
      val handlerExists = op("!==", stackHandlerPath, Value.Lit(Tree.UnitLit(false)))
      val scrutVal = op("&&", diffGeqLimitSym.asPath, handlerExistsSym.asPath)
      blockBuilder
        .assign(diffSym, diff)                    // diff = stackDepth - stackOffset
        .assign(diffGeqLimitSym, diffGeqLimit)    // diff >= depthLimit
        .assign(handlerExistsSym, handlerExists)  // stackHandler !== null
        .assign(scrutSym, scrutVal)               // diff >= depthLimit && stackHandler !== null
        .ifthen(
          scrutSym.asPath, Case.Lit(Tree.BoolLit(true)), 
          blockBuilder.assign( // dummy = perform(undefined) (is called `dummy` as the value is not used)
            TempSymbol(None, "dummy"), 
            Call(Select(stackHandlerPath, Tree.Ident("perform"))(N), Nil)(true)).end)
        .rest(newBody)
     
  def rewriteFn(defn: FunDefn) = FunDefn(defn.owner, defn.sym, defn.params, rewriteBlk(defn.body))

  def transformTopLevel(b: Block) = transform(b, true)
