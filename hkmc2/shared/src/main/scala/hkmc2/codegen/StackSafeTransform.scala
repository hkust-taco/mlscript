package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree

class StackSafeTransform(depthLimit: Int, paths: HandlerPaths)(using State):
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("stackDepth")

  private val runtimePath: Path = State.runtimeSymbol.asPath
  private val checkDepthPath: Path = runtimePath.selN(Tree.Ident("checkDepth"))
  private val resetDepthPath: Path = runtimePath.selN(Tree.Ident("resetDepth"))
  private val runStackSafePath: Path = runtimePath.selN(Tree.Ident("runStackSafe"))
  private val stackDepthPath: Path = runtimePath.selN(STACK_DEPTH_IDENT)

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
      blockBuilder
        .assignFieldN(runtimePath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
        .assign(tmp, res)
        .assign(tmp, Call(resetDepthPath, tmp.asPath.asArg :: curDepth.asPath.asArg :: Nil)(true, false))
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
        
        case HandleBlock(l, res, par, args, cls, hdr, bod, rst) => lastWords("HandleBlock in stack safe transformation")
        
        case _ => super.applyBlock(b)
        
        override def applyHandler(hdr: Handler): Handler = lastWords("HandleBlock in stack safe transformation")
      
      override def applyResult2(r: Result)(k: Result => Block): Block =
        if usesStack(r) then
          extract(r, false, k, N, curDepth)
        else
          super.applyResult2(r)(k)
      
      override def applyLam(lam: Value.Lam): Value.Lam = lastWords("Lambda in stack safe transformation")
  
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

  def rewriteCls(defn: ClsLikeDefn, isTopLevel: Bool): ClsLikeDefn = 
    val ClsLikeDefn(owner, isym, sym, k, paramsOpt, auxParams,
      parentPath, methods, privateFields, publicFields, preCtor, ctor) = defn
    ClsLikeDefn(
      owner, isym, sym, k, paramsOpt, auxParams, parentPath, methods.map(rewriteFn), privateFields,
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
        // .ifthen(resSym, Case.Lit(BoolLit(true)),  N)
        .rest(newBody)
     
  def rewriteFn(defn: FunDefn) = FunDefn(defn.owner, defn.sym, defn.params, rewriteBlk(defn.body))

  def transformTopLevel(b: Block) = transform(b, TempSymbol(N), true)
