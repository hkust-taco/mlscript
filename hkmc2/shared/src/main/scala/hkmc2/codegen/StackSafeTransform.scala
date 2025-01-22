package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree
import hkmc2.syntax.Keyword.`with`


class StackSafeTransform(depthLimit: Int)(using State):
  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("__stackDepth")
  private val STACK_OFFSET_IDENT: Tree.Ident = Tree.Ident("__stackOffset")
  private val STACK_HANDLER_IDENT: Tree.Ident = Tree.Ident("__stackHandler")

  private val stackDelayClsPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__StackDelay")).selN(Tree.Ident("class"))
  private val stackDepthPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(STACK_DEPTH_IDENT)
  private val stackOffsetPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(STACK_OFFSET_IDENT)
  private val stackHandlerPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(STACK_HANDLER_IDENT)
  private val predefPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef"))

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, List(a.asArg, b.asArg))(true)

  // TODO: this code is copied from HandlerLowering and is quite useful. Maybe refactor it into a utils file

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, isTailCall: Bool, f: Result => Block) =
    res match
      case Call(Value.Ref(s: BuiltinSymbol), args) => f(res)
      case _: Call | _: Instantiate =>
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
      case _ => f(res)

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block): Block = 
    // 1. rewrite lambdas
    def firstPass(b: Block): Block =
      val transform = new BlockTransformerShallow(SymbolSubst()):
        override def applyValue(v: Value): Value = v match
          case Value.Lam(params, body) => Value.Lam(params, rewriteBlk(body))
          case _ => super.applyValue(v)
        
        override def applyBlock(b: Block): Block = b match
          case HandleBlock(lhs, res, par, cls, handlers, body, rest) =>
            HandleBlock(
              lhs, res, par, cls, handlers.map(h => Handler(h.sym, h.resumeSym, h.params, applyBlock(h.body))),
              applyBlock(body), applyBlock(rest)
            )
          case _ => super.applyBlock(b)
        
      transform.applyBlock(b)
    
    // 2. rewrite calls and definitions
    def secondPass(b: Block): Block = 
      val transform = new BlockTransformerShallow(SymbolSubst()):
        override def applyDefn(defn: Defn): Defn = rewriteDefn(defn)

        override def applyBlock(b: Block): Block = b match
          case Return(c: Call, implct) => extractRes(c, true, Return(_, false))
          case Return(res, implct) => extractRes(res, false, Return(_, false))
          case Assign(lhs, rhs, rest) => 
            extractRes(rhs, false, Assign(lhs, _, applyBlock(rest)))
          case b @ AssignField(lhs, nme, rhs, rest) => extractRes(rhs, false, AssignField(lhs, nme, _, applyBlock(rest))(b.symbol))
          case Define(defn, rest) => Define(rewriteDefn(defn), applyBlock(rest))
          case HandleBlock(lhs, res, par, cls, handlers, body, rest) =>
            HandleBlock(
              lhs, res, par, cls, handlers.map(h => Handler(h.sym, h.resumeSym, h.params, applyBlock(h.body))),
              applyBlock(body), applyBlock(rest)
            )
          case HandleBlockReturn(c: Call) => extractRes(c, true, HandleBlockReturn(_))
          case HandleBlockReturn(res) => extractRes(res, false, HandleBlockReturn(_))
          case _ => super.applyBlock(b)
      transform.applyBlock(b)
    
    secondPass(firstPass(b))
  
  def isTrivial(b: Block): Boolean = 
    def resTrivial(r: Result) = r match
      case Call(Value.Ref(_: BuiltinSymbol), _) => true
      case _: Call => false
      case _: Instantiate => false
      case _ => true

    b match
      case Match(scrut, arms, dflt, rest) => 
        arms.foldLeft(dflt.map(isTrivial).getOrElse(true))((acc, bl) => acc && isTrivial(bl._2)) && isTrivial(rest)
      case Return(res, implct) => resTrivial(res)
      case Throw(exc) => resTrivial(exc)
      case Label(label, body, rest) => isTrivial(body) && isTrivial(rest)
      case Break(label) => true
      case Continue(label) => true
      case Begin(sub, rest) => isTrivial(sub) && isTrivial(rest)
      case TryBlock(sub, finallyDo, rest) => isTrivial(sub) && isTrivial(finallyDo) && isTrivial(rest)
      case Assign(lhs, rhs, rest) => resTrivial(rhs) && isTrivial(rest)
      case AssignField(lhs, nme, rhs, rest) => resTrivial(rhs) && isTrivial(rest)
      case Define(defn, rest) => isTrivial(rest)
      case HandleBlock(lhs, res, par, cls, handlers, body, rest) => isTrivial(body) && isTrivial(rest) 
      case HandleBlockReturn(res) => true
      case End(msg) => true

  def rewriteDefn(defn: Defn) = 
    defn match
    case d: FunDefn => rewriteFn(d)
    case _: ValDefn => defn
    case ClsLikeDefn(sym, k, parentPath, methods, privateFields, publicFields, preCtor, ctor) =>
      ClsLikeDefn(
        sym, k, parentPath, methods.map(rewriteFn), privateFields, publicFields,
        rewriteBlk(preCtor), rewriteBlk(ctor) // TODO: do we need to rewrite the preCtor?
      )

  def rewriteBlk(blk: Block) =
    val newBody = transform(blk)

    if isTrivial(blk) then 
      newBody
    else
      val diffSym = TempSymbol(None, "diff")
      val scrut1Sym = TempSymbol(None, "scrut1")
      val scrut2Sym = TempSymbol(None, "scrut2")
      val scrutSym = TempSymbol(None, "scrut")
      val diff = op("-", stackDepthPath, stackOffsetPath)
      val scrut1 = op(">=", diffSym.asPath, intLit(depthLimit))
      val scrut2 = op("!==", stackHandlerPath, Value.Lit(Tree.UnitLit(false)))
      val scrutVal = op("&&", scrut1Sym.asPath, scrut2Sym.asPath)
      blockBuilder
        .assign(diffSym, diff)        // diff = stackDepth - stackOffset
        .assign(scrut1Sym, scrut1)    // diff >= depthLimit
        .assign(scrut2Sym, scrut2)    // stackHandler !== null
        .assign(scrutSym, scrutVal)   // diff >= depthLimit && stackHandler !== null
        .ifthen(
          scrutSym.asPath, Case.Lit(Tree.BoolLit(true)), 
          blockBuilder.assign( // tmp = perform(undefined)
            TempSymbol(None, "tmp"), 
            Call(Select(stackHandlerPath, Tree.Ident("perform"))(N), Nil)(true)).end)
        .rest(newBody)
     
  def rewriteFn(defn: FunDefn) = FunDefn(defn.sym, defn.params, rewriteBlk(defn.body))

  def transformTopLevel(b: Block) =
    def replaceReturns(b: Block): Block =
      val transform = new BlockTransformerShallow(SymbolSubst()):
        override def applyBlock(b: Block): Block = b match
          case Return(res, _) => HandleBlockReturn(res)
          case HandleBlock(lhs, res, par, cls, handlers, body, rest) =>
            HandleBlock(
              lhs, res, par, cls, handlers,
              applyBlock(body), applyBlock(rest)
            )
          case _ => super.applyBlock(b)
      transform.applyBlock(b)
    
    // symbols
    val resumeSym = VarSymbol(Tree.Ident("resume"))
    val handlerSym = TempSymbol(None, "stackHandler")
    val resSym = TempSymbol(None, "res")
    val handlerRes = TempSymbol(None, "res")
    val curOffsetSym = TempSymbol(None, "curOffset")
    
    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("StackDelay$")
    )
    clsSym.defn = S(ClassDef(N, syntax.Cls, clsSym, Nil, N, ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true)))), Nil))

    val (blk, defns) = b.floatOutDefns(true)

    // the global stack handler is created here
    val handle = HandleBlock(
      handlerSym, resSym,
      stackDelayClsPath, clsSym,
      List(Handler(
        BlockMemberSymbol("perform", Nil), resumeSym, List(ParamList(ParamListFlags.empty, Nil, N)),
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
          .assign(handlerRes, Call(Value.Ref(resumeSym), List())(true))
          .assignFieldN(predefPath, STACK_OFFSET_IDENT, curOffsetSym.asPath)
          .ret(handlerRes.asPath)
      )),
      blockBuilder
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, handlerSym.asPath) // assign stack handler
        .rest(replaceReturns(transform(blk))), // transform the rest of the body
      blockBuilder // reset the stack safety values
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, Value.Lit(Tree.UnitLit(false))) // set stackHandler = null
        .rest(Return(Value.Ref(resSym), true))
    )

    defns.foldLeft[Block](handle)((blk, defn) => Define(rewriteDefn(defn), blk))