package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import scala.collection.mutable.ArrayBuffer
import java.lang.instrument.ClassDefinition

// This optimization assumes the lifter has been run.
class TailRecOpt(using State, TL, Raise):
  
  object CallToFun:
    def unapply(c: Call): Opt[TermSymbol] = c match
      case Call(fun = Value.Ref(b, S(r: TermSymbol))) => S(r)
      case Call(fun = s: Select) => s.symbol match
        case Some(r: TermSymbol) => S(r)
        case _ => N
      case _ => N
  
  object TailCallShape:
    def unapply(b: Block): Opt[(TermSymbol, Call)] = b match
      case Return(c @ CallToFun(r), _) => S((r, c))
      case Assign(a, c @ CallToFun(r), Return(b, _)) if a == b => S((r, c))
      case _ => N
    
  
  sealed abstract class CallEdge:
    val f1: TermSymbol
    val f2: TermSymbol
    val call: Call
  
  case class TailCall(f1: TermSymbol, f2: TermSymbol)(val call: Call) extends CallEdge
  case class NormalCall(f1: TermSymbol, f2: TermSymbol)(val call: Call) extends CallEdge
  
  class CallFinder(f: FunDefn) extends BlockTraverserShallow:
    
    var edges: List[CallEdge] = Nil
    
    def find =
      // Ignore functions with multiple parameter lists
      if f.params.length > 1 then
        if f.isTailRec then
          raise(ErrorReport(msg"Functions with more than one parameter list may not be marked @tailrec." -> f.dSym.toLoc :: Nil))
        Nil
      else
        edges = Nil
        applyBlock(f.body)
        edges
    
    override def applyBlock(b: Block): Unit = b match
      case TailCallShape(r, c) => edges ::= TailCall(f.dSym, r)(c)
      case Return(c: Call, _) =>
        if c.explicitTailCall then
          raise(ErrorReport(msg"Only direct calls in tail position may be marked @tailcall." -> c.toLoc :: Nil))
      case _ => super.applyBlock(b)
    
    override def applyResult(r: Result): Unit = r match
      case c: Call =>
        if c.explicitTailCall then
          raise(ErrorReport(msg"This call is not in tail position." -> c.toLoc :: Nil))
        c match
          case CallToFun(r) => edges ::= NormalCall(f.dSym, r)(c)
          case _ =>
      case _ => super.applyResult(r)
  
  def buildCallGraph(fs: List[FunDefn]): List[CallEdge] =
    fs.flatMap(f => CallFinder(f).find)
  
  case class SccOfCalls(funs: List[FunDefn], calls: List[CallEdge])
  
  def partFns(fs: List[FunDefn]): List[SccOfCalls] =
    val defnSyms = fs.map(_.dSym)
    val tsToDefn = fs.map(f => f.dSym -> f).toMap
    
    // Only care about calls to functions in the same scope
    // Note that the results may differ if the lifter has been run.
    val cg = buildCallGraph(fs).filter: c =>
      val cond = defnSyms.contains(c.f1) && defnSyms.contains(c.f2)
      c.match
        case c: TailCall if c.call.explicitTailCall && !cond =>
          raise(ErrorReport(
            msg"This tail call exits the current scope and cannot be optimized." -> c.call.toLoc :: Nil))
        case _ =>
      cond
    
    val cgTup = cg.map(c => (c.f1, c.f2))
    val sccs = algorithms.sccsWithInfo(cgTup, defnSyms)
    
    // partition the call graph
    val sccMap = sccs.sccs.flatMap:
      case (id, scc) => scc.map(f => f -> id)
    
    val cgLabelled = cg
      .groupBy: c =>
        val s1 = sccMap(c.f1)
        val s2 = sccMap(c.f2)
        if s1 != s2 && c.call.explicitTailCall then
          raise(ErrorReport(
            msg"This call is not optimized as it does not directly recurse through its parent function." -> c.call.toLoc :: Nil))
          -1
        else s1
      .filter:
        (id, _) => id != -1
    
    sccs.sccs.toList.map: v =>
      val (id, tss) = v
      val cgs = cgLabelled.get(id) match
        case Some(value) => value
        case None => Nil
      SccOfCalls(tss.map(tsToDefn), cgs)
  
  def maxInt[T](items: List[T], f: T => Int): Int = items.foldLeft(0):
    case (l, item) =>
      val x = f(item)
      if x > l then x else l
  
  def getParamSyms(f: FunDefn) = f.params.headOption match
    case Some(ParamList(_, params, S(rest))) =>
      params.map(_.sym).appended(rest.sym)
    case Some(p) => p.params.map(_.sym)
    case None => Nil
  
  // assume only one parameter list
  def paramsLen(f: FunDefn): Int = f.params match
    case head :: next =>
      if head.restParam.isDefined then 1 + head.params.length
      else head.params.length
    case Nil => 0
  
  def rewriteCallArgs(f: FunDefn, c: Call): Opt[List[Result]] =
    // need to be careful in handling restParams
    // if any arg is a spread that spreads across multiple parameters, then
    // we ignore it for now
    val ret = f.params match
      case head :: Nil =>
        val (headArgs, restArgs) = head.restParam match
          case Some(value) => c.args.splitAt(head.params.length)
          case None => (c.args, Nil)
        
        var bad = false
        val hd = for a <- headArgs yield a.spread match
          case Some(true) =>
            if c.explicitTailCall then
              raise(ErrorReport(msg"Spreads are not yet supported here in calls marked @tailcall." -> a.value.toLoc :: Nil))
            bad = true
            a.value
          case _ => a.value
        if bad then return N
        
        if head.restParam.isDefined then
          val rest =
            restArgs match
              case Arg(S(true), value) :: Nil => value
              case _ => Tuple(true, restArgs)
          hd.appended(rest)
        else
          hd
      case Nil => c.args.map(_.value)
      case _ => return N
    S(ret)
    
  def optScc(scc: SccOfCalls, owner: Opt[InnerSymbol]): List[FunDefn] =
    if scc.calls.size == 0 then return scc.funs
    
    val nonTailCalls = scc.calls
      .collect:
        case c: NormalCall => c.f2 -> c.call
      .toMap
    
    if !nonTailCalls.isEmpty then
      for f <- scc.funs if f.isTailRec do
        val reportLoc = nonTailCalls.get(f.dSym) match
          // always display a call to f, if possible
          case Some(value) => value.toLoc 
          case None => nonTailCalls.head._2.toLoc
        raise(ErrorReport(
            msg"`${f.sym.nme}` is not tail recursive." -> f.dSym.toLoc
            :: msg"It could self-recurse through this call, which is not a tail call." -> reportLoc
            :: Nil
          ))

    val maxParamLen = maxInt(scc.funs, paramsLen)
    val paramSyms =
        if scc.funs.length == 1 then (getParamSyms(scc.funs.head))
        else
          for i <- 0 to maxParamLen - 1 yield VarSymbol(Tree.Ident("param" + i))
      .toList
    val paramSymsArr = ArrayBuffer.from(paramSyms)
    val dSymIds = scc.funs.map(_.dSym).zipWithIndex.toMap
    val bms = 
      if scc.funs.size == 1 then scc.funs.head.sym
      else BlockMemberSymbol(scc.funs.map(_.sym.nme).mkString("_"), Nil, true)
    val dSym = 
      if scc.funs.size == 1 then scc.funs.head.dSym
      else TermSymbol(syntax.Fun, owner, Tree.Ident(bms.nme))
    val loopSym = TempSymbol(N, "loopLabel")
    val curIdSym = VarSymbol(Tree.Ident("id"))
    
    class FunRewriter(f: FunDefn) extends BlockTransformer(SymbolSubst()):
      val params = getParamSyms(f)
      val paramsSet = f.params.toSet
      val paramsIdxes = params.zipWithIndex.toMap
      
      def applyVarSym(l: VarSymbol): VarSymbol = paramsIdxes.get(l) match
        case Some(idx) => paramSymsArr(idx)
        case _ => l
      
      override def applyValue(v: Value)(k: Value => Block): Block = v match
        case Value.Ref(l: VarSymbol, d) => k(Value.Ref(applyVarSym(l), d))
        case _ => super.applyValue(v)(k)
      
      override def applyBlock(b: Block): Block = b match
        case TailCallShape(dSym, c) => dSymIds.get(dSym) match
          case Some(id) =>
            val argVals = rewriteCallArgs(f, c) match
              case Some(value) => value
              case None => return super.applyBlock(b)
            val cont = Assign(curIdSym, Value.Lit(Tree.IntLit(dSymIds(dSym))), Continue(loopSym))
            paramSyms.zip(argVals).foldRight[Block](cont):
              case ((sym, res), acc) => res match
                case Value.Ref(`sym`, _) => acc
                case _ => applyResult(res)(Assign(sym, _, acc))
          case None => super.applyBlock(b)
        case _ => super.applyBlock(b)
    
    val arms = scc.funs.map: f =>
      Case.Lit(Tree.IntLit(dSymIds(f.dSym))) -> FunRewriter(f).applyBlock(f.body)
    
    val switch = 
      if arms.length == 1 then arms.head._2
      else Match(curIdSym.asPath, arms, N, End())
    
    val loop = Label(loopSym, true, switch, End())
    
    val rewrittenFuns =
      if scc.funs.size == 1 then Nil
      else scc.funs.map: f =>
        val paramArgs = getParamSyms(f).map(_.asPath.asArg)
        val args = 
          Value.Lit(Tree.IntLit(dSymIds(f.dSym))).asArg
            :: paramArgs
            ::: List.fill(maxParamLen - paramArgs.length)(Value.Lit(Tree.UnitLit(false)).asArg)
        val newBod = Return(
          Call(Value.Ref(bms, S(dSym)), args)(true, false, false),
          false
        )
        FunDefn(f.owner, f.sym, f.dSym, f.params, newBod)(false)
    
    val params =
      val initial = paramSyms.map(Param.simple(_))
      if scc.funs.length == 1 then initial
      else Param.simple(curIdSym) :: initial
      
    FunDefn(
      owner, bms, dSym,
      PlainParamList(params) :: Nil,
      loop
    )(false) :: rewrittenFuns
  
  def optFunctions(fs: List[FunDefn], owner: Opt[InnerSymbol]) =
    partFns(fs).flatMap(optScc(_, owner))
  
  def optClasses(cs: List[ClsLikeDefn]) = cs.map: c =>
    val mtds = optFunctions(c.methods, S(c.isym))
    val companion = c.companion.map: comp =>
      val cMtds = optFunctions(comp.methods, S(comp.isym))
      comp.copy(methods = cMtds)
    c.copy(methods = mtds, companion = companion)
    
  def transform(b: Block) =
    val (blk, defns) = b.floatOutDefns()
    val (funs, clses) = 
      defns.foldLeft[(List[FunDefn], List[ClsLikeDefn])](Nil, Nil):
        case ((fs, cs), d) => d match
          case f: FunDefn => (f :: fs, cs)
          case c: ClsLikeDefn => (fs, c :: cs)
          case _ => (fs, cs) // unreachable as floatOutDefns only floats out FunDefns and ClsLikeDefns
    val bod1 = optFunctions(funs, N).foldLeft(blk):
      case (acc, f) => Define(f, acc)
    optClasses(clses).foldLeft(bod1):
      case (acc, c) => Define(c, acc)
