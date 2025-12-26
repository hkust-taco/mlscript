package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.{Tree, SpreadKind}
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
      case Assign(a, c @ CallToFun(r), Return(Value.Ref(b, _), _)) if a === b => S((r, c))
      case _ => N
    
  
  enum CallEdge:
    val f1: TermSymbol
    val f2: TermSymbol
    val call: Call
    case TailCall(f1: TermSymbol, f2: TermSymbol)(val call: Call)
    case NormalCall(f1: TermSymbol, f2: TermSymbol)(val call: Call)
  
  class CallFinder(f: FunDefn) extends BlockTraverserShallow:
    
    var edges: List[CallEdge] = Nil
    
    def find =
      // Ignore functions with multiple parameter lists
      if f.params.length > 1 then
        if f.forceTailRec then
          raise(ErrorReport(msg"Functions with more than one parameter list may not be marked @tailrec." -> f.dSym.toLoc :: Nil))
        Nil
      else
        edges = Nil
        applyBlock(f.body)
        edges
    
    override def applyBlock(b: Block): Unit = b match
      case TailCallShape(r, c) => edges ::= CallEdge.TailCall(f.dSym, r)(c)
      case Return(c: Call, _) =>
        if c.explicitTailCall then
          raise(ErrorReport(msg"Only direct calls in tail position may be marked @tailcall." -> c.toLoc :: Nil))
      case _ => super.applyBlock(b)
    
    override def applyResult(r: Result): Unit = r match
      case c: Call =>
        if c.explicitTailCall then
          raise(ErrorReport(msg"This call is not in tail position." -> c.toLoc :: Nil))
        c match
          case CallToFun(r) => edges ::= CallEdge.NormalCall(f.dSym, r)(c)
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
        case c: CallEdge.TailCall if c.call.explicitTailCall && !cond =>
          raise(ErrorReport(
            msg"This tail call exits the current scope is not optimized." -> c.call.toLoc :: Nil))
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
        if s1 =/= s2 && c.call.explicitTailCall then
          raise(ErrorReport(
            msg"This call is not optimized as it does not directly recurse through its parent function." -> c.call.toLoc :: Nil))
          -1
        else s1
      .filter:
        (id, _) => id =/= -1
    
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
          case Some(SpreadKind.Eager) =>
            if c.explicitTailCall then
              raise(ErrorReport(msg"Spreads are not yet fully supported in calls marked @tailcall." -> a.value.toLoc :: Nil))
            bad = true
            a.value
          case _ => a.value
        if bad then return N
        
        if head.restParam.isDefined then
          val rest =
            restArgs match
              case Arg(S(SpreadKind.Eager), value) :: Nil => value
              case _ => Tuple(true, restArgs)
          hd.appended(rest)
        else
          hd
      case Nil => c.args.map(_.value)
      case _ => return N
    S(ret)
    
  def optScc(scc: SccOfCalls, owner: Opt[InnerSymbol]): (Opt[FunDefn], List[FunDefn]) =
    // sort the functions so the order is more predictable
    val funs = scc.funs.sortBy(f => f.dSym.uid)
    // remove calls which don't flow into this scc
    val fSyms = funs.map(_.dSym).toSet
    
    val calls = scc.calls.filter(c => fSyms.contains(c.f2)) 
    
    val nonTailCallsLs = calls
      .collect:
        case c: CallEdge.NormalCall => c.f2 -> c.call
    val nonTailCalls = nonTailCallsLs.toMap
    
    if nonTailCallsLs.sizeCompare(calls) === 0 then
      for f <- funs if f.forceTailRec do
        raise(WarningReport(msg"This function does not directly self-recurse, but is marked @tailrec." -> f.dSym.toLoc :: Nil))
      return (N, funs)
    
    if !nonTailCalls.isEmpty then
      for f <- funs if f.forceTailRec do
        val reportLoc = nonTailCalls.get(f.dSym) match
          // always display a call to f, if possible
          case Some(value) => value.toLoc 
          case None => nonTailCalls.head._2.toLoc
        raise(ErrorReport(
            msg"This function is not tail recursive." -> f.dSym.toLoc
            :: msg"It could self-recurse through this call, which is not a tail call." -> reportLoc
            :: Nil
          ))

    val maxParamLen = maxInt(funs, paramsLen)
    val paramSyms =
        if funs.length === 1 then (getParamSyms(funs.head))
        else
          for i <- 0 to maxParamLen - 1 yield VarSymbol(Tree.Ident("param" + i))
      .toList
    val paramSymsArr = ArrayBuffer.from(paramSyms)
    val dSymIds = funs.map(_.dSym).zipWithIndex.toMap
    val bms =
      if funs.size === 1 then funs.head.sym
      else BlockMemberSymbol(funs.map(_.sym.nme).mkString("_"), Nil, true)
    val dSym =
      if funs.size === 1 then funs.head.dSym
      else TermSymbol(syntax.Fun, owner, Tree.Ident(bms.nme))
    val loopSym = TempSymbol(N, "loopLabel")
    val curIdSym = VarSymbol(Tree.Ident("id"))
    
    class FunRewriter(f: FunDefn) extends BlockTransformerShallow(SymbolSubst()):
      val params = getParamSyms(f)
      val paramsSet = f.params.toSet
      val paramsIdxes = params.zipWithIndex.toMap
      
      val symRewriter = new BlockTransformer(SymbolSubst()):
        def applyVarSym(l: VarSymbol): VarSymbol = paramsIdxes.get(l) match
          case Some(idx) => paramSymsArr(idx)
          case _ => l
        
        override def applyValue(v: Value)(k: Value => Block): Block = v match
          case Value.Ref(l: VarSymbol, d) => 
            val s = applyVarSym(l)
            if s is l then k(v)
            else k(Value.Ref(s, d))
          case _ => super.applyValue(v)(k)
      
      
      override def applyBlock(b: Block): Block = b match
        case TailCallShape(dSym, c) => dSymIds.get(dSym) match
          case Some(id) =>
            val argVals = rewriteCallArgs(f, c) match
              case Some(value) => value
              case None => return super.applyBlock(b)
            val cont =
              if scc.funs.size === 1 then Continue(loopSym)
              else Assign(curIdSym, Value.Lit(Tree.IntLit(dSymIds(dSym))), Continue(loopSym))
            
            // In some cases, we could have assignments like this:
            // param0 = whatever
            // param1 = <a result containing param0>
            // which means param1's value is incorrect.
            // We should thus assign the params to temporary symbols
            // if they are needed for a subsequent assignment.
            var assignedSyms: Map[VarSymbol, TempSymbol] = paramSyms.map:
                case sym => sym -> TempSymbol(N, sym.nme + "_tmp")
              .toMap
            var requiredTmps: Set[(VarSymbol, TempSymbol)] = Set.empty
            
            val paramRewriter = new BlockDataTransformer(SymbolSubst()):
              override def applyValue(v: Value)(k: Value => Block): Block = v match
                case Value.Ref(l: VarSymbol, disamb) => assignedSyms.get(l) match
                  case S(v) =>
                    requiredTmps += (l, v)
                    k(Value.Ref(v, disamb))
                  case _ => super.applyValue(v)(k)
                case _ => super.applyValue(v)(k)
              
            // remove symbols from assignedSyms as we encounter them
            // note that foldRight will call the function right to left
            val assigns = paramSyms.zip(argVals).foldRight[Block](cont): (v, acc) =>
              val (sym, res) = v
              assignedSyms -= sym
              val ret = applyResult(res)(Assign(sym, _, acc)) match
                case Assign(sym, res, rest) => paramRewriter.applyResult(res)(Assign(sym, _, rest)) match
                  case Assign(sym, Value.Ref(sym1, _), rest) if sym === sym1 => rest
                  case x => x
                case x => x
              ret
            // bind the tmps
            requiredTmps.toList.foldRight(assigns):
              case ((v, l), acc) => Assign(l, Value.Ref(v), acc)
          case None => super.applyBlock(b)
        case _ => super.applyBlock(b)
      
      def rewrite(b: Block) =
        applyBlock(symRewriter.applyBlock(b))
    
    val arms = funs.map: f =>
      Case.Lit(Tree.IntLit(dSymIds(f.dSym))) -> FunRewriter(f).rewrite(f.body)
    
    val switch = 
      if arms.length === 1 then arms.head._2
      else Match(curIdSym.asPath, arms, N, End())
    
    val loop = Label(loopSym, true, switch, End())
    
    val sel = owner match
      case Some(value) => Select(Value.Ref(value, N), Tree.Ident(bms.nme))(S(dSym))
      case None => Value.Ref(bms, S(dSym))
    
    val rewrittenFuns =
      if funs.size === 1 then Nil
      else funs.map: f =>
        val paramArgs = getParamSyms(f).map(_.asPath.asArg)
        val args = 
          Value.Lit(Tree.IntLit(dSymIds(f.dSym))).asArg
            :: paramArgs
            ::: List.fill(maxParamLen - paramArgs.length)(Value.Lit(Tree.UnitLit(false)).asArg)
        val newBod = Return(
          Call(sel, args)(true, false, false),
          false
        )
        FunDefn(f.owner, f.sym, f.dSym, f.params, newBod)(false)
    
    val params =
      val initial = paramSyms.map(Param.simple(_))
      if funs.length === 1 then initial
      else Param.simple(curIdSym) :: initial
    
    val loopDefn = FunDefn(
      owner, bms, dSym,
      PlainParamList(params) :: Nil,
      loop)(false)
    
    if funs.size === 1 then (N, loopDefn :: Nil)
    else (S(loopDefn), rewrittenFuns)
  
  def optFunctions(fs: List[FunDefn], owner: Opt[InnerSymbol]) =
    val (newFsOpt, fsOpt) = partFns(fs).map(optScc(_, owner)).foldLeft[(List[FunDefn], List[FunDefn])](Nil, Nil):
      case ((newFns, fns), (newFnOpt, fns_)) => newFnOpt match
        case Some(value) => (value :: newFns, fns_ ::: fns)
        case None => (newFns, fns_ ::: fns)
    // preserve the order of function defns
    val fMap = fsOpt.map(f => (f.dSym, f)).toMap
    val fsRet = fs.map(f => fMap(f.dSym))
    (newFsOpt, fsRet)
  
  def reportClassesTailrec(c: ClsLikeDefn) =
    new BlockTraverserShallow():
      for f <- c.methods do
        applyBlock(f.body)
        if f.forceTailRec then
          raise(ErrorReport(msg"Class methods may not yet be marked @tailrec." -> f.dSym.toLoc :: Nil))
      override def applyResult(r: Result): Unit = r match
        case c: Call if c.explicitTailCall =>
          raise(ErrorReport(msg"Calls from class methods cannot yet be marked @tailcall." -> c.toLoc :: Nil))
        case _ => super.applyResult(r)
  
  def optFunctionsFlat(fs: List[FunDefn], owner: Opt[InnerSymbol]) =
    val (a, b) = optFunctions(fs, owner)
    a ::: b
    
  def optClasses(cs: List[ClsLikeDefn]) = cs.map: c =>
    // Class methods cannot yet be optimized as they cannot yet be marked final.
    
    if c.k is syntax.Cls then
      reportClassesTailrec(c)
      val companion = c.companion.map: comp =>
        val cMtds = optFunctionsFlat(comp.methods, S(comp.isym))
        comp.copy(methods = cMtds)
      c.copy(companion = companion)
    else
      val mtds = optFunctionsFlat(c.methods, S(c.isym))
      val companion = c.companion.map: comp =>
        val cMtds = optFunctionsFlat(comp.methods, S(comp.isym))
        comp.copy(methods = cMtds)
      c.copy(methods = mtds, companion = companion)
  
  def transform(b: Block) =
    val defns = b.gatherDefns()
    val (funs, clses) = defns.partitionMap:
      case f: FunDefn => L(f)
      case c: ClsLikeDefn => R(c)
      case _ => die // unreachable as floatOutDefns only floats out FunDefns and ClsLikeDefns
    val (optFNew, optF) = optFunctions(funs, N)
    val optC = optClasses(clses)
    
    val fMap = optF.map(f => f.dSym -> f).toMap
    // Scala needs this annotation to type check for some reason
    val cMap: Map[DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, ClsLikeDefn] =
      optC.map(c => c.isym -> c).toMap
    
    // replace them in place 
    val transformer = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case f: FunDefn => fMap.get(f.dSym) match
          case Some(value) => k(value)
          case None => k(f)
        
        case c: ClsLikeDefn => cMap.get(c.isym) match
          case Some(value) => k(value)
          case None => k(c)
        
        case _ => super.applyDefn(defn)(k)
    
    optFNew.foldLeft(transformer.applyBlock(b)):
      case (acc, f) => Define(f, acc)
