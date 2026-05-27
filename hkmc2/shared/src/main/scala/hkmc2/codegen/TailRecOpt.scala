package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.{Tree, SpreadKind}
import hkmc2.ScopeData.*
import hkmc2.Lifter.AccessInfo
import scala.collection.mutable.ArrayBuffer
import java.lang.instrument.ClassDefinition

/*

DOCUMENTATION OF SEMANTICS OF @tailcall and @tailrec

@tailcall: Used to annotate specific function calls. Calls annotated with @tailcall 
must be tail calls. These calls must be optimized to not consume additional stack
space. If such an optimization is not possible, then the compiler will report an error.

@tailrec: Used to annotate functions. When this annotation is used on a function, say
`@tailrec fun foo()`, the compiler will ensure no sequence of statically known recursive calls back 
to foo() consumes stack space, i.e. they are all tail calls. For example,

@tailrec 
fun foo() =
  bar()
  foo()

fun bar() =
  bar()
  bar()

is valid. However,

@tailrec
fun foo() =
  bar()
fun bar() =
  foo()
  bar()

is invalid. If we swap the position of foo() and bar() in the body of bar, i.e.

@tailrec
fun foo() =
  bar()
fun bar() =
  bar()
  foo()

it is still invalid, since the following sequence of calls from foo to foo would incur extra stack space:
      foo
  ->  bar (tail call)
  ->  bar (not a tail call)
  ->  foo (tail call)

Equivalently, if fun foo() is annotated with @tailrec, let S be the largest strongly
connected component in the call-graph of the program that contains foo. Then an error
will be thrown unless all edges (calls) connecting the nodes of the strongly
connected component are tail calls.

*/

// This optimization assumes the lifter has been run.
class TailRecOpt(using State, TL, Raise):
  
  type AccessMap = Map[ScopedInfo, AccessInfo]
  
  object CallToFun:
    def unapply(c: Call): Opt[TermSymbol] = c match
      case Call(fun = Value.MemberRef(_, r: TermSymbol)) => S(r)
      case Call(fun = s: Select) => s.symbol match
        case Some(r: TermSymbol) => S(r)
        case _ => N
      case _ => N
  
  object TailCallShape:
    def unapply(b: Block): Opt[(TermSymbol, Call)] = b match
      case Return(c @ CallToFun(r)) => S((r, c))
      case Assign(a, c @ CallToFun(r), Return(Value.MemberRef(b, _))) if a === b => S((r, c))
      case _ => N
    
  
  enum CallEdge:
    val f1: TermSymbol
    val f2: TermSymbol
    val call: Call
    case TailCall(f1: TermSymbol, f2: TermSymbol)(val call: Call)
    case NormalCall(f1: TermSymbol, f2: TermSymbol)(val call: Call)
  
  class CallFinder(f: FunDefn)(using data: (ScopeData, AccessMap)) extends BlockTraverserShallow:
    
    val scopeData = data._1
    
    var edges: List[CallEdge] = Nil
    
    def find =
      edges = Nil
      applyBlock(f.body)
      edges
    
    def getFun(d: TermSymbol) = 
      if scopeData.contains(d) then
        scopeData.getNode(d) match
        case ScopeNode(obj = ScopedObject.Func(f, _)) => S(f)
        case _ => N
      else N
    
    override def applyBlock(b: Block): Unit = b match
      case TailCallShape(r, c) => getFun(r) match
        case Some(value) =>
          if c.argss.size != value.params.size then
            if c.explicitTailCall then
              raise(ErrorReport(msg"Only fully applied calls may be marked @tailcall." -> c.toLoc :: Nil))
          else edges ::= CallEdge.TailCall(f.dSym, r)(c)
        case None =>
          if c.explicitTailCall then
            raise(ErrorReport(msg"Only functions in this compilation unit may be marked @tailcall." -> c.toLoc :: Nil))
      case Return(c: Call) =>
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
  
  def buildCallGraph(fs: List[FunDefn])(using (ScopeData, AccessMap)): List[CallEdge] =
    fs.flatMap(f => CallFinder(f).find)
  
  case class SccOfCalls(funs: List[FunDefn], calls: List[CallEdge])
  
  def partFns(fs: List[FunDefn])(using (ScopeData, AccessMap)): List[SccOfCalls] =
    val defnSyms = fs.map(_.dSym)
    val tsToDefn = fs.map(f => f.dSym -> f).toMap
    
    // Only care about calls to functions in the same scope
    // Note that the results may differ if the lifter has been run.
    val cg = buildCallGraph(fs).filter: c =>
      val cond = defnSyms.contains(c.f1) && defnSyms.contains(c.f2)
      c.match
        case c: CallEdge.TailCall if c.call.explicitTailCall && !cond =>
          raise(ErrorReport(
            msg"This tail call exits the current scope and is not optimized." -> c.call.toLoc :: Nil))
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
  
  def getParamSyms(f: FunDefn) = f.params.flatMap:
    case ParamList(_, params, S(rest)) =>
      params.map(_.sym).appended(rest.sym)
    case p => p.params.map(_.sym)
  
  def paramsLen(f: FunDefn): Int = f.params.foldLeft(0): (acc, head) =>
    acc + (if head.restParam.isDefined then 1 + head.params.length
      else head.params.length)
  
  // Success:       This arg list was successfully transformed. The args may be blindly assigned to the
  //                parameters in order.
  // ForceSpread:   This arg list may be rewritten, but contains spread parameters for which must use a tuple
  //                to correctly extract the arguments correctly.
  private enum CallArgsResult:
    case Success(res: List[Result])
    case ForceSpread
  
  // Tries to rewrite an application of an arg list to a param list without needing to forcibly
  // unspread the arguments.
  private def rewriteArgsList(f: FunDefn, paramList: ParamList, args: List[Arg]): CallArgsResult =
    val (headArgs, restArgs) = paramList.restParam match
      case Some(value) => args.splitAt(paramList.params.length)
      case None => (args, Nil)
    
    var hasSpread = false
    // If any args have a spre
    val hd = for a <- headArgs yield a.spread match
      case Some(SpreadKind.Eager) =>
        hasSpread = true
        a.value
      case Some(SpreadKind.Lazy) => lastWords("Lazys pread in arguments")
      case _ => a.value
    if hasSpread then return CallArgsResult.ForceSpread
    
    if paramList.restParam.isDefined then
      val rest =
        restArgs match
          case Arg(S(SpreadKind.Eager), value) :: Nil => value
          case _ => Tuple(true, restArgs)
      CallArgsResult.Success(hd.appended(rest))
    else
      CallArgsResult.Success(hd)
    
  def optScc(scc: SccOfCalls, owner: Opt[InnerSymbol])(using accessInfo: (ScopeData, AccessMap)): (Opt[FunDefn], List[FunDefn]) =
    // sort the functions so the order is more predictable
    val funs = scc.funs.sortBy(f => f.dSym.uid)
    val fSyms = funs.map(_.dSym).toSet
    val funsMap = funs.map: f =>
        f.dSym -> f
      .toMap
    
    // remove calls which don't flow into this scc
    val calls = scc.calls.filter(c => fSyms.contains(c.f2)) 
    
    val nonTailCallsLs = calls.collect:
      case c: CallEdge.NormalCall => c.f2 -> c.call
    val nonTailCalls = nonTailCallsLs.toMap
    
    if nonTailCallsLs.sizeCompare(calls) === 0 then
      for f <- funs if f.tailRec do
        raise(WarningReport(msg"This function does not directly self-recurse, but is marked @tailrec." -> f.dSym.toLoc :: Nil))
      return (N, funs)
    
    if !nonTailCalls.isEmpty then
      for f <- funs if f.tailRec do
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
          for i <- 0 until maxParamLen yield VarSymbol(Tree.Ident("param" + i))
      .toList
    val paramSymsArr = ArrayBuffer.from(paramSyms)
    // Function -> param -> param symbol in the rewritten function
    val paramSymsMap: Map[TermSymbol, Map[VarSymbol, VarSymbol]] = 
      funs.map: f =>
        val flattenedSyms = f.params.flatMap(_.paramSyms)
        val mp = flattenedSyms.zipWithIndex.map:
            case (l, i) => l -> paramSymsArr(i)
          .toMap
        f.dSym -> mp
      .toMap
    
    val dSymIds = funs.map(_.dSym).zipWithIndex.toMap
    val dSymToDefn = funs.map(f => f.dSym -> f).toMap
    val bms =
      if funs.size === 1 then funs.head.sym
      else BlockMemberSymbol(funs.map(_.sym.nme).mkString("_"), Nil, true)
    val dSym =
      if funs.size === 1 then funs.head.dSym
      else TermSymbol(syntax.Fun, owner, Tree.Ident(bms.nme))
    val loopSym = LabelSymbol(N, "loopLabel")
    val curIdSym = VarSymbol(Tree.Ident("id"))
    
    class FunRewriter(f: FunDefn) extends BlockTransformerShallow(SymbolSubst.Id):
      val params = getParamSyms(f)
      val paramsSet = f.params.toSet
      val paramsIdxes = params.zipWithIndex.toMap
      
      // Certain variables must be re-defined in the tailrec loop
      // if they are captured by nested definitions or lambdas. Otherwise,
      // when they are mutated by a tailrec call, the nested definitions
      // would capture the mutated variable rather than the one defined
      // in the original call. See https://github.com/hkust-taco/mlscript/issues/415
      val copiedParams: Set[VarSymbol] = 
        // scopeData: A class that wraps a tree describing the scoping relation in the IR. Each node is
        //            an object that introduces a scope, which could be a scoped block, function, class, etc.
        //            A node's children represent that scope's nested scopes, functions, classes, etc.
        // accessMap: Maps scopes to the variables that they could access, either directly or by entering
        //            another scope. For functions, that would be the variables they could access.
        val (scopeData, accessMap) = accessInfo
        val node = scopeData.getNode(f)
        // Finds the immediate child functions/classes of the the function `f`.
        val (_, childDefNodes) = node.partitionTree2:
          case _: ScopedObject.Class => true
          case _: ScopedObject.Func => true
          case _ => false
        childDefNodes.iterator.map(_.obj)
          .collect:
            case r: ScopedObject.Referencable[?] => r.sym // Obtains the definition symbol of the nested class/function.
          .flatMap(s => accessMap(s).accessed) // All local variables that each nested class/function could access.
          .collect:
            case x: VarSymbol => x 
          .filter(params.toSet)
          .toSet
      
      val copiedParamSyms = copiedParams.map: x =>
          x -> VarSymbol(x.id)
        .toMap
      
      val subst = new SymbolSubst:
        override def mapVarSym(l: VarSymbol): VarSymbol =
          copiedParamSyms.getOrElse(
            l,
            paramsIdxes.get(l) match
              case Some(idx) => paramSymsArr(idx)
              case _ => l
          )
      val symRewriter = new BlockTransformer(subst)
      
      override def applyBlock(b: Block): Block = b match
        // Note: the args in `c` have already been rewritten to point to the symbols in `paramSyms`.
        case TailCallShape(calleeSym, c) => dSymIds.get(calleeSym) match
          case None => super.applyBlock(b)
          case Some(id) =>
            val callee = dSymToDefn(calleeSym)
            val calleeParamsMap = paramSymsMap(callee.dSym)
            // We require the call to be fully applied.
            if c.argss.size != callee.params.size then
              super.applyBlock(b)
            else
              // The code used to continute the loop.
              val cont =
                if scc.funs.size === 1 then Continue(loopSym)
                else Assign(curIdSym, Value.Lit(Tree.IntLit(dSymIds(calleeSym))), Continue(loopSym))
              // In some cases, we could have assignments like this:
              // param0 = whatever
              // param1 = <a result containing param0>
              // which means param1's value is incorrect.
              // We should thus assign the params to temporary symbols
              // if they are needed for a subsequent assignment.
              var assignedSyms: Map[VarSymbol, Lazy[TempSymbol]] = paramSyms.map: sym =>
                  sym -> Lazy(TempSymbol(N, sym.nme + "_tmp")) // Use `Lazy` to avoid generating useless symbols
                .toMap
              var requiredTmps: Set[(VarSymbol, TempSymbol)] = Set.empty
              
              // Rewrites references to mutated parameters to point to a temp variable instead, and
              // reports that the parameter's value must be assigned to that temp variable
              // before assigning to the parameters of this arg list.
              val paramRewriter = new BlockDataTransformer(SymbolSubst.Id):
                override def applyValue(v: Value)(k: Value => Block): Block = v match
                  // `assignedSyms` contains all of the param symbols that have been assigned to
                  // before the current assignment, and thus references to them must be rewritten
                  // to point to a temporary variable.
                  case Value.SimpleRef(l: VarSymbol) => assignedSyms.get(l) match
                    case S(v) =>
                      val tmpSym = v.force_!
                      // Adding this to `requiredTmps` will make sure we set the temporary variable
                      // to the current variable at the start of the rewritten call.
                      requiredTmps += (l, tmpSym)
                      k(tmpSym.asSimpleRef)
                    case _ => super.applyValue(v)(k)
                  case _ => super.applyValue(v)(k)
              
              val argListResults = callee.params.zip(c.argss).map:
                case (params, args) => (params, params.paramSyms.map(calleeParamsMap), args, rewriteArgsList(callee, params, args))
              
              // Prevent stupid assignments like `set a = a`
              val selfAssigns = argListResults.flatMap: (_, thisParamSyms, args, argsRes) =>
                argsRes match
                  case CallArgsResult.Success(res) => thisParamSyms.zip(res).collect:
                    case (sym1, Value.SimpleRef(sym2)) if sym1 === sym2 => sym1
                  case CallArgsResult.ForceSpread => List.empty
              assignedSyms --= selfAssigns
              
              
              // Algorithm: Apply the args from right to left, but have the resulting assignment order
              // be left to right.
              // 
              // When applying each arg, keep track of the parameters that must be assigned to be a
              // temporary variable. Also, remove each assigned parameter from `assignedSyms` after assigning
              // them, so that assignments coming before them will not mistakenly add the param syms from 
              // future assignments to `requiredTmps`.
              val assignments: Block = argListResults.foldRight(cont):
                case ((ogParamList, thisParamSyms, ogArgs, argRes), rest) =>
                  argRes match
                  case CallArgsResult.Success(argVals) =>
                    // Remove symbols from assignedSyms as we encounter them.
                    // Note that foldRight will call the function right to left
                    thisParamSyms.zip(argVals).foldRight[Block](rest): (v, acc) =>
                      val (sym, res) = v
                      assignedSyms -= sym
                      // Rewrite the result with symbols pointing to the temporary variables as described above.
                      // Note that we already rewrote the result with symbols pointing to the merged function parameters
                      // in `rewrite`. Also note that `paramRewriter` will add all encountered rewritten variables
                      // to `requiredTmps`.
                      val ret = paramRewriter.applyResult(res)(Assign(sym, _, acc)) match
                        case Assign(sym, Value.SimpleRef(sym1), rest) if sym === sym1 => rest // avoid useless assignments
                        case x => x
                      ret
                  case CallArgsResult.ForceSpread =>
                    // Forcibly spread the args in an array.
                    // Assume the lengths are correct
                    val paramList = ogParamList.params
                    val restParam = ogParamList.restParam
                    
                    val tupleSym = TempSymbol(N, "argList")
                    
                    // We can safely remove all of the symbols from this parameter list from `assignedSyms` at this stage,
                    // because the RHS of every parameter will be computed when spreading them in the tuple, which happens
                    // before any of the param symbols are assigned to.
                    assignedSyms --= thisParamSyms
                    paramRewriter.applyArgs(ogArgs): newArgs =>
                      val tupleRes = Tuple(false, newArgs)
                      
                      // Main args
                      def mainArgs(rest: List[Path]) = (0 until paramList.size).toList.foldRight(rest):
                        case (n, acc) => DynSelect(tupleSym.asSimpleRef, Value.Lit(Tree.IntLit(n)), true) :: acc
                      
                      // If the rest param exists, append a slice
                      val (initialBlk: (Block => Block), pathList: List[Path]) =
                        if restParam.isDefined then
                          val sliceResSym = TempSymbol(N, "sliceRes")
                          // runtime.Tuple.slice(tupleSym, paramList.length, 0)
                          val sliceRes = Call(
                            State.runtimeSymbol.asSimpleRef
                              .sel(Tree.Ident("Tuple"), State.tupleSymbol)
                              .sel(Tree.Ident("slice"), State.tupleSliceSymbol),
                            (tupleSym.asSimpleRef.asArg
                              :: Value.Lit(Tree.IntLit(paramList.length)).asArg
                              :: Value.Lit(Tree.IntLit(0)).asArg
                              :: Nil) ne_:: Nil
                          )(true, false, false)
                          val blk = blockBuilder
                            .assignScoped(tupleSym, tupleRes)
                            .assignScoped(sliceResSym, sliceRes)
                          (blk, mainArgs(sliceResSym.asSimpleRef :: Nil))
                        else
                          (blockBuilder.assignScoped(tupleSym, tupleRes), mainArgs(Nil))
                      end val
                      val paramAssignments = (thisParamSyms zip pathList).foldRight[Block](rest):
                        case ((sym, path), restBlk) => Assign(sym, path, restBlk)
                    
                      initialBlk.rest(paramAssignments)
              end assignments
              
              // Bind the tmps
              Scoped(
                requiredTmps.values.toSet,
                requiredTmps.toList.foldRight(assignments):
                  case ((v, l), acc) => Assign(l, v.asSimpleRef, acc))
        // Not a tail call
        case _ => super.applyBlock(b)
      
      def rewrite(b: Block): Block =
        // Rewrite the result with symbols pointing to the merged function parameters and possibly the copied parameters (see `copiedParams`).
        val blk = applyBlock(symRewriter.applyBlock(b))
        val withCopied = copiedParamSyms.toArray.sortBy(_._1.uid).foldRight(blk):
          case ((ogParam, copiedParam), accBlk) => Assign(copiedParam, paramSymsArr(paramsIdxes(ogParam)).asSimpleRef, accBlk)
        Scoped(copiedParamSyms.map(_._2).toSet, withCopied)
        
    val arms = funs.map: f =>
      Case.Lit(Tree.IntLit(dSymIds(f.dSym))) -> FunRewriter(f).rewrite(f.body)
    
    val switch = 
      if arms.length === 1 then arms.head._2
      else Match(curIdSym.asSimpleRef, arms, N, End())
    
    val loop = Label(loopSym, true, switch, End())
    
    val sel = owner match
      case Some(value) => Select(value.asThis, Tree.Ident(bms.nme))(S(dSym))
      case None => bms.asMemberRef(dSym)
    
    val rewrittenFuns =
      if funs.size === 1 then Nil
      else funs.map: f =>
        val paramArgs = getParamSyms(f).map(s => s.asSimpleRef.asArg)
        val args = 
          Value.Lit(Tree.IntLit(dSymIds(f.dSym))).asArg
            :: paramArgs
            ::: List.fill(maxParamLen - paramArgs.length)(Value.Lit(Tree.UnitLit(false)).asArg)
        val newBod = Return(
          Call(sel, args ne_:: Nil)(true, false, false),
        )
        FunDefn(f.owner, f.sym, f.dSym, f.params, newBod)(N, f.annotations)
    
    val params =
      val initial = paramSyms.map(Param.simple(_))
      if funs.length === 1 then initial
      else Param.simple(curIdSym) :: initial
    
    val loopDefn = FunDefn(
      owner, bms, dSym,
      PlainParamList(params) :: Nil,
      loop)(N, annotations = Nil) // Q: maybe should be Private?
    
    if funs.size === 1 then
      val f = funs.head
      if f.params.length > 1 then
        // When a function has multiple param lists, TailRecOpt flattens them into a single
        // param list for the internal loop. We need a wrapper function that preserves the
        // original multi-param-list interface and delegates to the flattened internal loop.
        val loopBms = BlockMemberSymbol(bms.nme + "$tailrec", Nil, true)
        val loopDSym = TermSymbol(syntax.Fun, owner, Tree.Ident(loopBms.nme))
        val internalLoopDefn = FunDefn(
          owner, loopBms, loopDSym,
          PlainParamList(params) :: Nil,
          loop)(N, annotations = Annot.Private :: Nil)
        val paramArgs = getParamSyms(f).map(s => s.asSimpleRef.asArg)
        val internalSel = owner match
          case Some(value) => Select(value.asThis, Tree.Ident(loopBms.nme))(S(loopDSym))
          case None => loopBms.asMemberRef(loopDSym)
        val wrapperBod = Return(
          Call(internalSel, paramArgs ne_:: Nil)(true, false, false),
        )
        val wrapperDefn = FunDefn(f.owner, f.sym, f.dSym, f.params, wrapperBod)(
          f.configOverride, annotations = f.annotations)
        (S(internalLoopDefn), wrapperDefn :: Nil)
      else
        (N, loopDefn :: Nil)
    else (S(loopDefn), rewrittenFuns)
  
  def optFunctions(fs: List[FunDefn], owner: Opt[InnerSymbol])(using (ScopeData, AccessMap)) =
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
        if f.tailRec then
          raise(ErrorReport(msg"Class methods may not yet be marked @tailrec." -> f.dSym.toLoc :: Nil))
      override def applyResult(r: Result): Unit = r match
        case c: Call if c.explicitTailCall =>
          raise(ErrorReport(msg"Calls from class methods cannot yet be marked @tailcall." -> c.toLoc :: Nil))
        case _ => super.applyResult(r)
  
  def optFunctionsFlat(fs: List[FunDefn], owner: Opt[InnerSymbol])(using (ScopeData, AccessMap)) =
    val (a, b) = optFunctions(fs, owner)
    a ::: b
    
  def optClasses(cs: List[ClsLikeDefn])(using (ScopeData, AccessMap)) = cs.map: c =>
    // Class methods cannot yet be optimized as they cannot yet be marked final.
    
    if c.k is syntax.Cls then
      reportClassesTailrec(c)
      val companion = c.companion.map: comp =>
        val cMtds = optFunctionsFlat(comp.methods, S(comp.isym))
        comp.copy(methods = cMtds)
      c.copy(companion = companion)(c.configOverride, c.annotations)
    else
      val mtds = optFunctionsFlat(c.methods, S(c.isym))
      val companion = c.companion.map: comp =>
        val cMtds = optFunctionsFlat(comp.methods, S(comp.isym))
        comp.copy(methods = cMtds)
      c.copy(methods = mtds, companion = companion)(c.configOverride, c.annotations)
  
  def transform(b: Block) =
    /* To avoid `x` being overridden in the following when the lifter is not run:
     * 
     * let lam
     * fun f(x) =
     *   set lam = () => x
     *   f(x + 1)
     * 
     * we need to do some analysis on what nested functions use what variables. We
     * re-use the analysis from the lifter to do this.
     */
    
    given (ScopeData, AccessMap) = 
      // IgnoredScoes can be an empty set, since that information is only relevant for lifting
      given IgnoredScopes = IgnoredScopes(S(Set.empty))
      val scopeData = ScopeData(b)
      val analyzer = new UsedVarAnalyzer(b, scopeData)
      (scopeData, analyzer.accessMapWithIgnored)
    
    val defns = b.gatherDefns()
    val (funs, clses) = defns.partitionMap:
      case f: FunDefn => L(f)
      case c: ClsLikeDefn => R(c)
      case _ => die // unreachable as floatOutDefns only floats out FunDefns and ClsLikeDefns
    // Filter out functions that have a @config annotation disabling tailRecOpt
    val (tailRecFuns, _) = funs.partition: f =>
      f.configOverride.forall(_.tailRecOpt)
    val (optFNew, optF) = optFunctions(tailRecFuns, N)
    val optC = optClasses(clses)
    
    val fMap = optF.map(f => f.dSym -> f).toMap
    // Scala needs this annotation to type check for some reason
    val cMap: Map[DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, ClsLikeDefn] =
      optC.map(c => c.isym -> c).toMap
    
    // replace them in place 
    val transformer = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case f: FunDefn => fMap.get(f.dSym) match
          case Some(value) => k(value)
          case None => k(f)
        
        case c: ClsLikeDefn => cMap.get(c.isym) match
          case Some(value) => k(value)
          case None => k(c)
        
        case _ => super.applyDefn(defn)(k)
    
    val result = Scoped(
      optFNew.map(_.sym).toSet,
      optFNew.foldLeft(transformer.applyBlock(b)):
        case (acc, f) => Define(f, acc))
    
    // Report @tailrec on functions that weren't processed by the optimization above,
    // e.g. nested functions or functions with @config(tailRecOpt: false).
    // Class/module methods are handled separately by optClasses and are skipped here.
    val tailRecFunSyms = tailRecFuns.map(_.dSym).toSet
    new BlockTraverser:
      override def applyFunDefn(fun: FunDefn): Unit =
        if fun.tailRec && !tailRecFunSyms.contains(fun.dSym) then
          raise(ErrorReport(
            msg"This @tailrec function was not processed by the tail-call optimizer." -> fun.dSym.toLoc :: Nil))
        super.applyFunDefn(fun)
      override def applyDefn(defn: Defn): Unit = defn match
        case _: ClsLikeDefn => ()
        case _ => super.applyDefn(defn)
    .applyBlock(result)
    
    result
