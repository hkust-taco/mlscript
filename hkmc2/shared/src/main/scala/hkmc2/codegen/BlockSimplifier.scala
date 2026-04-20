package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}
import scala.annotation.tailrec
import sourcecode.Line

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.State
import mlscript.utils.algorithms.partitionScc


/** `symbolsToPreserve` is the set of local symbols we want to leave alone;
  * typically, these will be top-level symbols that are being exported from a diff-test block;
  * we don't want to eliminate these. */
class BlockSimplifier(symbolsToPreserve: Set[Local])(using DebugPrinter, State, Config, TL):
  
  
  private var changed = true
  
  def registerChange = changed = true
  // * For debugging:
  // def registerChange(using line: Line) = { println(s"Change at line ${line.value}"); changed = true }
  
  def apply(prog: Program): Program =
    var res = prog
    while changed do
      changed = false
      res = new DeadCodeElim().apply(res)
      summon[Config].inlining.foreach: cfg =>
        res = new Inliner.Inliner(using cfg).applyProgram(res)
      // TODO: other simplifications, such as inlining
    res
  end apply
  
  
  class DeadCodeElim() extends BlockTransformer(SymbolSubst.Id):
    
    
    val usedLabels = MutSet.empty[LabelSymbol]
    val definedVars = MutSet.empty[Local]
    val localVars = MutSet.empty[Local]
    val usedVars = MutSet.empty[Local]
    var tailLabels = MutSet.empty[LabelSymbol]
    
    def apply(prog: Program): Program =
      
      new BlockTraverser:
        
        applyProgram(prog)
        
        override def applyDefn(defn: Defn): Unit =
          defn match
          case cls: ClsLikeDefn =>
            localVars ++= cls.privateFields
            cls.companion.foreach(localVars ++= _.privateFields)
          case _ =>
          super.applyDefn(defn)
        
        override def applyPath(p: Path): Unit =
          p match
            case Value.Ref(loc, _) =>
              usedVars += loc
            case _ =>
          super.applyPath(p)
        
        override def applyBlock(b: Block): Unit =
          b match
            case Define(defn, rst) =>
              definedVars += defn.sym
            case Scoped(syms, _) =>
              localVars ++= syms
            case Break(lbl) => usedLabels += lbl
            case Continue(lbl) => usedLabels += lbl
            case Assign(lhs, rhs, rst) =>
              definedVars += lhs
            case _ =>
          super.applyBlock(b)
      
      applyProgram(prog)
    
    // Evaluate `thunk` with a new tail label set. This is used for evaluating any sub blocks that is not in the tail position.
    // For example, the match arms within a `Match` node are not in the tail position unless the rest block is `End`.
    // When evaluating the match arms, the tail labels should not be considered to be at tail.
    // The tail label set is restored after `thunk` completes.
    inline def nestLabelCtx[T](inline thunk: => T): T =
      val oldTailLabels = tailLabels
      tailLabels = MutSet.empty
      val result = thunk
      tailLabels = oldTailLabels
      result
    
    // Add the new label to the tail label set during the execution of `thunk`.
    inline def withTailLabel[T](newLabel: LabelSymbol)(inline thunk: => T): T =
      assert(!tailLabels.contains(newLabel))
      tailLabels += newLabel
      val result = thunk
      tailLabels -= newLabel
      result
    
    // * Cached analysis to find which labels are the targets of `break`s in a given block
    object BrokenLabels extends CachedAnalysis[Block, Set[LabelSymbol]]:
      
      def analyzeUncached(block: Block): Set[LabelSymbol] = block match
        case Break(lbl) => Set.single(lbl)
        case _ => block.subBlocks.iterator.flatMap(analyze).toSet
      
    end BrokenLabels
    
    
    // * Cached analysis to find whether a block is abortive
    // * (i.e. always throws, returns, breaks, continues, or is unreachable)
    object AbortiveAnalysis extends CachedAnalysis[Block, Bool]:
      
      def analyzeUncached(block: Block): Bool = block match
        case Scoped(syms, body) =>
          body.analyze
        case Match(scrut, arms, dflt, rest) =>
          rest.analyze || arms.forall(_._2.analyze) && dflt.exists(_.analyze)
        case Begin(sub, rest) =>
          sub.analyze || rest.analyze
        case Define(defn, rest) =>
          // TODO: we could also analyse the effects of the extends clauses and companion module ctor
          rest.analyze
        case x: (Assign | AssignField | AssignDynField) =>
          x.rest.analyze
        case TryBlock(sub, finallyDo, rest) =>
          sub.analyze || rest.analyze
        case Label(lbl, loop, bod, rst) =>
          bod.analyze
            && !BrokenLabels.analyze(bod).contains(lbl) // if `bod` breaks to `lbl`, then we must consider `rst`
            || rst.analyze
        case _: Throw | Return(_, false) | _: Unreachable | _: Continue | _: Break => true
        case Return(_, true) => false
        case _: End => false
        case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
          body.analyze || rest.analyze
        
    end AbortiveAnalysis
    
    
    val removedLocals: MutSet[Local] = MutSet.empty
    
    
    override def applyValue(v: Value)(k: Value => Block) = v match
      // * Replace with `undefined` those references to local variables that are never assigned
      case Value.Ref(loc, N) if localVars.contains(loc) && !definedVars.contains(loc) =>
        registerChange
        if !symbolsToPreserve(loc) then removedLocals += loc
        k(Value.Lit(syntax.Tree.UnitLit(false)))
      case _ => super.applyValue(v)(k)
    
    override def applyBlock(b: Block): Block = b match
      
      // * Discard assignments to local variables that are never read (and are not preserved)
      case Assign(lhs, rhs, rst) if localVars(lhs) && !usedVars(lhs) && !symbolsToPreserve(lhs) =>
        registerChange
        removedLocals += lhs
        applyResult(rhs)(r => Assign.discard(r, applyBlock(rst)))
      
      // * Remove local pure definitions that are never read (and are not preserved)
      case Define(defn, rest) =>
        if !defn.isPure
        || !localVars(defn.sym)
        || usedVars(defn.sym)
        || symbolsToPreserve(defn.sym)
        then super.applyBlock(b)
        else
          registerChange
          removedLocals += defn.sym
          applyBlock(rest)
        
      // * Simplify labelled blocks
      case Label(lbl, loop, bod, rst) =>
        if !BrokenLabels.analyze(bod).contains(lbl) && AbortiveAnalysis.analyze(bod) && !rst.isInstanceOf[Unreachable] then
          registerChange
          val unr = Unreachable("Rest of abortive labelled block")
          if usedLabels.contains(lbl)
          then Label(lbl, loop, nestLabelCtx(applyBlock(bod)), unr)
          else Begin(nestLabelCtx(applyBlock(bod)), unr)
        else
          if usedLabels.contains(lbl) then
            def computeBod =
              withTailLabel(lbl):
                applyBlock(bod)
            val lbl2 = lbl.subst
            val bod2 = if rst.isEmpty && !loop then computeBod else nestLabelCtx(computeBod)
            val rst2 = applySubBlock(rst)
            if (lbl2 is lbl) && (bod2 is bod) && (rst2 is rst) then b else Label(lbl2, loop, bod2, rst2)
          else
            registerChange
            Begin(nestLabelCtx(applyBlock(bod)), applyBlock(rst))
      
      // * Remove useless break
      case Break(label) if tailLabels.contains(label) =>
        tl.log(s"Break ${label} is eliminated: current tail label list is ${tailLabels}")
        registerChange
        End()
      
      case x => super.applyBlock(x)
    
    
    // FIXME: refactor transformers so this is not so error-prone (adding this case to `applyBlock` doesn't work)
    override def applyScopedBlock(b: Block): Block = b match
      // * Delete removed local variables from Scoped blocks
      case Scoped(syms, body) =>
        val body2 = applyBlock(body)
        // println(s">> $body2 ${body is body2}")
        // println(s">> $body2 ${changed}")
        if changed then
        // if changed || (body isnt body2) then
          val syms2 = syms.filterNot(removedLocals)
          // println(s">> $syms $syms2 ${removedLocals}")
          if syms2.size === syms.size && (body2 is body) then b
          else Scoped(syms2, body2)
        else b
      case _ => super.applyScopedBlock(b)
    
    override def applyFunBodyLikeBlock(b: Block): Block =
      nestLabelCtx:
        super.applyFunBodyLikeBlock(b)
    
    override def applySubBlockNonTail(b: Block): Block =
      nestLabelCtx:
        super.applySubBlockNonTail(b)
    
  end DeadCodeElim
  
  
  object Inliner:
    object Inliner:

      // Reference to a function body can occur as a.f or f, this handles both cases.
      object TermSymbolPath:
        def unapply(p: Path) = p match
          case Value.Ref(l, S(ts: TermSymbol)) => S(ts)
          case s: Select => s.symbol match
            case S(ts: TermSymbol) => S(ts)
            case _ => N
          case _ => N
      
      def matchArgs(args: List[Arg], params: ParamList): Option[List[(VarSymbol, Result)]] =
        if args.exists(_.spread.isDefined) then
          // we require a precise match when any arg is a spread arg
          if params.restParam.isEmpty then return N
          if args.exists(_.spread.exists(!_.isEager)) then return N
          if args.size =/= params.params.size then return N
          val pairs = args.zip(params.params.iterator.map((_, false)) ++ params.restParam.map((_, true)))
          if pairs.exists((arg, param) => arg.spread.isDefined =/= param._2) then return N
          S(pairs.map((arg, param) => (param._1.sym, arg.value)))
        else
          // otherwise arg list is a simple list, and
          // we can perform manual array instantiation if params contain a spread param
          if params.restParam.isEmpty then
            if args.size =/= params.params.size then return N
            S(args.zip(params.params).map((arg, param) => (param.sym, arg.value)))
          else
            if args.size < params.params.size then return N
            val (fixedArgs, restArgs) = args.splitAt(params.params.size)
            S(fixedArgs.zip(params.params).map((arg, param) => (param.sym, arg.value)) ++
              List((params.restParam.get.sym, Tuple(true, restArgs))))
    
    import Inliner.*
    
    object InlinerAnalyzer:
      case class InlinerFunInfo(
        defn: FunDefn,
        isMethod: Bool,
        private[InlinerAnalyzer] var useCount: Int,
        private[InlinerAnalyzer] var hasNakedRef: Bool,
        private[InlinerAnalyzer] var isLoopBreaker: Bool,
      ):
        def isPrivate = !symbolsToPreserve.contains(defn.sym)
        
        // Whether this function can be inlined without causing any code duplication,
        // i.e. the original definition can be removed and there is only one usage.
        def canBeInlineEliminated =
          isPrivate && !isMethod && useCount <= 1 && !hasNakedRef && !isLoopBreaker
          // false
        
        def shouldBeInlined(newBlk: Block)(using Config.Inliner): Bool =
          if isLoopBreaker then return false
          // method requires the capturing of `this`, which is not supported currently.
          if isMethod then return false
          val threshold = summon[Config.Inliner].inlineThreshold
          newBlk.size <= threshold || canBeInlineEliminated
        
      type InlinerMap = Map[TermSymbol, InlinerFunInfo]
      
      case class FunLikeContext(
        curFunSym: Opt[TermSymbol],
      )
      
      class Traverser extends BlockTraverser:
        var map: InlinerMap = Map.empty
        val useCnt = MutMap.WithDefault(MutMap.empty[TermSymbol, Int], _ => 0)
        val usages = MutMap.WithDefault(MutMap.empty[TermSymbol, List[(Option[TermSymbol], Call)]], _ => Nil)
        val hasNakedRef = MutMap.WithDefault(MutMap.empty[TermSymbol, Bool], _ => false)
        var contextList: List[FunLikeContext] = FunLikeContext(N) :: Nil
        
        def currentContext = contextList.head
        
        def currentFunSym = currentContext.curFunSym
        
        def nested(ts: Option[TermSymbol])(thunk: => Unit) =
          contextList = FunLikeContext(ts) :: contextList
          thunk
          val res = contextList.head
          contextList = contextList.tail
          res
        
        def addFunctionAndApplyBody(f: FunDefn, isMethod: Bool) =
          val r = nested(S(f.dSym)):
            applyBlock(f.body)
          map = map + (f.dSym -> InlinerFunInfo(f, isMethod, 0, false, false))
        
        override def applyDefn(defn: Defn): Unit = defn match
          case f: FunDefn =>
            addFunctionAndApplyBody(f, false)
          case c: ClsLikeDefn =>
            c.parentPath.foreach(applyPath)
            c.methods.foreach: f =>
              addFunctionAndApplyBody(f, true)
            // Note: no tracking, since `Instantiate` will not be inlined and won't cause cycles.
            nested(N):
              applySubBlock(c.preCtor)
              applySubBlock(c.ctor)
            c.companion.foreach: m =>
              m.methods.foreach: f =>
                addFunctionAndApplyBody(f, true)
              // This inherits the previous context as the module ctor is run with the constructor.
              applySubBlock(m.ctor)
          case _ => super.applyDefn(defn)
        
        override def applyResult(r: Result): Unit = r match
          case c @ Call(TermSymbolPath(ts), args) =>
            useCnt(ts) += 1
            usages(ts) ::= (currentFunSym, c)
            args.foreach(applyArg)
          case _ => super.applyResult(r)
        
        override def applySymbol(sym: Symbol): Unit =
          sym.asTrm.foreach: ts =>
            useCnt(ts) += 1
            hasNakedRef(ts) = true
        
        def analyze(blk: Block): InlinerMap =
          applyBlock(blk)
          map.foreach: (sym, info) =>
            info.useCount = useCnt(sym)
            info.hasNakedRef = info.hasNakedRef || hasNakedRef(sym)
          val edges: Buffer[(TermSymbol, TermSymbol)] = Buffer.empty
          usages.foreach: (sym, calls) =>
            calls.foreach: (caller, call) =>
              if map.contains(sym) then
                map(sym).hasNakedRef = map(sym).hasNakedRef ||
                  map(sym).defn.params.sizeCompare(1) =/= 0 || matchArgs(call.args, map(sym).defn.params.head).isEmpty
                caller.foreach: caller =>
                  edges.append((caller, sym))
          
          @tailrec
          def assignLoopBreakers(): Unit =
            val sccs = partitionScc(edges.filterNot((from, to) => map(to).isLoopBreaker), map.keys)
            if sccs.forall(_.sizeIs == 1) then return
            sccs.foreach: sccComp =>
              if sccComp.sizeIs > 1 then
                // TODO: Score computation
                map(sccComp.minBy(_.uid)).isLoopBreaker = true
            assignLoopBreakers()
          edges.foreach: (from, to) =>
            if from === to then
              map(from).isLoopBreaker = true
          assignLoopBreakers()
          map
      
      def walk(blk: Block): InlinerMap = Traverser().analyze(blk)
    
    import InlinerAnalyzer.InlinerMap
    
    
    object InlinerReplacer:
      
      class Copier(resSym: Symbol, existingMapping: Map[Symbol, Symbol])(using State):
        val lblSym = LabelSymbol(N, "inlinedLbl")
        
        object Copier extends SymbolRefresher(existingMapping):
          var currentlyNested = false
          
          override def applyFunBodyLikeBlock(b: Block): Block =
            val saved = currentlyNested
            currentlyNested = true
            val res = super.applyFunBodyLikeBlock(b)
            currentlyNested = saved
            res
          
          override def applyBlock(b: Block): Block = b match
            case Return(res, false) if !currentlyNested =>
              applyResult(res): r2 =>
                Assign(resSym, r2, Break(lblSym))
            case _ => super.applyBlock(b)
        
        def applyBlock(blk: Block) =
          Label(lblSym, false, Copier.applyBlock(blk), _)
      
      class Transformer(m: InlinerMap)(using Config.Inliner, State) extends BlockTransformer(SymbolSubst()):
        
        // The call graph may be cyclic, in which case we break the infinite loop using this map by
        // assuring that the block corresponding to a term symbol may only be transformed once.
        // This map also allows the function block to be optimized on first use before its declaration.
        // Key not in map -> not yet analyzed
        // Key in map but value is None -> the optimized body is being computed
        // Key in map with value -> the function is optimized
        val newFunctionBody = MutMap.empty[TermSymbol, Option[Block]]
        
        override def applyMainBlock(main: Block): Block =
          super.applyMainBlock(main).flattened
        
        override def applyBlock(blk: Block) = blk match
          case Define(defn: FunDefn, rest) if m(defn.dSym).canBeInlineEliminated =>
            tl.log(s"Inline elimination: ${defn.dSym}")
            registerChange
            applyBlock(rest)
          case _ => super.applyBlock(blk)
        
        override def applyFunDefn(fun: FunDefn): FunDefn =
          newFunctionBody.get(fun.dSym) match
            case N =>
              newFunctionBody(fun.dSym) = N
              val newBdy = applyBlock(fun.body)
              newFunctionBody(fun.dSym) = S(newBdy)
              if newBdy is fun.body then fun else
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, newBdy)(fun.forceTailRec, fun.configOverride, fun.visibility)
            case S(N) =>
              // The expansion of the function body itself reaches its own definition, which is impossible
              lastWords("Function body contains its own definition.")
            case S(S(blk)) =>
              if blk is fun.body then fun else
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, blk)(fun.forceTailRec, fun.configOverride, fun.visibility)
        
        override def applyResult(r: Result)(k: Result => Block): Block = r match
          case Call(TermSymbolPath(ts), args) if m.contains(ts) =>
            newFunctionBody.get(ts)
            .getOrElse:
              newFunctionBody(ts) = N
              val newBdy = applyBlock(m(ts).defn.body)
              newFunctionBody(ts) = S(newBdy)
              S(newBdy)
            .fold(super.applyResult(r)(k)): blk =>
              val info = m(ts)
              if !info.shouldBeInlined(blk) || info.defn.params.size =/= 1 then
                super.applyResult(r)(k)
              else
                val matchedArgs = matchArgs(args, info.defn.params.head)
                matchedArgs match
                case N =>
                  super.applyResult(r)(k)
                case S(matchedArgs) =>
                  registerChange
                  tl.log(s"Inline call for ${ts}, with args ${args}")
                  def go(acc: Block => Block, args: List[(VarSymbol, Result)], mapping: Map[Symbol, Symbol]): Block =
                    args match
                    case Nil =>
                      val resSym = TempSymbol(N, "inlinedVal")
                      val copier = Copier(resSym, mapping)
                      val newBlk = copier.applyBlock(blk)
                      acc(Scoped(Set.single(resSym), newBlk(k(Value.Ref(resSym)))))
                    case (sym, value) :: argRest =>
                      val newSym = VarSymbol(sym.id)
                      go(acc.assignScoped(newSym, value), argRest, mapping + (sym -> newSym))
                  go(blockBuilder, matchedArgs, Map.empty)
          case _ => super.applyResult(r)(k)
      
      def replace(m: InlinerMap, prog: Program)(using Config.Inliner, State): Program =
        Transformer(m).applyProgram(prog)
    
    class Inliner(using Config.Inliner, State):
      def applyProgram(prog: Program): Program =
        val m = InlinerAnalyzer.walk(prog.main)
        InlinerReplacer.replace(m, prog)
  end Inliner
  
  
end BlockSimplifier


