package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}
import scala.annotation.tailrec
import sourcecode.{Line, FileName}

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.{State, Ctx, ctx}
import mlscript.utils.algorithms.partitionScc
import java.util.IdentityHashMap
import hkmc2.syntax.Literal
import hkmc2.{codegen => argss}


/** `symbolsToPreserve` is the set of local symbols we want to leave alone;
  * typically, these will be top-level symbols that are being exported from a diff-test block;
  * we don't want to eliminate these. */
class BlockSimplifier
    (symbolsToPreserve: Set[Local], tl: TL, printer: Program => Str)
    (using DebugPrinter, State, Config, Raise, Ctx):
  import tl.*
  
  
  val deadBranchRemoval = config.deadBranchRemoval
  
  val MaxIterations = 10
  
  
  def apply(prog: Program): Program =
    
    var res = prog
    def printRes = printer(res)
    var changed = true
    var iteration = 0
    
    while changed do
      changed = false
      iteration += 1
      
      if iteration > MaxIterations then
        log(s"⬤ Reached maximum number of iterations ($MaxIterations), stopping simplifications")
        return res
      
      log(s"⬤ Simplif. iter. $iteration")
      
      val dce = new DeadCodeElim()
      res = dce.apply(res)
      changed ||= dce.changed
      if dce.changed then log("▶ DCE:\n" + printRes)
      
      val vp = new DataFlowAnalysis(LocalVars.analyze(res.main))
      res = vp.apply(res)
      changed ||= vp.changed
      if vp.changed then log("▶ VP:\n" + printRes)
      
      summon[Config].inlining.foreach: cfg =>
        val inl = new Inliner(using cfg)
        res = inl.apply(res)
        changed ||= inl.changed
        if inl.changed then log("▶ INL:\n" + printRes)
      
      // TODO: other simplifications, such as partial evaluation?
      
    end while
    
    res
  end apply
  
  
  trait Helper:
    
    var changed = false
    
    def registerChange(dbg: => Str)(using Line) =
      log(s"!! Change triggered { ${dbg} }")
      // * For debugging:
      // log(s"!! Change triggered { ${dbg} } at ${summon[FileName].value}:${summon[Line].value}")
      changed = true
    
  end Helper
  
  
  type LocalVar = LocalVarSymbol
  
  object LocalVars extends CachedAnalysis[Block, Set[LocalVar]]:
    
    def analyzeUncached(block: Block): Set[LocalVar] = block match
      case Scoped(syms, rest) =>
        rest.analyze ++ syms.iterator.collect { case v: LocalVar => v }
      case _ => block.subBlocks.iterator.flatMap(analyze).toSet
    
  end LocalVars
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  /** A simple pass to eliminate the most obvious kind of dead code;
    * hopefully allows more expensive passes such as DataFlowAnalysis to do less work. */
  class DeadCodeElim() extends BlockTransformer(SymbolSubst.Id), Helper:
    
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
        
    end AbortiveAnalysis
    
    
    val removedLocals: MutSet[Local] = MutSet.empty
    
    
    override def applyValue(v: Value)(k: Value => Block) = v match
      // * Replace with `undefined` those references to local variables that are never assigned
      case Value.Ref(loc, N) if localVars.contains(loc) && !definedVars.contains(loc) =>
        registerChange(s"${loc.showDbg} is never assigned; replacing read with undefined")
        if !symbolsToPreserve(loc) then removedLocals += loc
        k(Value.Lit(syntax.Tree.UnitLit(false)))
      case _ => super.applyValue(v)(k)
    
    override def applyBlock(b: Block): Block = b match
      
      // * Discard assignments to local variables that are never read (and are not preserved)
      case Assign(lhs, rhs, rst) if localVars(lhs) && !usedVars(lhs) && !symbolsToPreserve(lhs) =>
        registerChange(s"rm ${lhs.showDbg} = ${rhs.showDbg}")
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
          registerChange(s"rm unused pure defn ${defn.sym.showDbg}")
          removedLocals += defn.sym
          applyBlock(rest)
        
      // * Simplify labelled blocks
      case Label(lbl, loop, bod, rst) =>
        if !BrokenLabels.analyze(bod).contains(lbl) && AbortiveAnalysis.analyze(bod) && !rst.isInstanceOf[Unreachable] then
          registerChange(s"label ${lbl.showDbg} body is abortive; rest is unreachable")
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
            registerChange(s"rm unused label ${lbl.showDbg}")
            Begin(nestLabelCtx(applyBlock(bod)), applyBlock(rst))
      
      // * Remove useless break
      case Break(label) if tailLabels.contains(label) =>
        log(s"Break ${label} is eliminated: current tail label list is ${tailLabels}")
        registerChange(s"rm tail-position break ${label.showDbg}")
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
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  /** Basic intraprocedural flow-sensitive analysis to figure out which assignments may flow into which variables,
    * at each point of the program.
    * For loops, it is enough to pass through the loop body once without transforming it ("dry run")
    * to get the data flow information from loop-back edges, and then to actually transform the loop.
    * When in dry-run mode, nested loops are also traversed in dry-run mode,
    * so overall each Block is traversed at most twice.
    * We keep track of a tree of assignments where, if the RHS was a local variable, we also store its analysis value
    * that was in effect at this point, which allows us to eliminate useless transitive assignments.
    * We keep track of variables going out of scope to avoid using them afterwards. */
  class DataFlowAnalysis(localVars: Set[LocalVar]) extends BlockTransformer(SymbolSubst.Id), Helper:
    
    
    val capturedVars = MutSet.empty[LocalVar]
    // ^ TODO: technically, all we need to prevent is changes to `nonLocallyAssignedVars`,
    //    so we should compute that instead in the future.
    //    Note that the capturing definitions won't see the assignments of the captured variable anyway
    //    because that variable will be treated as unknown, since nested definitions start from an empty environment.
    
    val unstableRefs = MutSet.empty[Local]
    // ^ We currently represent private fields using plain TermSymbol references,
    //    so these have to be special-cased as 'unstable'.
    //    TODO: represent them as fields, as they should be!
    //    TODO: then, the symbol type in `Assign` should be tightened to `LocalVar`
    
    
    def apply(prog: Program): Program =
      
      var cur = prog
      
      // * Collect captured variables
      new BlockTraverser:
        applyProgram(prog)
        
        override def applyDefn(defn: Defn): Unit =
          defn match
          case _: ClsLikeDefn | _: FunDefn =>
            capturedVars ++= defn.freeVars.iterator.collect { case v: LocalVar => v }
          case _ =>
          super.applyDefn(defn)
        
        // This override can go once we get rid of `unstableRefs`
        override def applyBlock(b: Block): Unit =
          b match
          case Assign(_: LocalVar, _, _) =>
          case Assign(lhs, _, _) =>
            unstableRefs += lhs
          case _ =>
          super.applyBlock(b)

        override def applyLam(lam: Lambda): Unit =
          capturedVars ++= lam.freeVars.iterator.collect { case v: LocalVar => v }
          super.applyLam(lam)
        
      end new
      
      log(s"Captured variables: ${capturedVars}")
      
      cur = applyProgram(prog)
      
      // * [Future: dead assignment removal]
      // * Technically, if nothing in the program changed, we could remove dead assignments using a simple flag.
      /* 
      if !changed then cur =
        (new BlockTransformer(SymbolSubst.Id):
          
          override def applyBlock(b: Block): Block =
            b match
            case ass @ Assign(lhs: LocalVar, rhs, rst)
            if localVars(lhs) && !capturedVars(lhs) && !symbolsToPreserve(lhs) && !liveAssignments.containsKey(ass)
            =>
              import scala.jdk.CollectionConverters._
              log(s"Live assignments: ${liveAssignments.keySet.asScala.toList.sortBy(_.toString)
                  .map(a => a.showDbg + System.identityHashCode(a))
                }")
              registerChange(s"rm ass ${lhs.showDbg} = ${rhs.showDbg}")
              registerChange(s"rm id ${System.identityHashCode(this)}")
              Assign.discard(rhs, applyBlock(rst))
            case _ => super.applyBlock(b)
          
        ).applyProgram(cur)
      */
      
      cur
      
    end apply
    
    
    enum AssignInfo:
      case Unknown
      case Uninitialized
      case Assigned(asst: Assign, varAsst: Opt[Value.Ref -> AssignInfo])
      case Merge(asst1: AssignInfo, asst2: AssignInfo)
      
      override def toString: String = this match
        case Unknown => "?"
        case Uninitialized => "∅"
        case Assigned(asst, varAsst) => s"${asst.rhs}${varAsst.fold("")("‹"+_+"›")}"
        case Merge(a1, a2) => s"{${a1.toString} | ${a2.toString}}"
      
      def merge(that: AssignInfo): AssignInfo =
        if this is that then this
        else that match
          case Unknown => that
          case Uninitialized => this
          // case Merge(l, r) => Merge(merge(this, l), r)
          case _: Assigned | _: Merge =>
            this match
              case Unknown => this
              case Uninitialized => that
              case _: Assigned | _: Merge => Merge(this, that)
      
    import AssignInfo.*
    
    
    type AssignedResults = Map[LocalVar, AssignInfo]
    
    val emptyAssignedResults: AssignedResults = Map.empty.withDefaultValue(Unknown)
    
    def impossible: AssignedResults =
      assignedResults.view.mapValues(_ => Uninitialized).toMap.withDefaultValue(Unknown)
    inline def makeImpossibleAfter[R](inline code: => R) =
      val res = code
      assignedResults = impossible
      res
    
    // *** ASSUMPTION (should be an invariant of the IR): only LocalVar symbols can be Assign'ed ***
    var assignedResults: AssignedResults = emptyAssignedResults
    var inDryRun = false // for traversing loop bodies once before actually transforming the program
    
    def withFreshAssignedResults[T](thunk: => T): T =
      val oldAssignedResults = assignedResults
      assignedResults = emptyAssignedResults
      val res = thunk
      assignedResults = oldAssignedResults
      res
    
    val atLabelBegin: MutMap[LabelSymbol, AssignedResults] = MutMap.empty.withDefaultValue(emptyAssignedResults)
    val atLabelEnd: MutMap[LabelSymbol, AssignedResults] = MutMap.empty.withDefaultValue(emptyAssignedResults)
    
    // * Careful: can't use `mergeMap` because we need to retain values defined in only one of the maps,
    // * merging them with `Unknown` (instead of just dropping them).
    def merge(ar1: AssignedResults, ar2: AssignedResults): AssignedResults =
      ar1.iterator
        .map: (k, v) =>
          k -> v.merge(ar2(k))
        .++(ar2.iterator.filterNot(ar1 contains _._1).map: (k, v) =>
          k -> ar1(k).merge(v)
        )
        .toMap
        .withDefaultValue(Unknown)
    
    
    // * [Future: dead assignment removal]
    // val liveAssignments: IdentityHashMap[Block, Unit] = new IdentityHashMap()
    
    
    override def applyDefn(defn: Defn)(k: Defn => Block): Block =
      defn match
      case _: ValDefn => super.applyDefn(defn)(k)
      case defn: (FunDefn | ClsLikeDefn) =>
        if inDryRun then k(defn)
        else
          val oldAssignedResults = assignedResults
          assignedResults = emptyAssignedResults
          super.applyDefn(defn): res =>
            assignedResults = oldAssignedResults
            k(res)
    
    // * Lambda bodies are function boundaries: `makeImpossibleAfter` on a Return inside a lambda
    // * must not leak out and corrupt the outer `assignedResults`.
    override def applyLam(lam: Lambda): Lambda =
      val oldAssignedResults = assignedResults
      assignedResults = emptyAssignedResults
      val res = super.applyLam(lam)
      assignedResults = oldAssignedResults
      res
    
    override def applyBlock(b: Block): Block =
    // trace[Block](s"Applying block: ${b.abbreviate} with map: ${assignedResults}", res => s"|= ${assignedResults}"):
      b match
        
      case ass @ Assign(lhs: LocalVar, rhs, rst) if !capturedVars(lhs) =>
        // log(s"Propagating ${lhs} := ${rhs} (${assignedResults.get(lhs)})")
        
        assignedResults += lhs -> Assigned(ass, rhs.match
          case r @ Value.Ref(sym: LocalVar, N) =>
            if capturedVars(sym) then N
            else
              val rhs2 = assignedResults(sym)
              S(r -> rhs2)
          case r @ Value.Ref(sym, _) if unstableRefs(sym) =>
            N
          case r @ Value.Ref(sym, _) =>
            S(r -> Unknown)
          case _ => N
        )
        super.applyBlock(b)
        
      case Assign(lhs, rhs, rst) =>
        // log(s"Not propagating ${lhs} := ${rhs}")
        
        super.applyBlock(b)
        
      case Label(label, loop, body, rest) =>
        
        // TODO: fix the rest of the compiler so this invariant actually holds
        // assert(!atLabelBegin.contains(label) && !atLabelEnd.contains(label))
        
        // * Loops always go through a dry run, but crucially,
        // * when in dry-run mode, loops do NOT go through normal processing,
        // * so that we only go through the whole program at most twice
        // * (not exponentially many times).
        if loop then
          atLabelBegin.put(label, assignedResults)
          // * Would seem to make sense to make the below `impossible`, but it doesn't work,
          // * even if we add `atLabelEnd.put(label, merge(atLabelEnd(label), assignedResults))`
          // * after the `applyBlock` call. Not entirely sure why.
          atLabelEnd.put(label, emptyAssignedResults)
          val oldDryRun = inDryRun
          inDryRun = true
          applyBlock(body)
          inDryRun = oldDryRun
          assignedResults = merge(assignedResults, atLabelBegin(label))
        if !loop || !inDryRun then
          val newBody = applyBlock(body)
          assignedResults = merge(assignedResults, atLabelEnd(label))
          val newRest = applySubBlock(rest)
          if (newBody is body) && (newRest is rest) then b
          else Label(label, loop, newBody, newRest)
        else
          // During dry run, still need to traverse `rest` to discover
          // assignments and continues that may affect outer loop analysis.
          applyBlock(rest)
          b
          
      case Continue(label) =>
        // log(s"Continue to ${label} with map: ${assignedResults}")
        // log(s"  atLabelBegin: ${atLabelBegin(label)}")
        atLabelBegin.put(label, merge(assignedResults, atLabelBegin(label)))
        makeImpossibleAfter:
          super.applyBlock(b)
        
      case Break(label) =>
        // TODO: this is probably only needed when `!inDryRun`?
        atLabelEnd.put(label, merge(assignedResults, atLabelEnd(label)))
        makeImpossibleAfter:
          super.applyBlock(b)
        
      case TryBlock(sub, finallyDo, rest) =>
        val sub2 = applyBlock(sub)
        val finallyDo2 =
          // * This block might be executed from an unknown point in the previous block,
          // * so we have to be conservative and not propagate any information.
          assignedResults = emptyAssignedResults
          applyBlock(finallyDo)
        val rest2 = applySubBlock(rest)
        if (sub2 is sub) && (finallyDo2 is finallyDo) && (rest2 is rest) then b
        else TryBlock(sub2, finallyDo2, rest2)
        
      case _: Return | _: Throw | _: Unreachable =>
        makeImpossibleAfter:
          super.applyBlock(b)
        
      case Match(scrut, arms, dflt, rest) =>
        
        applyPath(scrut): scrut2 =>
          
          // * TODO: Support Tup and Field shapes; ModuleOrObjectSymbol
          // * TODO: Support class inheritance reasoning (using a tree of hierarchical shapes)
          // type Shape = Literal | ClassSymbol | ModuleOrObjectSymbol
          type Shape = Literal | ClassLikeSymbol
          var gaveUp = false
          def giveUp =
            gaveUp = true
            Set.empty[Shape]
          def getShapesA(a: AssignInfo): Set[Shape] =
          // trace[Set[Shape]](s"Getting shapes for assignment ${a}", r => s"= ${r}"):
            a match
            case Unknown => giveUp
            case Uninitialized => Set.empty
            case Merge(a1, a2) => getShapesA(a1) | getShapesA(a2)
            case Assigned(asst, varAsst) =>
              varAsst match
              case S(Value.Ref(r, S(sym: ModuleOrObjectSymbol)) -> _) =>
                Set.single(sym)
              case S(_ -> ass) =>
                getShapesA(ass)
              case N =>
                asst.rhs match
                case p: Path => getShapes(p)
                case Call(path, args) =>
                  path.targetSymbol match
                  case S(tsym: TermSymbol) =>
                    tsym.owner match
                    case S(sym: ClassSymbol) =>
                      sym.defn match
                      case S(cls: ClassLikeDef)
                        if cls.auxParams.isEmpty
                        => Set.single(sym)
                      case _ => giveUp
                    case _ => giveUp
                  case _ => giveUp
                case Instantiate(mut, cls, args) =>
                  cls.targetSymbol match
                  case S(sym: ClassSymbol) =>
                    sym.defn match
                    case S(cls: ClassLikeDef)
                      // if the instantiation call is saturated
                      if cls.auxParams.isEmpty || cls.paramsOpt.isEmpty && cls.auxParams.sizeCompare(1) <= 0
                      => Set.single(sym)
                    case _ => giveUp
                  case _ => giveUp
                case _ => giveUp
          def getShapes(p: Path): Set[Shape] =
            if gaveUp then Set.empty
            else
              p match
              case Value.Ref(r: LocalVar, N) if capturedVars(r) =>
                giveUp
              case Value.Ref(r: LocalVar, N) =>
                assignedResults.get(r).fold(giveUp)(getShapesA)
              case Value.Ref(r, S(sym: ModuleOrObjectSymbol)) =>
                Set.single(sym)
              case Value.Lit(lit) => Set.single(lit)
              case _ => giveUp
          
          var shapes = if deadBranchRemoval then getShapes(scrut2) else giveUp
          // TODO: if analysis gave up, make the shapes the set of cases of the patmat, to rm redundant arms
          
          if !gaveUp then log(s"Initial shapes: ${shapes}")
          
          val oldAssigned = assignedResults
          var curAssigned = oldAssigned
          
          val arms2 = if gaveUp then arms else arms.filterConserve: (pat, body) =>
            @inline def regChange(reason: Str) =
              registerChange(s"Arm ${pat.showDbg} is unreachable. Reason: ${reason}")
              false
            pat match
            case Case.Lit(lit) => 
              shapes.contains(lit) && { shapes -= lit; true } || regChange("Impossible literal")
            case Case.Cls(sym, _) =>
              
              // FIXME: take inheritance into account
              // FIXME: take lit <: virual-cls into account (such as true <: Bool)
              
              shapes.contains(sym) && { shapes -= sym; true } || regChange("Impossible instanceof")
            case _ => true
          
          if !gaveUp then log(s"Filtered arms: ${arms2.map(_._1)}")
          
          val newArms = arms2.mapConserve:
            case arm @ (cse, body) =>
              val newBody = applyBlock(body)
              curAssigned = merge(curAssigned, assignedResults)
              assignedResults = oldAssigned
              if newBody is body then arm else cse -> newBody
          val newDflt = if !gaveUp && shapes.isEmpty
            then S(Unreachable("exhaustive match"))
            else dflt.mapConserve:
              case body =>
                val newBody = applyBlock(body)
                curAssigned = merge(curAssigned, assignedResults)
                assignedResults = oldAssigned
                if newBody is body then body else newBody
          if newDflt.isEmpty then curAssigned = merge(curAssigned, assignedResults)
          assignedResults = curAssigned
          
          // log(s"After match: ${assignedResults}")
          val restRewritten = applySubBlock(rest)
          
          if (scrut2 is scrut) && (newArms is arms) && (newDflt is dflt) && (restRewritten is rest) then b
          else Match(scrut2, newArms, newDflt, restRewritten)
          
      case _ => 
        super.applyBlock(b)
    
    // FIXME: refactor transformers so this is not so error-prone (adding this case to `applyBlock` doesn't work)
    override def applyScopedBlock(b: Block): Block =
      b match
      case Scoped(syms, body) =>
        syms.foreach:
          case sym: LocalVar =>
            assignedResults += sym -> Uninitialized
          case _ =>
        val res = super.applyScopedBlock(b)
        syms.foreach:
          case sym: LocalVar =>
            // * Note: it's crucial to reset the symbols to `uninitialized` when the scope ends,
            // * otherwise they could be picked up by transitive assignments rewriting.
            // * This reassignment makes them ineligible.
            assignedResults += sym -> Uninitialized
          case _ =>
        res
      case _ =>
        super.applyScopedBlock(b)
    
    override def applyValue(v: Value)(k: Value => Block): Block =
      v match
      case Value.Ref(loc: LocalVar, N) if !inDryRun && !capturedVars(loc) =>
        
        val rs = assignedResults(loc)
        // log(s"Ref ${loc.showDbg} ${rs} ${localVars(loc)} ${capturedVars(loc)}")
        
        def analyzeAssignments(asst: AssignInfo): Unit =
          asst match
          case Unknown | Uninitialized => ()
          case Merge(a1, a2) =>
            analyzeAssignments(a1)
            analyzeAssignments(a2)
          case Assigned(ass, _) =>
            // * [Future: dead assignment removal]
            // liveAssignments.put(ass, ())
        
        var litValue: Bool | Value = true
        var emptyHanded = false
        
        def analyzeValues(asst: AssignInfo): Set[Value.Ref] =
          if emptyHanded && litValue === false then
            analyzeAssignments(asst)
            Set.empty
          else asst match
            case Unknown =>
              litValue = false
              Set.empty
            case Uninitialized => Set.empty
            case Assigned(ass, opt) =>
              // * [Future: dead assignment removal]
              // liveAssignments.put(ass, ())
              
              if litValue =/= false then
                ass.rhs match
                case v @ Value.Lit(lit) =>
                  if litValue === true then
                    litValue = v
                  else if litValue =/= v then
                    litValue = false
                case _ =>
                  litValue = false
              opt match
              case S((r @ Value.Ref(lv: LocalVar, N)) -> rhs) =>
                if assignedResults(lv) is rhs
                then Set.single(r) ++ analyzeValues(rhs)
                else Set.empty
              case S(lv -> rhs) =>
                Set.single(lv) ++ analyzeValues(rhs)
              case N => Set.empty
            case Merge(a1, a2) =>
              // * [Future: dead assignment removal]
              // FIXME: this currently short-circuits, which will miss some live assignments...
              
              val l = analyzeValues(a1)
              if l.isEmpty && litValue === false then
                emptyHanded = true
                analyzeAssignments(a2)
                Set.empty
              else l & analyzeValues(a2)
        
        val vars = analyzeValues(rs)
        
        // log(s"Analysis: litValue: ${litValue}, unchanged vars: ${vars}")
        
        litValue match
        case true =>
          registerChange(s"${loc.showDbg} ~> undefined")
          return k(Value.Lit(syntax.Tree.UnitLit(false)))
        case lit: Value =>
          registerChange(s"${loc.showDbg} ~> ${lit.showDbg}")
          return k(lit)
        case false =>
          vars.minByOption(_.l.uid) match
          case N => k(v)
          case S(v2) => 
            registerChange(s"${loc.showDbg} ~> ${v2.showDbg} (via ${vars.map(_.showDbg).mkString(", ")})")
            k(v2)
        
      case _ => super.applyValue(v)(k)
    
    override def applyResult(r: Result)(k: Result => Block): Block =
      // Some partial evaluation – TODO: move to IR smart constructors
      r match
      case Call(Value.Ref(sym: BuiltinSymbol, N), (arg1 :: arg2 :: Nil) :: Nil)
        if sym.nme === "," && arg1.spread.isEmpty && arg2.spread.isEmpty
        =>
          Assign.discard(arg1.value, k(arg2.value))
      case Call(Value.Ref(sym: BuiltinSymbol, N), args :: Nil) if args.forall(_.value.isInstanceOf[Value]) =>
        val argValues = args.map(_.value.asInstanceOf[Value])
        args.foreach(a => assert(a.spread.isEmpty))
        builtinEval.lift((sym.nme, argValues)) match
        case S(v) =>
          registerChange(s"Evaluating builtin ${sym.nme} with args ${argValues.map(_.showDbg).mkString(", ")} ~> ${v.showDbg}")
          k(v)
        case N => super.applyResult(r)(k)
      case r => super.applyResult(r)(k)
    
    // TODO: mv to smart ctor of Call
    import syntax.Tree.*, Value.Lit
    val builtinEval: PartialFunction[(Str, List[Value]), Value] =
      case ("+", (lit @ Lit(IntLit(v1))) :: Nil) => lit
      case ("+", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(IntLit(v1 + v2))
      case ("-", Lit(IntLit(v1)) :: Nil) => Lit(IntLit(-v1))
      case ("-", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(IntLit(v1 - v2))
      case ("*", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(IntLit(v1 * v2))
      // * For "/", should check for 0 and return a DecLit
      case ("%", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(IntLit(v1 % v2))
      case ("===", Lit(l1) :: Lit(l2) :: Nil) => Lit(BoolLit(l1 == l2))
      case ("!==", Lit(l1) :: Lit(l2) :: Nil) => Lit(BoolLit(l1 != l2))
      case ("<", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(BoolLit(v1 < v2))
      case ("<=", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(BoolLit(v1 <= v2))
      case (">", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(BoolLit(v1 > v2))
      case (">=", Lit(IntLit(v1)) :: Lit(IntLit(v2)) :: Nil) => Lit(BoolLit(v1 >= v2))
      case ("&&", Lit(BoolLit(v1)) :: Lit(BoolLit(v2)) :: Nil) => Lit(BoolLit(v1 && v2))
      case ("||", Lit(BoolLit(v1)) :: Lit(BoolLit(v2)) :: Nil) => Lit(BoolLit(v1 || v2))
      case ("!", Lit(BoolLit(v)) :: Nil) => Lit(BoolLit(!v))
    
  end DataFlowAnalysis
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  class Inliner(using Config.Inliner) extends Helper:
    
    def apply(prog: Program): Program =
      val m = InlinerAnalyzer.walk(prog.main)
      InlinerReplacer.replace(m, prog)
    
    object Helpers:
      
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
      
      /** Match multiple argument lists against multiple parameter lists.
        * Returns None if any arg list fails to match its corresponding param list,
        * or if there are fewer arg lists than param lists (partial application).
        * Extra arg lists beyond the param lists are ignored here and should be
        * handled by the caller (e.g., applied as a chained call on the result). */
      def matchAllArgs(argss: List[List[Arg]], params: List[ParamList]): Option[List[(VarSymbol, Result)]] =
        if argss.length < params.length then return N
        val matchedPairs = argss.zip(params)
        val allMatched = matchedPairs.foldLeft[Option[List[(VarSymbol, Result)]]](S(Nil)):
          case (N, _) => N
          case (S(acc), (args, paramList)) =>
            matchArgs(args, paramList).map(acc ::: _)
        allMatched
    
    import Helpers.*
    
    object InlinerAnalyzer:
      case class InlinerFunInfo(
        defn: FunDefn,
        isMethod: Bool,
        private[InlinerAnalyzer] var useCount: Int,
        private[InlinerAnalyzer] var disallowElimination: Bool,
        private[InlinerAnalyzer] var isLoopBreaker: Bool,
      ):
        def isPrivate = !symbolsToPreserve.contains(defn.sym)
        
        // Whether this function can be inlined without causing any code duplication,
        // i.e. the original definition can be removed and there is only one usage.
        def canBeInlineEliminated =
          isPrivate && !isMethod && useCount <= 1 && !disallowElimination && !isLoopBreaker
          // false
        
        def shouldBeInlined(newBlk: Block): Bool =
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
          case c @ Call(TermSymbolPath(ts), argss) =>
            useCnt(ts) += 1
            usages(ts) ::= (currentFunSym, c)
            argss.foreach(_.foreach(applyArg))
          case _ => super.applyResult(r)
        
        override def applySymbol(sym: Symbol): Unit =
          sym.asTrm.foreach: ts =>
            useCnt(ts) += 1
            hasNakedRef(ts) = true
        
        def analyze(blk: Block): InlinerMap =
          applyBlock(blk)
          map.foreach: (sym, info) =>
            info.useCount = useCnt(sym)
            info.disallowElimination = info.disallowElimination || hasNakedRef(sym)
          val edges: Buffer[(TermSymbol, TermSymbol)] = Buffer.empty
          usages.foreach: (sym, calls) =>
            calls.foreach: (caller, call) =>
              if map.contains(sym) then
                map(sym).disallowElimination = map(sym).disallowElimination ||
                  map(sym).defn.params.isEmpty ||
                  matchAllArgs(call.argss, map(sym).defn.params).isEmpty
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
    
    end InlinerAnalyzer
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
      
      class Transformer(m: InlinerMap) extends BlockTransformer(SymbolSubst()):
        
        // The call graph may be cyclic, in which case we break the infinite loop using this map by
        // assuring that the block corresponding to a term symbol may only be transformed once.
        // This map also allows the function block to be optimized on first use before its declaration.
        // Key not in map -> not yet analyzed
        // Key in map but value is None -> the optimized body is being computed
        // Key in map with value -> the function is optimized
        val newFunctionBody = MutMap.empty[TermSymbol, Option[Block]]
        
        override def applyMainBlock(main: Block): Block =
          super.applyMainBlock(main).flattened
        
        override def applyBlock(blk: Block) =
          blk match
          case Define(defn: FunDefn, rest) if m(defn.dSym).canBeInlineEliminated =>
            log(s"Inline elimination: ${defn.dSym}")
            registerChange(s"rm inline-eliminated function ${defn.dSym.showDbg}")
            applyBlock(rest)
          case _ => super.applyBlock(blk)
        
        override def applyFunDefn(fun: FunDefn): FunDefn =
          newFunctionBody.get(fun.dSym) match
            case N =>
              newFunctionBody(fun.dSym) = N
              val newBdy = applyBlock(fun.body)
              newFunctionBody(fun.dSym) = S(newBdy)
              if newBdy is fun.body then fun else
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, newBdy)(fun.configOverride, fun.annotations)
            case S(N) =>
              // The expansion of the function body itself reaches its own definition, which is impossible
              lastWords("Function body contains its own definition.")
            case S(S(blk)) =>
              if blk is fun.body then fun else
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, blk)(fun.configOverride, fun.annotations)
        
        override def applyResult(r: Result)(k: Result => Block): Block = r match
          case c @ Call(TermSymbolPath(ts), argss) if m.contains(ts) && argss.nonEmpty =>
            newFunctionBody.get(ts)
            .getOrElse:
              newFunctionBody(ts) = N
              val newBdy = applyBlock(m(ts).defn.body)
              newFunctionBody(ts) = S(newBdy)
              S(newBdy)
            .fold(super.applyResult(r)(k)): blk =>
              val info = m(ts)
              if !info.shouldBeInlined(blk) then
                super.applyResult(r)(k)
              else
                val matchedArgs = matchAllArgs(argss, info.defn.params)
                matchedArgs match
                case N =>
                  super.applyResult(r)(k)
                case S(matchedArgs) =>
                  registerChange(s"inline call ${ts.showDbg}")
                  log(s"Inline call for ${ts}, with args ${argss}")
                  val extraArgss = argss.drop(info.defn.params.length)
                  def go(acc: Block => Block, args: List[(VarSymbol, Result)], mapping: Map[Symbol, Symbol]): Block =
                    args match
                    case Nil =>
                      val resSym = TempSymbol(N, "inlinedVal")
                      val copier = Copier(resSym, mapping)
                      val newBlk = copier.applyBlock(blk)
                      if extraArgss.isEmpty then
                        acc(Scoped(Set.single(resSym), newBlk(k(Value.Ref(resSym)))))
                      else
                        acc(Scoped(Set(resSym), newBlk(
                          k(Call(resSym.asPath, extraArgss.ne_!)(c.isMlsFun, c.mayRaiseEffects, false)))))
                    case (sym, value) :: argRest =>
                      val newSym = VarSymbol(sym.id)
                      go(acc.assignScoped(newSym, value), argRest, mapping + (sym -> newSym))
                  go(blockBuilder, matchedArgs, Map.empty)
          case _ => super.applyResult(r)(k)
      
      def replace(m: InlinerMap, prog: Program): Program =
        Transformer(m).applyProgram(prog)
    
    end InlinerReplacer
    
  end Inliner
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
end BlockSimplifier


