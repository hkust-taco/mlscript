package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer, LinkedHashSet}
import scala.annotation.tailrec
import sourcecode.{Line, FileName}

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.{State, Ctx, ctx}
import hkmc2.syntax.Literal
import hkmc2.{codegen => argss}


/** `symbolsToPreserve` is the set of local symbols we want to leave alone;
  * typically, these will be top-level symbols that are being exported from a diff-test block;
  * we don't want to eliminate these. */
class BlockSimplifier
    (symbolsToPreserve: Set[BoundSymbol], tl: TL, printer: Program => Str)
    (using DebugPrinter, State, Config, Raise, Ctx):
  import tl.*
  
  
  val deadBranchRemoval = config.deadBranchRemoval
  
  val MaxIterations = 10
  val MaxDCEIterationsPerIter = 10
  val MinInlineFuelInThresholdUnits = 100
  // * The inlining growth budget is granted on the first application and then retained across
  // * later ones: the compilation pipeline applies the same simplifier more than once to a given
  // * compilation unit, and the budget is meant to bound code growth per file, not per pass.
  // * These are only ever written by `apply` and `spendInlineFuel` below.
  private var inlineFuelGranted = false
  private var remainingInlineFuel = 0
  
  
  def apply(prog: Program): Program =
    
    // Automatic inlining is individually bounded by the small-body threshold, but
    // repeated simplification can keep making a recursive worker look small after
    // each round of constant propagation. Give each file a finite growth budget
    // proportional to its initial IR size, with a threshold-based floor so tiny
    // files can still benefit from ordinary cross-file inlining. Explicit
    // `@inline` and no-duplication inline elimination do not spend from this budget.
    if !inlineFuelGranted then
      inlineFuelGranted = true
      remainingInlineFuel = config.inlining match
        case S(cfg) => prog.main.size max (cfg.inlineThreshold * MinInlineFuelInThresholdUnits)
        case N => 0

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
      
      if summon[Config].optimizer.deadCodeElim then
        // * Running DCE once sometimes produces more DCE opportunities;
        // * it is important to apply all of them so that later passes, such as COC,
        // * are not impeded by things like unused labels from inlining.
        var dceIteration = 0
        while
          val dce = new DeadCodeElim()
          res = dce.apply(res)
          changed ||= dce.changed
          if dce.changed then
            log("▶ DCE:\n" + printRes)
            dceIteration += 1
            dceIteration < MaxDCEIterationsPerIter
          else false
        do ()
      
      if summon[Config].optimizer.dataFlowAnalysis then
        val vp = new DataFlowAnalysis(LocalVars.analyze(res.main))
        res = vp.apply(res)
        changed ||= vp.changed
        if vp.changed then log("▶ VP:\n" + printRes)
      
      summon[Config].inlining.foreach: cfg =>
        
        // * Runs after DCE so that unused labels from inlining are already removed
        val coc = new CaseOfCase(using cfg)
        res = coc.applyProgram(res)
        changed ||= coc.changed
        if coc.changed then log("▶ COC:\n" + printRes)
        
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
  
  
  // * Only such variables can be assigned directly in the IR
  type LocalVar = LocalVarSymbol
  
  object LocalVars extends CachedAnalysis[Block, Set[LocalVar]]:
    
    def analyzeUncached(block: Block): Set[LocalVar] =
      def paramsOf(paramLists: IterableOnce[ParamList]): Iterator[LocalVar] =
        paramLists.iterator.flatMap(_.paramSyms).collect:
          case v: LocalVar => v
      def default =
        block.subBlocks.iterator.flatMap(analyze)
      block match
      case Define(fd: FunDefn, rest) =>
        (paramsOf(fd.params) ++ default).toSet
      case Define(cd: ClsLikeDefn, rest) =>
        (paramsOf(cd.paramsOpt.iterator ++ cd.auxParams.iterator) ++
          paramsOf(cd.methods.iterator.flatMap(_.params)) ++
          paramsOf(cd.companion.iterator.flatMap(_.methods).flatMap(_.params)) ++
          default).toSet
      case Scoped(syms, rest) =>
        (rest.analyze.iterator ++ syms.iterator.collect { case v: LocalVar => v }).toSet
      case _ => default.toSet
    
  end LocalVars
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  /** A simple pass to eliminate the most obvious kind of dead code;
    * hopefully allows more expensive passes such as DataFlowAnalysis to do less work. */
  class DeadCodeElim() extends BlockTransformer(SymbolSubst.Id), Helper:
    
    var analysisDone = false
    
    val usedLabels = MutSet.empty[LabelSymbol]
    val definedVars = MutSet.empty[ScopedSymbol]
    val localVars = MutSet.empty[ScopedSymbol]
    val usedVars = MutSet.empty[ScopedSymbol]
    val privateVars = MutSet.empty[TermSymbol]
    val usedPrivateFields = MutSet.empty[TermSymbol]
    lazy val privateFieldsToRemove: Set[TermSymbol] =
      assert(analysisDone)
      privateVars.iterator.filterNot(usedPrivateFields).toSet
    var tailLabels = MutSet.empty[LabelSymbol]
    
    def apply(prog: Program): Program =
      
      new BlockTraverser:
        
        applyProgram(prog)
        
        override def applyPath(p: Path): Unit =
          p match
            case sel: Select =>
              sel.symbol.foreach:
                case ts: TermSymbol =>
                  usedPrivateFields += ts
                case _ =>
            case Value.SimpleRef(loc: LocalVarSymbol) =>
              usedVars += loc
            case Value.MemberRef(loc, _) =>
              usedVars += loc
            case _ =>
          super.applyPath(p)
        
        override def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
          privateVars ++= defn.privateFields
          defn.companion.foreach(body => privateVars ++= body.privateFields)
          super.applyClsLikeDefn(defn)
        
        override def applyBlock(b: Block): Unit =
          b match
            case Define(defn, rst) =>
              definedVars += defn.sym
            case Scoped(syms, _) =>
              localVars ++= syms
            case Break(lbl) => usedLabels += lbl
            case Continue(lbl) => usedLabels += lbl
            case Assign(lhs: LocalVarSymbol, rhs, rst) =>
              definedVars += lhs
            case _ =>
          super.applyBlock(b)
      
      analysisDone = true
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
        case _: Throw | _: Return | _: Unreachable | _: Continue | _: Break => true
        case _: End => false
        
    end AbortiveAnalysis
    
    
    override def applyValue(v: Value)(k: Value => Block) = v match
      // * Replace with `undefined` those references to local variables that are never assigned
      case Value.SimpleRef(loc: LocalVarSymbol) if localVars.contains(loc) && !definedVars.contains(loc) =>
        registerChange(s"${loc.showDbg} is never assigned; replacing read with undefined")
        // if !symbolsToPreserve(loc) then removedLocals += loc
        k(Value.Lit(syntax.Tree.UnitLit(false)))
      case _ => super.applyValue(v)(k)
    
    override def applyBlock(b: Block): Block = b match
      // * Discard assignments to local variables that are never read (and are not preserved)
      case Assign(lhs: LocalVarSymbol, rhs, rst) if localVars(lhs) && !usedVars(lhs) && !symbolsToPreserve(lhs) =>
        registerChange(s"rm ${lhs.showDbg} = ${rhs.showDbg}")
        applyResult(rhs)(r => Assign.discard(r, applyBlock(rst)))

      // * Discard writes to private fields that are never read
      case assign @ AssignField(lhs, _, rhs, rst) =>
        assign.symbol match
        case S(ts: TermSymbol) if privateFieldsToRemove(ts) =>
          registerChange(s"rm unused private field write ${ts.showDbg} = ${rhs.showDbg}")
          applyPath(lhs): lhs2 =>
            applyResult(rhs): rhs2 =>
              Assign.discard(lhs2, Assign.discard(rhs2, applyBlock(rst)))
        case _ => super.applyBlock(b)

      // * Remove local pure definitions that are never read (and are not preserved)
      case Define(defn, rest) =>
        val defnSym = defn.sym
        if !defn.isPure
        || !localVars(defnSym)
        || usedVars(defnSym)
        || symbolsToPreserve(defnSym)
        then super.applyBlock(b)
        else
          registerChange(s"rm unused pure defn ${defnSym.showDbg}")
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

    private def removeUnusedPrivateFields(fields: Ls[TermSymbol]): Ls[TermSymbol] =
      fields.filterConserve: fld =>
        val keep = !privateFieldsToRemove(fld)
        if !keep then registerChange(s"rm unused private field ${fld.showDbg}")
        keep

    override def applyObjBody(defn: ClsLikeBody): ClsLikeBody =
      val defn2 = super.applyObjBody(defn)
      val privateFields2 = removeUnusedPrivateFields(defn2.privateFields)
      if privateFields2 is defn2.privateFields
      then defn2
      else defn2.copy(privateFields = privateFields2)

    override def applyClsLikeDefn(defn: ClsLikeDefn)(k: Defn => Block): Block =
      super.applyClsLikeDefn(defn):
        case cls: ClsLikeDefn =>
          val privateFields2 = removeUnusedPrivateFields(cls.privateFields)
          val cls2 =
            if privateFields2 is cls.privateFields
            then cls
            else cls.copy(privateFields = privateFields2)(cls.configOverride, cls.annotations)
          k(cls2)
        case other => k(other)
    
    
    // FIXME: refactor transformers so this is not so error-prone (adding this case to `applyBlock` doesn't work)
    override def applyScopedBlock(b: Block): Block = b match
      // * Delete removed local variables from Scoped blocks
      case Scoped(syms, body) =>
        val body2 = applyBlock(body)
        val fvs = body2.freeVars
        val syms2 =
          // * Avoid building sets of symbols if we know that nothing needs to be removed
          val needsCleanup = syms.exists: sym =>
            !fvs.contains(sym) && !symbolsToPreserve(sym)
          if needsCleanup then syms.filter(sym => fvs.contains(sym) || symbolsToPreserve(sym))
          else syms
        if (syms2 is syms) && (body2 is body) then b
        else Scoped(syms2, body2)
      case _ => super.applyScopedBlock(b)
    
    override def applyFunBodyLikeBlock(b: Block): Block =
      nestLabelCtx:
        super.applyFunBodyLikeBlock(b)
    
    override def applySubBlockNonTail(b: Block): Block =
      nestLabelCtx:
        super.applySubBlockNonTail(b)
    
  end DeadCodeElim
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  def getInstCtorShape(path: Path): Opt[ClassLikeSymbol] =
    path.targetSymbol.flatMap:
      case sym: ClassLikeSymbol => S(sym)
      case _ => N
  
  def getCallCtorShape(path: Path, argss: NELs[Ls[Arg]]): Opt[ClassLikeSymbol] =
    path.targetSymbol
      .collect:
        case ccs: ClassCtorSymbol => ccs.associatedCls
      .collect:
        case sym: ClassSymbol if isSaturatedClassCtorCall(sym, argss) => sym
  
  def isSaturatedClassCtorCall(sym: ClassSymbol, argss: NELs[Ls[Arg]]): Bool =
    sym.irClsLikeDefn
    .fold(
        // FIXME: remove this case.
        //    IR passes should NOT access `sym.defn` at all;
        //    but this access is currently necessary because we do not yet store `irClsLikeDefn` in imported symbols.
        sym.defn.map(defn => defn.paramsOpt.size + defn.auxParams.size)
      ): ird =>
        S(ird.paramsOpt.size + ird.auxParams.size)
    .exists: paramListsSize =>
      argss.sizeCompare(paramListsSize) === 0
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  /** Basic intraprocedural flow-sensitive analysis to figure out which assignments may flow into which variables,
    * at each point of the program.
    * 
    * For loops, it is enough to pass through the loop body once without transforming it ("dry run")
    * to get the data flow information from loop-back edges, and then to actually transform the loop.
    * When in dry-run mode, nested loops are also traversed in dry-run mode,
    * so overall each Block is traversed at most twice.
    * 
    * We keep track of a tree of assignments where, if the RHS was a local variable, we also store its analysis value
    * that was in effect at this point, which allows us to eliminate useless transitive assignments.
    * We keep track of variables going out of scope to avoid using them afterwards.
    * 
    * Note that if the program tree is changed, it is imperative to register the change,
    * otherwise dead assignment removal (which runs when no change was detected) will not work correctly,
    * as it relies on object identity. */
  class DataFlowAnalysis(localVars: Set[LocalVar]) extends BlockTransformer(SymbolSubst.Id), Helper:
    
    
    val capturedVars = MutSet.empty[LocalVar]
    // ^ TODO: technically, all we need to prevent is changes to `nonLocallyAssignedVars`,
    //    so we should compute that instead in the future.
    //    Note that the capturing definitions won't see the assignments of the captured variable anyway
    //    because that variable will be treated as unknown, since nested definitions start from an empty environment.
    
    
    val liveAssignInfosUntilChangeTriggered: Buffer[AssignInfo] = Buffer.empty
    
    // * We might need to opt out of tracking some locals, such as those that are assigned
    // * in places with observable non-local control flow, such as in a `try` block.
    // * We can't remove assignments to these variables even if they locally look dead,
    // * as they might in fact not be.
    val impreciselyTrackedVars: MutSet[LocalVar] = MutSet.empty
    
    
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
        
        override def applyLam(lam: Lambda): Unit =
          capturedVars ++= lam.freeVars.iterator.collect { case v: LocalVar => v }
          super.applyLam(lam)
        
      end new
      
      log(s"Captured variables: ${capturedVars}")
      
      cur = applyProgram(prog)
      
      // * Dead assignment removal: if nothing in the program changed, we can remove dead assignments.
      // * We mark live assignments by traversing all live AssignInfo objects that were observed during the analysis.
      if !changed && {
        val ok = cur is prog
        softAssert(ok, "A change in the program was not properly registered during data-flow analysis")
        ok
      } then cur =
        
        import scala.jdk.CollectionConverters._
        import java.util.IdentityHashMap
        
        val traversedAssignedInfos: IdentityHashMap[AssignInfo, Unit] = new IdentityHashMap()
        
        val liveAssigns: IdentityHashMap[Assign, Unit] = new IdentityHashMap()
        
        def rec(assnd: AssignInfo): Unit =
          if traversedAssignedInfos.put(assnd, ()) is null then
            assnd match
            case ass @ AssignInfo.Assigned(_, _, varAsst, rhsRequirements) =>
              liveAssigns.put(ass.originalAssignment, ())
            case AssignInfo.Merge(l, r) =>
              rec(l)
              rec(r)
            case AssignInfo.Uninitialized | AssignInfo.Unknown => ()
        
        liveAssignInfosUntilChangeTriggered.foreach(rec)
        
        // log(s"Live assignments: ${liveAssigns.keySet.asScala.toList.map(a =>
        //   s"${a.lhs.showDbg} := ${a.rhs.showDbg}").sorted}")
        // log(s"Imprecisely accessed: ${impreciselyReadVars.toList.map(_.toString).sorted}")
        
        (new BlockTransformer(SymbolSubst.Id):
          
          override def applyBlock(b: Block): Block =
            b match
            case ass @ Assign(lhs: LocalVar, rhs, rst)
            if localVars(lhs) && !capturedVars(lhs) && !symbolsToPreserve(lhs)
              && !impreciselyTrackedVars(lhs) && !liveAssigns.containsKey(ass)
            =>
              registerChange(s"rm ass ${lhs.showDbg} = ${rhs.showDbg}")
              Assign.discard(rhs, applyBlock(rst))
            case _ => super.applyBlock(b)
          
        ).applyProgram(cur)
      
      end if
      
      cur
      
    end apply
    
    // * A reference we may substitute for another reference, together with
    // * the assignment facts that must still be current for the substitution
    // * to be sound. Requirements are compared by object identity below, so
    // * they precisely describe the data-flow state observed when the fact
    // * was recorded.
    case class TrackedRef(ref: Value.RefLike, requirements: Set[LocalVar -> AssignInfo]):
      def isCurrent: Bool =
        requirements.forall((loc, asst) => assignedResults(loc) is asst)
    
    // * Summary of the direct value that can be propagated for a local.
    // *   - `false` means no known value.
    // *   - `true` means definitely uninitialized,
    // *     meaning any variable access can be replaced by `undefined`, ie, `Value.Lit(UnitLit(false))`.
    // *   - `Value` means this exact value is still available for propagation.
    type KnownValue = Bool | Value
    
    // * The propagated value fact for an assignment, plus equivalent
    // * references that could be substituted while their requirements hold.
    case class ValueAnalysis(litValue: KnownValue, refs: List[TrackedRef])
    
    object ValueAnalysis:
      
      val conservative: ValueAnalysis = ValueAnalysis(false, Nil)
      
      // * Keep a value fact only when all merged control-flow paths agree.
      def mergeLitValues(l: KnownValue, r: KnownValue): KnownValue =
        (l, r) match
        case (false, _) | (_, false) => false
        case (true, true) => true
        case (true, v: Value) => v
        case (v: Value, true) => v
        case (v1: Value, v2: Value) if v1 === v2 => v1
        case _ => false
      
      def mergeRefs(l: List[TrackedRef], r: List[TrackedRef]): List[TrackedRef] =
        l.flatMap: lr =>
          r.collect:
            case rr if lr.ref === rr.ref =>
              TrackedRef(lr.ref, lr.requirements ++ rr.requirements)
    
    end ValueAnalysis
    
    // * An unsaturated pure call that can be spliced into a later call, as in
    // * `let f = foo(x); f(y)` ~> `foo(x)(y)`, provided every local captured
    // * by the prefix still denotes the same assignment fact.
    case class TrackedPureCall(call: Call, requirements: Set[LocalVar -> AssignInfo]):
      def isCurrent: Bool =
        requirements.forall((loc, asst) => !capturedVars(loc) && (assignedResults(loc) is asst))
    
    // * Data-flow fact for the latest assignment known for a local variable.
    // * Facts are intentionally immutable so derived analyses can be cached in
    // * lazy values and compared by identity when validating requirements.
    enum AssignInfo:
      case Unknown
      case Uninitialized
      // * `varAsst` is defined if the RHS is a direct reference to some local L,
      // * so that the current variable can be treated as an alias of L as long as L's
      // * associated `AssignInfo` assignment facts remain current.
      // * `rhsRequirements` tracks
      // * all local variables mentioned by the RHS so pure-call prefixes do not
      // * outlive locals that were only valid in a narrower scope.
      case Assigned(
        lhs: LocalVar,
        rhs: Result,
        varAsst: Opt[Value.RefLike -> AssignInfo],
        rhsRequirements: Set[LocalVar -> AssignInfo],
      )(val originalAssignment: Assign)
      case Merge(asst1: AssignInfo, asst2: AssignInfo)
      
      override def toString: String = this match
        case Unknown => "?"
        case Uninitialized => "∅"
        case Assigned(l, r, varAsst, _) => s"${r.showDbg}${
            varAsst.fold(""):
              case (l, r) => "‹"+l.showDbg+":="+r+"›"
          }"
        case Merge(a1, a2) => s"{${a1.toString} | ${a2.toString}}"
      
      def merge(that: AssignInfo): AssignInfo =
        // * Important note: we intentionally do not simplify merges with Unknown,
        // * although it would be logically valid to simplify them to Unknown.
        // * We can't do that here, though, as it would lose information which is currently
        // * used to determine whether a variable has changed or not:
        // * when a variable is reassigned, we always map it to a fresh Assigned node;
        // * the analysis then checks whether a variable has changed by comparing the object identity
        // * of the node that was originally assigned to the variable with the variable's current node.
        // * Now, if the original node was Unknown and we have a control-flow split leading to a merged
        // * of, eg, (Unknown, Assigned(...)), then simplifying that to Unknown would leave the object
        // * identity unchanged, wrongly indicating that the variable has not changed,
        // * when in fact it may have been reassigned (in one of the two control-flow paths).
        if this is that then this
        else this match
        case Uninitialized => that
        case Unknown =>
          if that is Uninitialized then this
          else Merge(this, that)
        case _: Assigned | _: Merge =>
          that match
          case Uninitialized => this
          case Unknown => Merge(this, that)
          case _: Assigned | _: Merge => Merge(this, that)
      
      // * This lazy val is used to avoid retraversing the DAG and to deduplicate entries.
      // * There are more efficient ways of traversing the DAG (e.g. using a mutable visited set),
      // * which could avoid merging so many intermediate sets,
      // * but this is simpler and should be sufficient for now.
      lazy val assigns: Opt[Set[Assigned]] = this match
        case a: Assigned => S(Set.single(a))
        case Merge(asst1, asst2) =>
          // * `for` is only for rich kids
          asst1.assigns match
          case N => N
          case S(set1) =>
            asst2.assigns match
            case N => N
            case S(set2) => S(set1 ++ set2)
        case Uninitialized => S(Set.empty)
        case Unknown => N
      
      lazy val valueAnalysis: ValueAnalysis = this match
        case Unknown =>
          ValueAnalysis.conservative
        case Uninitialized =>
          ValueAnalysis(true, Nil)
        case Assigned(lhs, rhs, opt, _) =>
          val litValue = rhs match
            case v @ Value.Lit(_) => v
            case _ => false
          val refs = opt match
            case S((r @ Value.SimpleRef(lv: LocalVar)) -> rhs) =>
              val requirement = lv -> rhs
              TrackedRef(r, Set.single(requirement)) :: rhs.valueAnalysis.refs
            case S(ref -> rhs) =>
              TrackedRef(ref,
                // * Other types of direct references don't need requirements because they cannot be reassigned:
                // * indeed, `mut val` is not valid outside of an object/module scope,
                // * and if defined in such a scope, a `mut val x` would be referred to through `this.x`.
                Set.empty
              ) :: rhs.valueAnalysis.refs
            case N => Nil
          ValueAnalysis(litValue, refs)
        case Merge(asst1, asst2) =>
          // * [Future: dead assignment removal]
          // FIXME: this currently short-circuits, which will miss some live assignments...
          val l = asst1.valueAnalysis
          if l.refs.isEmpty && l.litValue === false then
            ValueAnalysis.conservative
          else
            val r = asst2.valueAnalysis
            ValueAnalysis(
              ValueAnalysis.mergeLitValues(l.litValue, r.litValue),
              ValueAnalysis.mergeRefs(l.refs, r.refs))
      
      lazy val pureCallPrefix: Opt[TrackedPureCall] = this match
        case Unknown | Uninitialized => N
        case Assigned(lhs, rhs, opt, rhsRequirements) =>
          rhs match
          case call: Call if call.isKnownUnsaturatedCall && call.isPure =>
            S(TrackedPureCall(call, rhsRequirements))
          case _ =>
            opt match
            case S((Value.SimpleRef(next: LocalVar), originalAsst)) =>
              // * If the RHS was a variable that was at the time assigned to a pure call prefix,
              // * we can directly pick up that call, regardless of the current status of that variable.
              originalAsst.pureCallPrefix
            case _ => N
        case Merge(asst1, asst2) =>
          asst1.pureCallPrefix match
          case S(call1) =>
            asst2.pureCallPrefix match
            case S(call2) if call1.call === call2.call =>
              S(TrackedPureCall(call1.call, call1.requirements ++ call2.requirements))
            case _ => N
          case N => N
    
    import AssignInfo.*
    
    
    type AssignedResults = Map[LocalVar, AssignInfo]
    
    val emptyAssignedResults: AssignedResults = Map.empty.withDefaultValue(Unknown)
    
    def impossible: AssignedResults =
      assignedResults.view.mapValues(_ => Uninitialized).toMap.withDefaultValue(Unknown)
    inline def makeImpossibleAfter[R](inline code: => R) =
      val res = code
      assignedResults = impossible
      res
    
    var assignedResults: AssignedResults = emptyAssignedResults
    
    def accessAssignedResults(sym: LocalVar): AssignInfo =
      val res = assignedResults(sym)
      if !changed then
        liveAssignInfosUntilChangeTriggered += res
      res
    
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
    
    
    private def showMap: Str = assignedResults
      .iterator.map: (k, v) =>
        s"${k.showDbg} -> ${v.toString}"
      .mkString("{", ", ", "}")
    
    private def canCollapseImmediateCallPrefix(
        lhs: LocalVar,
        path: Path,
        fun: LocalVar,
        argss: NELs[Ls[Arg]],
    ): Bool =
      !inDryRun && (fun is lhs) && !capturedVars(lhs)
        && !path.freeVars(lhs)
        && !argss.iterator.flatten.exists(_.value.freeVars(lhs))

    private def applyLocalAssignLhs(lhs: LocalVar): LocalVar =
      applyAssignLhs(lhs) match
      case lhs2: LocalVar => lhs2
      case other =>
        softAssert(false, s"Expected local assignment lhs ${lhs.showDbg}, got ${other.showDbg}")
        lhs

    // * `originalAssignment` is the `Assign` node this fact originates from; it is used by
    // * dead-assignment removal to identify the live assignments by object identity,
    // * which is only sound when the program was left unchanged by this analysis.
    private def recordAssignmentFact(lhs: LocalVar, rhs: Result, originalAssignment: Assign): LocalVar =
      val lhs2 = applyLocalAssignLhs(lhs)
      val varAsst = rhs.match
        case r @ Value.SimpleRef(sym: LocalVar) =>
          // * Cross-unit inlining may expose a local owned by another compilation unit. This
          // * intraprocedural analysis does not see that unit's assignments or captures, so only
          // * locals declared in the program being analyzed may participate in alias propagation.
          if !localVars(sym) || capturedVars(sym) then N
          else S(r -> accessAssignedResults(sym))
        case r: Value.RefLike => S(r -> Unknown)
        case _ => N
      val rhsRequirements = rhs.freeVars.iterator.collect:
        case sym: LocalVar if !capturedVars(sym) =>
          sym -> accessAssignedResults(sym)
      assignedResults += lhs2 -> Assigned(lhs2, rhs, varAsst, rhsRequirements.toSet)(originalAssignment)
      lhs2

    override def applySimpleSymbol(sym: SimpleSymbol): SimpleSymbol = sym match
      case sym: LocalVar =>
        accessAssignedResults(sym)
        super.applySimpleSymbol(sym)
      case _ => super.applySimpleSymbol(sym)
    
    override def applyBlock(b: Block): Block =
    // trace[Block](s"Applying block: ${b.showDbg.abbreviate} with map:\n${showMap}", res => s"|= ${showMap}"):
      b match
      
      // * Collapse immediately-invoked path aliases.
      // * This can often arise due to inlining and forwarding functions like `fun i = id`.
      case ass @ Assign(lhs: LocalVar, path: Path, Assign(nextLhs, call @ Call(Value.SimpleRef(fun: LocalVar), argss), rst))
        if canCollapseImmediateCallPrefix(lhs, path, fun, argss) && path.isPure
      =>
          registerChange(s"immediate assigned call prefix ${lhs.showDbg} ~> ${path.showDbg}")
          applyPath(path): path2 =>
            val lhs2 = recordAssignmentFact(lhs, path2, ass)
            val combined = Call(path2, argss)(call.metadata).withLocOf(call)
            val res = applyBlock(Assign(nextLhs, combined, rst))
            // * Note that it is incorrect to eliminate the `lhs` assignment even if `!rst.freeVars(lhs)`,
            // * because the assignment may be visible from an outer block
            // * (eg, the current block could be inside a Label or Match).
            Assign(lhs2, path2, res)
      // * Note the following case does not necessarily assume evaluating the path is pure.
      // * Since there is no intervening statement and the local has no other use,
      // * this preserves both the number and order of evaluations.
      case ass @ Assign(lhs: LocalVar, path: Path, Return(call @ Call(Value.SimpleRef(fun: LocalVar), argss)))
        if canCollapseImmediateCallPrefix(lhs, path, fun, argss) && (path.isPure || !symbolsToPreserve(lhs))
      =>
          registerChange(s"immediate returned call prefix ${lhs.showDbg} ~> ${path.showDbg}")
          applyPath(path): path2 =>
            val lhs2 = recordAssignmentFact(lhs, path2, ass)
            val combined = Call(path2, argss)(call.metadata).withLocOf(call)
            val res = applyBlock(Return(combined))
            if symbolsToPreserve(lhs) then Assign(lhs2, path2, res) else res

      // * Discard local variables that are assigned just to be returned
      // * Note: the reason we do this here and not in DeadCodeElim is that we need to check `capturedVars`
      case Assign(lhs: LocalVar, rhs, Return(Value.SimpleRef(ret)))
        if !inDryRun && (ret is lhs) && !capturedVars(lhs) && !symbolsToPreserve(lhs)
      =>
        registerChange(s"tail-return ${lhs.showDbg} ~> ${rhs.showDbg}")
        applyBlock(Return(rhs))
      
      case ass @ Assign(lhs: LocalVar, rhs, rst) if !capturedVars(lhs) =>
        // log(s"Propagating ${lhs.showDbg} := ${rhs.showDbg} (${assignedResults.get(lhs)})")
        
        applyResult(rhs): rhs2 =>
        
          val lhs2 = recordAssignmentFact(lhs, rhs2, ass)
          val rst2 = applyBlock(rst)
          if (lhs2 is lhs) && (rhs2 is rhs) && (rst2 is rst) then ass else Assign(lhs, rhs2, rst2)
        
      case Assign(lhs, rhs, rst) =>
        // log(s"Not propagating ${lhs } := ${rhs}")
        
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
          // * Initially, we treat this loop's rest block as unreachable.
          // * Then, when non-abortive loops are found to either `break` or fall-through,
          // * we will get merges that make the rest recognized as reachable.
          atLabelEnd.put(label, impossible)
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
          // * This block might be executed from an unknown point in `sub` (where the first exception is thrown),
          // * so we have to be conservative and not propagate any information.
          if !changed then
            assignedResults.valuesIterator.foreach(liveAssignInfosUntilChangeTriggered += _)
            // * ^ all assigned infos are still to be considered live, even though we reset `assignedResults`
          assignedResults = emptyAssignedResults
          // * Moreover, we have to special-case all assigned local variables, as the corresponding assignments
          // * might end up being live even though local flow analysis would think they are not.
          sub.definedVars.foreach:
            case sym: LocalVar =>
              log(s"Variable ${sym.showDbg} is written in a `finally` block; marking it as imprecise tracked")
              impreciselyTrackedVars += sym
            case _ =>
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
          def getAssignInfoShapes(a: AssignInfo): Set[Shape] =
            if gaveUp then Set.empty
            a.assigns match
            case N => giveUp
            case S(assts) => assts.flatMap:
              case Assigned(lhs, rhs, varAsst, _) =>
                varAsst match
                case S(Value.MemberRef(r, sym: ModuleOrObjectSymbol) -> _) =>
                  Set.single(sym)
                case S(_ -> ass) =>
                  getAssignInfoShapes(ass)
                case N =>
                  rhs match
                  case p: Path => getShapes(p)
                  case Call(path, argss) =>
                    getCallCtorShape(path, argss) match
                    case S(sym: ClassSymbol) =>
                      Set.single(sym)
                    case _ => giveUp
                  case Instantiate(_, cls, _) =>
                    // * Note: Instantiate nodes are globally assumed to be saturated
                    getInstCtorShape(cls) match
                    case S(sym) =>
                      Set.single(sym)
                    case _ => giveUp
                  case _ => giveUp
          def getShapes(p: Path): Set[Shape] =
            if gaveUp then Set.empty
            else
              p match
              case Value.SimpleRef(r: LocalVar) if capturedVars(r) =>
                giveUp
              case Value.SimpleRef(r: LocalVar) =>
                assignedResults.get(r).fold(giveUp)(getAssignInfoShapes)
              case Value.MemberRef(r, sym: ModuleOrObjectSymbol) =>
                Set.single(sym)
              case Value.Lit(lit) => Set.single(lit)
              case _ =>
                p.targetSymbol match
                case S(sym: ModuleOrObjectSymbol) => Set.single(sym)
                case _ => giveUp
          
          var shapes = if deadBranchRemoval then getShapes(scrut2) else giveUp
          // TODO: if analysis gave up, make the shapes the set of cases of the patmat, to rm redundant arms
          
          if !gaveUp then log(s"Initial shapes: ${shapes}")
          
          val oldAssigned = assignedResults
          var branchAssigneds = List.empty[AssignedResults]
          def recordBranch(newBody: Block): Unit =
            if !newBody.isAbortive then
              branchAssigneds ::= assignedResults
            assignedResults = oldAssigned
          def canEscapeBranch(info: AssignInfo): Bool = info match
            case Unknown => false
            case Uninitialized => true
            case Assigned(_, rhs, _, _) =>
              rhs.freeVars.forall:
                case sym: LocalVar => oldAssigned.contains(sym)
                case _ => true
            case Merge(asst1, asst2) =>
              canEscapeBranch(asst1) && canEscapeBranch(asst2)
          def mergeBranchInfos(infos: List[AssignInfo]): AssignInfo =
            // * Unlike `AssignInfo.merge`, which retains the merged facts precisely so that later
            // * reads can still reach them, giving up here *discards* them: a read after the match
            // * would only see `Unknown`, so dead assignment removal could no longer tell that the
            // * discarded assignments are in fact live. We therefore mark them live explicitly.
            def giveUp: AssignInfo =
              infos.foreach(liveAssignInfosUntilChangeTriggered += _)
              Unknown
            if infos.exists(_ is Unknown) then giveUp
            else if infos.exists(_ is Uninitialized) && !infos.forall(_ is Uninitialized) then
              val initializedInfos = infos.filterNot(_ is Uninitialized)
              if initializedInfos.forall(canEscapeBranch) then initializedInfos.reduce(_.merge(_))
              else giveUp
            else infos.reduce(_.merge(_))
          
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
              // * We need to visit the symbols of the cases to register the liveness of their AssignedInfo.
              // * Normally, the Match case uses `applyCase`, which uses `applyPath`, and they both take a continuation,
              // * making things unnecessarily awkward for the data-flow analysis.
              cse.freeVars.foreach:
                case sym: SimpleSymbol => applySimpleSymbol(sym)
                case _ =>
              val newBody = applyBlock(body)
              recordBranch(newBody)
              if newBody is body then arm else cse -> newBody
          val newDflt =
            if !gaveUp && shapes.isEmpty
            then
              val res = S(Unreachable("exhaustive match"))
              if dflt === res then dflt else
                registerChange(s"Default arm is unreachable because all shapes are covered")
                res
            else dflt.mapConserve:
              case body =>
                val newBody = applyBlock(body)
                recordBranch(newBody)
                if newBody is body then body else newBody
          if newDflt.isEmpty then branchAssigneds ::= oldAssigned
          val branchKeys = branchAssigneds.iterator.flatMap(_.keysIterator).toSet
          assignedResults =
            branchKeys.iterator
              .map: key =>
                key -> mergeBranchInfos(branchAssigneds.map(_(key)))
              .toMap
              .withDefaultValue(Unknown)
          
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
      case Value.SimpleRef(loc: LocalVar) if !inDryRun && !capturedVars(loc) =>
        
        val rs = accessAssignedResults(loc)
        // log(s"Ref ${loc.showDbg} ${rs} ${localVars(loc)} ${capturedVars(loc)}")
        
        val analysis = rs.valueAnalysis
        
        // log(s"Analysis: litValue: ${analysis.litValue}, unchanged vars: ${refs}")
        
        analysis.litValue match
        case true =>
          registerChange(s"${loc.showDbg} ~> undefined")
          return k(Value.Lit(syntax.Tree.UnitLit(false)))
        case lit: Value =>
          registerChange(s"${loc.showDbg} ~> ${lit.showDbg}")
          return k(lit)
        case false =>
          def refs = analysis.refs.iterator.filter(_.isCurrent).map(_.ref)
          refs.minByOption(_.symbol.uid) match
          case N => k(v)
          case S(v2) =>
            registerChange(s"${loc.showDbg} ~> ${v2.showDbg} (via ${refs.map(_.showDbg).mkString(", ")})")
            k(v2)
        
      case _ => super.applyValue(v)(k)
    
    
    private def assignedPureCallPrefix(loc: LocalVar): Opt[Call] =
      // * Only expose prefixes whose dependency facts still match the current
      // * data-flow state; otherwise the prefix may mention stale scoped locals.
      assignedResults(loc).pureCallPrefix.collect:
        case prefix if prefix.isCurrent => prefix.call
    
    
    override def applyResult(r: Result)(k: Result => Block): Block =
      // Some partial evaluation – TODO: move to IR smart constructors
      r match
      
      // * Try to propagate pure calls
      case Value.SimpleRef(loc: LocalVar) if !inDryRun && !capturedVars(loc) =>
        assignedPureCallPrefix(loc) match
        case S(call) =>
          registerChange(s"${loc.showDbg} ~> ${call.showDbg}")
          super.applyResult(call)(k)
        case N =>
          super.applyResult(r)(k)
      
      // * Try to combine pure calls (typically unsaturated calls) assigned to a variable into the current call
      case c @ Call(Value.SimpleRef(loc: LocalVar), argss) if !inDryRun && !capturedVars(loc) =>
        assignedPureCallPrefix(loc) match
        case S(prefix) =>
          registerChange(s"${loc.showDbg} call prefix ~> ${prefix.showDbg}")
          val combined = Call(prefix.fun, (prefix.argss ::: argss).ne_!)(
            CallMetadata(
              prefix.metadata.isMlsFun,
              prefix.metadata.mayRaiseEffects || c.metadata.mayRaiseEffects,
              prefix.metadata.annotations ++ c.metadata.annotations,
            ),
          ).withLocOf(c)
          super.applyResult(combined)(k)
        case N => super.applyResult(r)(k)
      
      // * Remove uses of the strange builtin comma operator
      // * This is not implemented as a smart constructor (unlike usual constant folding)
      // * because it needs to insert an Assign statement.
      case Call(Value.SimpleRef(sym: BuiltinSymbol), (arg1 :: arg2 :: Nil) :: Nil)
        if sym.nme === "," && arg1.spread.isEmpty && arg2.spread.isEmpty
        =>
          registerChange(s"rm comma ${arg1.value.showDbg}, ${arg2.value.showDbg}")
          Assign.discard(arg1.value, k(arg2.value))
      
      case r =>
        super.applyResult(r)(k)
    
    
  end DataFlowAnalysis
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  /** Specialize a match whose scrutinee was assigned known constructors by an earlier match.
    * The remaining unknown path, if any, keeps the original consumer match.
    * More specifically, we optimize successive Match blocks where all of the following hold:
    * - the branches of the previous match assign known constructors to some variable,
    *   except at most one branch which can be assigning an unknown value or not assigning at all to this variable;
    * - the second match scrutinizes that variable and either:
    *     - the branches of the second match can be inlined into the first match
    *       without introducing any code duplication; or
    *     - the branches that would be duplicated are below the inlining threshold;
    * - all the statements between the two matches are pure and can thus be moved out of the way,
    *   similar to how `MergeMatchArmTransformer` works (in `Lowering.scala`) – we reuse `TrivialStatementsAndMatch`.
    * See examples in [test:case-of-case]. */
  class CaseOfCase(using cfg: Config.Inliner) extends BlockTransformer(SymbolSubst.Id), Helper:
    
    type Shape = Literal | ClassLikeSymbol
    
    case class Selected(index: Int, body: Block)
    
    enum ProducerPlan:
      case Abortive(body: Block)
      case Known(body: Block, selected: Selected)
      case Unknown(body: Block)
    
    import ProducerPlan.*
    
    def getShape(result: Result): Opt[Shape] = result match
      case Value.MemberRef(_, sym: ModuleOrObjectSymbol) => S(sym)
      case Value.Lit(lit) => S(lit)
      case path: Path => path.targetSymbol.flatMap(_.asModOrObj)
      case Call(path, argss) => getCallCtorShape(path, argss)
      case Instantiate(_, cls, _) => getInstCtorShape(cls)
      case _ => N
    
    /** Find the shape held by `target` after a straight-line producer arm.
      * Complex control flow remains on the unspecialized path. */
    def getAssignedShape(body: Block, target: LocalVarSymbol): Opt[Shape] =
      def loop(body: Block, shape: Opt[Shape])(k: Opt[Shape] => Opt[Shape]): Opt[Shape] = body match
        case _: End => k(shape)
        case Assign(`target`, rhs, rest) => loop(rest, getShape(rhs))(k)
        case Assign(_, rhs, rest) if rhs.isPure => loop(rest, shape)(k)
        case AssignField(_, _, _, rest) => loop(rest, shape)(k)
        case AssignDynField(_, _, _, _, rest) => loop(rest, shape)(k)
        case Define(_, rest) => loop(rest, shape)(k)
        case Scoped(_, body) => loop(body, shape)(k)
        case Begin(sub, rest) => loop(sub, shape)(loop(rest, _)(k))
        case _ => N
      loop(body, N)(identity)
    
    def isSubtypeOf(actual: ClassLikeSymbol, expected: ClassLikeSymbol): Opt[Bool] =
      def parentOf(sym: ClassLikeSymbol): Opt[Opt[ClassLikeSymbol]] =
        (sym match
          case sym: ClassSymbol => sym.irClsLikeDefn
          case sym: ModuleOrObjectSymbol => sym.irClsLikeDefn
        ).flatMap: defn =>
          defn.parentPath match
            case S(parent) => getInstCtorShape(parent).map(S(_))
            case N => S(N)
        .orElse:
          // FIXME: remove this fallback once imported classes have their `irClsLikeDefn` properly linked
          (sym match
            case sym: ClassSymbol => sym.defn
            case sym: ModuleOrObjectSymbol => sym.defn
          ).flatMap: defn =>
            defn.ext match
              case S(parent) => parent.cls.resolvedSym.flatMap(_.asClsOrMod).map(S(_))
              case N => S(N)
      @tailrec
      def loop(cur: ClassLikeSymbol, seen: Set[ClassLikeSymbol]): Opt[Bool] =
        if cur is expected then S(true)
        else if seen(cur) then N
        else parentOf(cur) match
          case S(S(parent)) => loop(parent, seen + cur)
          case S(N) => S(false)
          case N => N
      loop(actual, Set.empty)
    
    /** Return whether a known shape matches a case, or `None` if deciding would
      * require reasoning that this optimization deliberately does not attempt. */
    def matches(cse: Case, shape: Shape): Opt[Bool] = (cse, shape) match
      case (Case.Lit(expected), actual: Literal) => S(expected == actual)
      case (Case.Lit(_), _: ClassLikeSymbol) => S(false)
      case (Case.Cls(expected, _), actual: ClassLikeSymbol) => isSubtypeOf(actual, expected)
      case _ => N
    
    def select(shape: Shape, arms: Ls[Case -> Block], dflt: Opt[Block]): Opt[Selected] =
      @tailrec
      def loop(arms: Ls[Case -> Block], index: Int): Opt[Selected] = arms match
        case (cse, body) :: rest => matches(cse, shape) match
          case S(true) => S(Selected(index, body))
          case S(false) => loop(rest, index + 1)
          case N => N
        case Nil => dflt.map(Selected(index, _))
      loop(arms, 0)
    
    def canMove(prefix: Block): Bool = prefix match
      case _: End => true
      case Assign(_, _: Value, rest) => canMove(rest)
      case Assign(_, path: Select, rest) => path.isPure && canMove(rest)
      case Define(defn: ValDefn, rest) =>
        defn.rhs.isPure && defn.tsym.owner.isEmpty && canMove(rest)
      case Define(defn: FunDefn, rest) => defn.owner.isEmpty && canMove(rest)
      case Define(defn: ClsLikeDefn, rest) => defn.isPure && canMove(rest)
      case _ => false
    
    def plan(body: Block, target: LocalVarSymbol, consumer: Match): ProducerPlan =
      if body.isAbortive then Abortive(body)
      else
        getAssignedShape(body, target)
          .flatMap(select(_, consumer.arms, consumer.dflt))
          .fold(Unknown(body))(Known(body, _))
    
    override def applyBlock(b: Block): Block = super.applyBlock(b) match
      case m @ Match(scrut, arms, dflt,
        TrivialStatementsAndMatch(k,
          consumer @ Match(Value.SimpleRef(target: LocalVarSymbol), _, _, consumerRest)))
      =>
        
        val prefix = k.fold[Block](End())(_(End()))
        
        val producerDefinedVars: Set[Symbol] = arms.iterator.flatMap(_._2.definedVars).toSet
          ++ dflt.iterator.flatMap(_.definedVars)
        
        if !canMove(prefix) || prefix.freeVars.exists(producerDefinedVars.contains) then m
        else
          val armPlans = arms.map((cse, body) => cse -> plan(body, target, consumer))
          val dfltPlan = dflt.fold[ProducerPlan](Unknown(End()))(plan(_, target, consumer))
          val allPlans = armPlans.map(_._2) :+ dfltPlan
          val unknownCount = allPlans.count(_.isInstanceOf[Unknown])
          
          if unknownCount > 1 then m
          else
            val selected = allPlans.collect:
              case Known(_, selected) => selected
            
            if selected.isEmpty then m
            else
              val selectedCounts = selected.groupMapReduce(_.index)(_ => 1)(_ + _)
              val originalConsumerRetained = unknownCount === 1
              val wouldDuplicate = selected.exists: selected =>
                selectedCounts(selected.index) + (if originalConsumerRetained then 1 else 0) > 1
                  && selected.body.size > cfg.inlineThreshold
              
              if wouldDuplicate then m
              else
                registerChange(s"case-of-case on ${target.showDbg}")
                val usedOriginals = MutSet.empty[Int]
                def materialize(selected: Selected): Block =
                  if originalConsumerRetained || usedOriginals(selected.index) then
                    SymbolRefresher(Map.empty).applyBlock(selected.body)
                  else
                    usedOriginals += selected.index
                    selected.body
                def consumerWithoutRest: Block =
                  Match(consumer.scrut, consumer.arms, consumer.dflt, End())
                def rewrite(plan: ProducerPlan): Block = plan match
                  case Abortive(body) => body
                  case Known(body, selected) => Begin(body, materialize(selected))
                  case Unknown(body) => Begin(body, consumerWithoutRest)
                val newArms = armPlans.map((cse, plan) => cse -> rewrite(plan))
                val newDflt = S(rewrite(dfltPlan))
                k.getOrElse(identity[Block]):
                  Match(scrut, newArms, newDflt, consumerRest)
      
      case b => b
    
  end CaseOfCase
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
  class Inliner(using Config.Inliner) extends Helper:
    
    def apply(prog: Program): Program =
      val m = InlinerAnalyzer.walk(prog.main)
      InlinerReplacer.replace(m, prog)
    
    object Helpers:
      
      /** Match calls to methods selected through a qualifier, such as `Outer.Inner.f(x)`.
        *
        * The qualifier is later used to rewrite module `this` references in the copied body.
        * Direct member refs do not carry enough qualifier information and are handled by
        * `TermSymbolPath` instead. */
      object MethodCallQualifier:
        def unapply(p: Path): Opt[(Path, TermSymbol)] = p match
          case s: Select => s.symbol match
            case S(ts: TermSymbol) if ts.owner.nonEmpty => S((s.qual, ts))
            case _ => N
          case _ => N

      /** Build a mapping from module `this` symbols to their call-site qualifier paths.
        *
        * For example, for `Outer.Mid.Inner.f(x)`, this records:
        * `Inner.this -> Outer.Mid.Inner`, `Mid.this -> Outer.Mid`,
        * and `Outer.this -> Outer`. */
      def buildThisMapping(qual: Path, ownerSym: InnerSymbol): Map[InnerSymbol, Path] =
        def loop(currentQual: Path, currentOwner: InnerSymbol, acc: Map[InnerSymbol, Path]): Map[InnerSymbol, Path] =
          val acc2 = acc + (currentOwner -> currentQual)
          currentQual match
          case s: Select =>
            s.qual.targetSymbol match
            case S(ds: InnerSymbol) => loop(s.qual, ds, acc2)
            case _ => acc2
          case _ => acc2
        loop(qual, ownerSym, Map.empty)

      def accessesPrivateMembers(blk: Block): Bool =
        var found = false
        (new BlockTraverser:
          override def applySymbol(sym: Symbol): Unit = sym match
            case ts: TermSymbol if ts.isPrivate => found = true
            case _ =>
        ).applyBlock(blk)
        found

      // * TODO: once bad actors like the current pattern compiler stop duplicating symbols,
      // *  we can remove this ugly workaround.
      def hasDuplicateBoundSymbols(fun: FunDefn): Bool =
        val seen = MutSet.empty[BoundSymbol | LabelSymbol | ClassCtorSymbol]
        var found = false
        def register(sym: BoundSymbol | LabelSymbol | ClassCtorSymbol): Unit =
          if seen(sym) then found = true
          else seen += sym
        def registerParamList(pl: ParamList): Unit =
          pl.params.foreach(param => register(param.sym))
          pl.restParam.foreach(param => register(param.sym))
        (new BlockTraverser:
          override def applyBlock(b: Block): Unit = b match
            case Scoped(syms, body) =>
              syms.foreach(register)
              applyBlock(body)
            case Label(lbl, loop, body, rest) =>
              register(lbl)
              applyBlock(body)
              applyBlock(rest)
            case _ => super.applyBlock(b)

          override def applyFunDefn(fun: FunDefn): Unit =
            // Local function member symbols are introduced by `Scoped`. Method member symbols
            // have no enclosing `Scoped` and are registered by their owning class below.
            register(fun.dSym)
            fun.params.foreach(registerParamList)
            applyBlock(fun.body)

          override def applyClsLikeDefn(defn: ClsLikeDefn): Unit =
            // Like local functions, local class-like member symbols are introduced by `Scoped`.
            // Methods, on the other hand, bind their member symbols directly in the class body.
            defn.methods.foreach(method => register(method.sym))
            defn.companion.foreach(_.methods.foreach(method => register(method.sym)))
            defn.ctorSym.foreach(register)
            defn.paramsOpt.foreach(registerParamList)
            defn.auxParams.foreach(registerParamList)
            super.applyClsLikeDefn(defn)
        ).applyFunDefn(fun)
        found

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
        private[InlinerAnalyzer] var _isLoopBreaker: Bool,
      ):
        def isPrivate = !symbolsToPreserve.contains(defn.sym)
        private lazy val isPatternHelper = defn.owner.exists(_.isInstanceOf[PatternSymbol])
        private lazy val hasDuplicateBindings = hasDuplicateBoundSymbols(defn)
        private lazy val hasPrivateMemberAccesses = accessesPrivateMembers(defn.body)
        
        inline def isLoopBreaker = _isLoopBreaker
        
        // Whether this method belongs to a true module (as opposed to a class or
        // an instance-based singleton object).
        // Inlining non-virtual (ie final) methods might be done in the future,
        // but will need to be careful about `super` calls and `this` references.
        def isModuleMethod: Bool = defn.dSym.owner match
          case S(owner: ModuleOrObjectSymbol) => owner.tree.k is syntax.Mod
          case _ => false

        /** Requirements that can reject a non-local body without inspecting its body. */
        def passesStaticRequirements: Bool =
          if defn.noInline then return false
          // Pattern compiler helpers may intentionally reuse source pattern variables across
          // mutually-exclusive generated blocks. Symbol-refreshing them as ordinary inline
          // bodies is not sound, so keep those helpers in place.
          if isPatternHelper then return false
          // Instance methods access instance state via `this`, so they must not be
          // inlined as if they were static calls. True modules are safe because
          // their `this` references can be replaced by call-site qualifier paths.
          if isMethod && !isModuleMethod then return false
          // Instantiate nodes are rendered according to the receiving JS builder's
          // freezing policy. Moving a body across compilation units with a different
          // policy could silently turn mutable values into frozen values, or vice versa.
          if defn.dSym.getState.compilationUnitConfig.exists(_.noFreeze =/= config.noFreeze)
          then return false
          true

        // Whether this function can be inlined without causing any code duplication,
        // i.e. the original definition can be removed and there is only one usage.
        def canBeInlineEliminated: Bool =
          isPrivate && !isMethod && !defn.noInline && useCount <= 1 && !disallowElimination && !isLoopBreaker
            && !isPatternHelper && !hasDuplicateBindings
          // false
        
        def inlineCost(newBlk: Block, threshold: Int): Opt[Int] =
          if !passesStaticRequirements then return N
          // Pattern compiler helpers may intentionally reuse source pattern variables across
          // mutually-exclusive generated blocks. Symbol-refreshing them as ordinary inline
          // bodies is not sound, so reject the same shape wherever duplicate bindings occur.
          if hasDuplicateBindings then return N
          // Accessors for JS-private members use a fresh Symbol shared by the owner
          // definition and its out-of-owner references within one emitted module.
          // There is deliberately no cross-module accessor ABI, so keep such accesses
          // in the compilation unit that defines them.
          if (defn.dSym.getState isnt State) && hasPrivateMemberAccesses
          then return N
          // `import.meta.url` denotes the file containing the generated code.
          // Moving it into a caller would silently change its meaning.
          if newBlk.freeVars.exists:
            case sym: VarSymbol => sym.nme === "import"
            case _ => false
          then return N
          // If the definition is marked with inline, we should inline it regardless of the size of the body.
          // If both callee and caller are marked with inline, inlining will ignore the stricter @inline limits.
          // Remark: the case of a recursive function marked with inline will be blocked by loop breaker logic.
          if defn.inline then return S(0)
          // Inline elimination does not spend fuel: the original definition disappears, so
          // substituting it at its only call site does not duplicate the body.
          if canBeInlineEliminated then return S(0)
          if newBlk.size <= threshold then S(newBlk.size) else N
        
      type InlinerMap = Map[TermSymbol, InlinerFunInfo]

      /** @param callGraphSource the function whose outgoing call-graph edges are being collected;
        *   absent in the program's root block and in constructor bodies, which do not correspond
        *   to an inlineable function and therefore cannot be an edge source.
        * @param isNonLocal whether the current function body was obtained through its symbol's
        *   `irDefn`, rather than encountered as a local `Define` in the block being simplified.
        *   Such bodies contribute call-graph edges, but their references do
        *   not affect use counts or elimination decisions for the local block.
        */
      case class FunLikeContext(
        callGraphSource: Opt[TermSymbol],
        hasInlineAnnot: Bool,
        isNonLocal: Bool,
      )
      
      class Traverser extends BlockTraverser:
        import InlinerBodySummary.Entry

        var map: InlinerMap = Map.empty
        val useCnt = MutMap.WithDefault(MutMap.empty[TermSymbol, Int], _ => 0)
        val usages = MutMap.WithDefault(MutMap.empty[TermSymbol, List[(Option[TermSymbol], Call)]], _ => Nil)
        val summaryAdjLists = MutMap.empty[TermSymbol, Set[TermSymbol]]
        val disallowElimination = MutMap.WithDefault(MutMap.empty[TermSymbol, Bool], _ => false)
        // * Non-local definitions are registered before being appended to this worklist. Recursive
        // * references therefore terminate immediately, while advancing an index discovers the
        // * transitive closure without rescanning symbols.
        val pendingNonLocalFunctionBodies = Buffer.empty[FunDefn]
        var nextNonLocalFunctionBody = 0
        val analyzedFunctionBodies = MutSet.empty[TermSymbol]
        val rejectedNonLocalFunctions = MutSet.empty[TermSymbol]
        val cfg = summon[Config.Inliner]
        val maxAutomaticThreshold = cfg.inlineThreshold max cfg.altSmallThreshold
        var contextList: List[FunLikeContext] = FunLikeContext(N, false, false) :: Nil
        
        def currentContext = contextList.head
        
        def currentCallGraphSource = currentContext.callGraphSource
        
        def nested(callGraphSource: Option[TermSymbol], hasInlineAnnot: Bool, isNonLocal: Bool)(thunk: => Unit) =
          contextList = FunLikeContext(callGraphSource, hasInlineAnnot, isNonLocal) :: contextList
          thunk
          val res = contextList.head
          contextList = contextList.tail
          res
        
        def registerFunction(f: FunDefn, isMethod: Bool, isNonLocal: Bool): Bool =
          if !map.contains(f.dSym) then
            val info = InlinerFunInfo(f, isMethod, 0, isNonLocal, false)
            val canAnalyze = !isNonLocal || info.passesStaticRequirements &&
              (f.inline || f.body.size <= maxAutomaticThreshold)
            if !canAnalyze then
              rejectedNonLocalFunctions += f.dSym
              return false
            // * A non-local definition cannot be eliminated from the local block. This is based
            // * on where the definition was encountered, rather than symbol state: incremental
            // * worksheet blocks can share a state while still having distinct function bodies.
            map = map + (f.dSym -> info)
            true
          else
            val info = map(f.dSym)
            softAssert((info.defn is f) && info.isMethod === isMethod,
              s"Inconsistent definitions registered for ${f.dSym.showDbg}")
            if !isNonLocal then
              // * A forward reference may have provisionally registered this definition as
              // * non-local before its local `Define` node was reached. Its local occurrence makes
              // * elimination eligible again.
              info.disallowElimination = false
            false

        def replayBodySummary(summary: InlinerBodySummary): Unit =
          summary.entries.foreach:
            case Entry.DirectCall(callee, call, hasCallGraphSource) =>
              val source = currentCallGraphSource.filter(_ => hasCallGraphSource)
              observeCall(callee, call, source)
            case Entry.NestedFunction(defn, isMethod) =>
              addFunctionAndApplyBody(defn, isMethod)

        def applyFunctionBody(f: FunDefn, isNonLocal: Bool): Unit =
          if analyzedFunctionBodies.add(f.dSym) then
            val summary = f.getOrComputeInlinerBodySummary
            summaryAdjLists(f.dSym) = summary.transitiveCallTargets
            summary.transitiveCallTargets.foreach(registerNonLocalFunction)
            nested(S(f.dSym), f.inline, isNonLocal):
              if isNonLocal then replayBodySummary(summary)
              else applyBlock(f.body)

        def addFunctionAndApplyBody(f: FunDefn, isMethod: Bool): Unit =
          if currentContext.isNonLocal then
            if registerFunction(f, isMethod, true) then applyFunctionBody(f, true)
          else
            applyFunctionBody(f, false)
            registerFunction(f, isMethod, false)

        def registerNonLocalFunction(sym: TermSymbol): Unit =
          if !map.contains(sym) && !rejectedNonLocalFunctions(sym) then
            sym.irDefn.foreach:
              case fd: FunDefn =>
                if registerFunction(fd, fd.owner.nonEmpty, true) then
                  pendingNonLocalFunctionBodies.append(fd)
              case _ =>

        def applyPendingNonLocalFunctionBodies(): Unit =
          while nextNonLocalFunctionBody < pendingNonLocalFunctionBodies.size do
            val f = pendingNonLocalFunctionBodies(nextNonLocalFunctionBody)
            nextNonLocalFunctionBody += 1
            applyFunctionBody(f, true)
        
        override def applyDefn(defn: Defn): Unit = defn match
          case f: FunDefn =>
            addFunctionAndApplyBody(f, false)
          case c: ClsLikeDefn =>
            c.parentPath.foreach(applyPath)
            c.methods.foreach: f =>
              addFunctionAndApplyBody(f, true)
            // Note: no tracking, since `Instantiate` will not be inlined and won't cause cycles.
            nested(N, false, currentContext.isNonLocal):
              applySubBlock(c.preCtor)
              applySubBlock(c.ctor)
            c.companion.foreach: m =>
              m.methods.foreach: f =>
                addFunctionAndApplyBody(f, true)
              // This inherits the previous context as the module ctor is run with the constructor.
              applySubBlock(m.ctor)
          case _ => super.applyDefn(defn)
        
        def observeCall(ts: TermSymbol, call: Call, source: Opt[TermSymbol]): Unit =
          if !currentContext.isNonLocal then
            if currentContext.hasInlineAnnot then
              // Not eligible for inline elimination
              disallowElimination(ts) = true
            useCnt(ts) += 1
          usages(ts) ::= (source, call)
          registerNonLocalFunction(ts)

        override def applyResult(r: Result): Unit = r match
          case c @ Call(TermSymbolPath(ts), argss) =>
            observeCall(ts, c, currentCallGraphSource)
            argss.foreach(_.foreach(applyArg))
          case _ => super.applyResult(r)
        
        override def applyValue(v: Value): Unit = v match
          case Value.MemberRef(bms, ts: TermSymbol) =>
            applySymbol(bms)
            if !currentContext.isNonLocal then
              useCnt(ts) += 1
              disallowElimination(ts) = true
          case _ => super.applyValue(v)

        override def applySymbol(sym: Symbol): Unit =
          if !currentContext.isNonLocal then
            sym.asTrm.foreach: ts =>
              useCnt(ts) += 1
              disallowElimination(ts) = true
        
        def analyze(blk: Block): InlinerMap =
          applyBlock(blk)
          applyPendingNonLocalFunctionBodies()
          map.foreach: (sym, info) =>
            info.useCount = useCnt(sym)
            info.disallowElimination = info.disallowElimination || disallowElimination(sym)
          val adjList = MutMap.empty[TermSymbol, LinkedHashSet[TermSymbol]]
          summaryAdjLists.foreach: (from, tos) =>
            if map.contains(from) then
              for to <- tos if map.contains(to) do
                adjList.getOrElseUpdate(from, LinkedHashSet.empty).add(to)
          usages.foreach: (sym, calls) =>
            calls.foreach: (caller, call) =>
              if map.contains(sym) then
                map(sym).disallowElimination = map(sym).disallowElimination ||
                  map(sym).defn.params.isEmpty ||
                  matchAllArgs(call.argss, map(sym).defn.params).isEmpty
                caller.foreach: caller =>
                  softAssert(map.contains(caller),
                    s"Call-graph source ${caller.showDbg} was not registered before traversal")
                  adjList.getOrElseUpdate(caller, LinkedHashSet.empty).add(sym)

          def pickLoopBreaker(sccComp: Ls[TermSymbol]): TermSymbol =
            sccComp.minBy: sym =>
              (if map(sym).defn.inline then 1 else 0, sym.uid)

          @tailrec
          def assignLoopBreakers(): Unit =
            val sccs = SccAnalysis.sccsFrom(
              (from: TermSymbol) => adjList.getOrElse(from, Nil)
                .iterator.filterNot(to => map(to).isLoopBreaker),
              map.keys)
            if sccs.forall(_.sizeIs == 1) then return
            sccs.foreach: sccComp =>
              if sccComp.sizeIs > 1 then
                // Prefer breaking cycles at non-inline definitions so tiny wrappers
                // can still disappear while their workers stop recursive expansion.
                map(pickLoopBreaker(sccComp))._isLoopBreaker = true
            assignLoopBreakers()
          for (from, tos) <- adjList do
            if tos.contains(from) then
              map(from)._isLoopBreaker = true
          assignLoopBreakers()
          map
      
      def walk(blk: Block): InlinerMap = Traverser().analyze(blk)
    
    end InlinerAnalyzer
    import InlinerAnalyzer.InlinerMap
    
    
    object InlinerReplacer:
      
      class Copier(resSym: LocalVarSymbol, existingMapping: Map[Symbol, Symbol], thisMapping: Map[InnerSymbol, Path])(using State):
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
            case Return(res) if !currentlyNested =>
              applyResult(res): r2 =>
                Assign(resSym, r2, Break(lblSym))
            case _ => super.applyBlock(b)
        
          override def applyValue(v: Value)(k: Value => Block): Block = v match
            case Value.This(sym) if thisMapping.contains(sym) =>
              thisMapping(sym) match
              case v2: Value => k(v2)
              case _ => super.applyValue(v)(k)
            case _ => super.applyValue(v)(k)

          override def applyPath(p: Path)(k: Path => Block): Block = p match
            case Value.This(sym) if thisMapping.contains(sym) =>
              k(thisMapping(sym))
            case _ => super.applyPath(p)(k)

        def applyBlock(blk: Block) =
          Label(lblSym, false, Copier.apply(blk), _)
      
      class Transformer(m: InlinerMap) extends BlockTransformer(SymbolSubst()):
        
        // The call graph may be cyclic, in which case we break the infinite loop using this map by
        // assuring that the block corresponding to a term symbol may only be transformed once.
        // This map also allows the function block to be optimized on first use before its declaration.
        // Key not in map -> not yet analyzed
        // Key in map but value is None -> the optimized body is being computed
        // Key in map with value -> the function is optimized
        val newFunctionBody = MutMap.empty[TermSymbol, Option[Block]]
        var insideInlineAnnotatedFunction = false
        var insideCrossUnitFunctionBody = false

        def spendInlineFuel(cost: Int): Bool =
          if cost <= 0 then return true
          if remainingInlineFuel < cost then return false
          remainingInlineFuel -= cost
          true

        inline def enterFunBlock[T](inlineAnnot: Bool, inline thunk: => T): T =
          val old = insideInlineAnnotatedFunction
          insideInlineAnnotatedFunction = inlineAnnot
          val res = thunk
          insideInlineAnnotatedFunction = old
          res
        
        inline def enterFunctionBody[T](fun: FunDefn, inline thunk: => T): T =
          val old = insideCrossUnitFunctionBody
          insideCrossUnitFunctionBody = fun.dSym.getState isnt State
          val res = enterFunBlock(fun.inline, thunk)
          insideCrossUnitFunctionBody = old
          res

        def shouldDeferCrossUnitInline(info: InlinerAnalyzer.InlinerFunInfo): Bool =
          insideCrossUnitFunctionBody && (info.defn.dSym.getState isnt State) && !info.defn.inline

        override def applyMainBlock(main: Block): Block =
          super.applyMainBlock(main).flattened
        
        override def applyBlock(blk: Block) =
          blk match
          case Define(defn: FunDefn, rest) if m.get(defn.dSym).exists(_.canBeInlineEliminated) =>
            log(s"Inline elimination: ${defn.dSym}")
            registerChange(s"rm inline-eliminated function ${defn.dSym.showDbg}")
            applyBlock(rest)
          case _ => super.applyBlock(blk)
        
        override def applyFunDefn(fun: FunDefn): FunDefn =
          newFunctionBody.get(fun.dSym) match
            case N =>
              newFunctionBody(fun.dSym) = N
              val newBdy = enterFunctionBody(fun, applyBlock(fun.body))
              newFunctionBody(fun.dSym) = S(newBdy)
              if newBdy is fun.body then fun else
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, newBdy)(fun.configOverride, fun.annotations)
            case S(N) =>
              // The expansion of the function body itself reaches its own definition, which is impossible
              lastWords("Function body contains its own definition.")
            case S(S(blk)) =>
              if blk is fun.body then fun else
              FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, blk)(fun.configOverride, fun.annotations)

        private def inlineCall(
            call: Call,
            callee: TermSymbol,
            argss: NELs[Ls[Arg]],
            thisMapping: => Map[InnerSymbol, Path],
        )(k: Result => Block): Block =
          val info = m(callee)
          if shouldDeferCrossUnitInline(info) || info.isLoopBreaker then
            return super.applyResult(call)(k)
          newFunctionBody.get(callee)
          .getOrElse:
            newFunctionBody(callee) = N
            val newBdy = enterFunctionBody(info.defn, applyBlock(info.defn.body))
            newFunctionBody(callee) = S(newBdy)
            S(newBdy)
          .fold(super.applyResult(call)(k)): blk =>
            val cfg = summon[Config.Inliner]
            val threshold = if insideInlineAnnotatedFunction then cfg.altSmallThreshold else cfg.inlineThreshold
            info.inlineCost(blk, threshold) match
            case N =>
              super.applyResult(call)(k)
            case S(cost) =>
              matchAllArgs(argss, info.defn.params) match
              case N =>
                super.applyResult(call)(k)
              case S(_) if !spendInlineFuel(cost) =>
                super.applyResult(call)(k)
              case S(matchedArgs) =>
                registerChange(s"inline call ${callee.showDbg}")
                log(s"Inline call for ${callee}, with args ${argss}")
                val extraArgss = argss.drop(info.defn.params.length)
                def go(acc: Block => Block, args: List[(VarSymbol, Result)], mapping: Map[Symbol, Symbol]): Block =
                  args match
                  case Nil =>
                    val resSym = TempSymbol(N, "inlinedVal")
                    val copier = Copier(resSym, mapping, thisMapping)
                    val newBlk = copier.applyBlock(blk)
                    if extraArgss.isEmpty then
                      acc(Scoped(Set.single(resSym), newBlk(k(resSym.asSimpleRef))))
                    else
                      acc(Scoped(Set(resSym), newBlk(
                        k(Call(resSym.asSimpleRef, extraArgss.ne_!)(
                          call.metadata.copy(
                            annotations = call.metadata.annotations.filterNot(_ == Annot.TailCall),
                          ))))))
                  case (sym, value) :: argRest =>
                    val newSym = VarSymbol(sym.id)
                    go(acc.assignScoped(newSym, value), argRest, mapping + (sym -> newSym))
                go(blockBuilder, matchedArgs, Map.empty)
        
        override def applyResult(r: Result)(k: Result => Block): Block = r match
          case c @ Call(MethodCallQualifier(qual, ts), argss) if m.contains(ts) && argss.nonEmpty =>
            // `this.method()` calls inside constructors/methods are deliberately left alone:
            // inlining them can bypass runtime checks and resolve forward references too early.
            if qual.isInstanceOf[Value.This] then return super.applyResult(r)(k)
            inlineCall(c, ts, argss,
              ts.owner match
              case S(ownerSym: InnerSymbol) => buildThisMapping(qual, ownerSym)
              case _ => Map.empty,
            )(k)

          case c @ Call(TermSymbolPath(ts), argss) if m.contains(ts) && argss.nonEmpty =>
            inlineCall(c, ts, argss, Map.empty)(k)
          case _ => super.applyResult(r)(k)
      
      def replace(m: InlinerMap, prog: Program): Program =
        Transformer(m).applyProgram(prog)
    
    end InlinerReplacer
    
  end Inliner
  
  
  // ——————————————————————————————————————————————————————————————————————————————————————————— //
  
  
end BlockSimplifier
