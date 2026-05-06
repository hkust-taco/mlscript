package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.{Literal, Tree, Keyword}, utils.*
import Message.MessageContext
import Elaborator.{Ctx, State, ctx}
import codegen.Lowering
import collection.mutable.{Map as MutMap}


class Normalization(lowering: Lowering)(using tl: TL)(using Raise, Ctx, State) extends TermSynthesizer:
  import Normalization.*, Mode.*
  import tl.*

  def reportUnreachableCase[T <: Located](unreachable: Located, subsumedBy: T, when: Bool = true): T =
    if when then warn(
      msg"this case is unreachable" -> unreachable.toLoc,
      msg"because it is subsumed by the branch" -> subsumedBy.toLoc)
    subsumedBy

  extension (these: Split)
    def markAsFallback: Split =
      these.isFallback = true
      these

    def clearFallback: Split =
      these.isFallback = false
      these

    def ++(those: Split): Split =
      if these.isFull then
        log("tail is discarded")
        these
      else (these match
        case Split.Cons(head, tail) => Split.Cons(head, tail ++ those)
        case Split.Let(name, term, tail) => Split.Let(name, term, tail ++ those)
        case Split.Else(_) /* impossible */ | Split.End => those)
  
  extension (lhs: FlatPattern)
    /** Checks if two patterns are the same. */
    def =:=(rhs: FlatPattern): Bool = (lhs, rhs) match
      case (lhs: FlatPattern.ClassLike, rhs: FlatPattern.ClassLike) =>
        lhs.constructor.symbol === rhs.constructor.symbol
      case (FlatPattern.Lit(l1), FlatPattern.Lit(l2)) => l1 === l2
      case (FlatPattern.Tuple(n1, b1), FlatPattern.Tuple(n2, b2)) => n1 === n2 && b1 === b2
      case (FlatPattern.Record(ls1), FlatPattern.Record(ls2)) =>
        ls1.lazyZip(ls2).forall:
          case ((fieldName1, p1), (fieldName2, p2)) =>
            fieldName1 === fieldName2 && p1 === p2
      case (_: FlatPattern.ClassLike, _) | (_: FlatPattern.Lit, _) |
        (_: FlatPattern.Tuple, _) | (_: FlatPattern.Record, _) => false
    /** Checks if `lhs` can be subsumed under `rhs`. */
    def <:<(rhs: FlatPattern): Bool = compareCasePattern(lhs, rhs)
    /** If the pattern is a class-like pattern, override its `refined` flag. */
    def markAsRefined: Unit = lhs match
      case lhs: FlatPattern.ClassLike => lhs.refined = true
      case _ => ()
  
  extension (lhs: FlatPattern.Record)
    /** reduces the record pattern `lhs` assuming we have matched `rhs`.
      * It removes field matches that may now be unnecessary
      */
    infix def assuming(rhs: FlatPattern): FlatPattern.Record = rhs match
      case FlatPattern.Record(rhsEntries) =>
        val filteredEntries = lhs.entries.filter:
          (fieldName1, _) => rhsEntries.forall { (fieldName2, _) => !(fieldName1 === fieldName2)}
        FlatPattern.Record(filteredEntries)
      case rhs: FlatPattern.ClassLike => rhs.constructor.symbol.flatMap(_.asCls) match
        case S(cls: ClassSymbol) => cls.defn match
          case S(ClassDef.Parameterized(params = paramList)) =>
            val filteredEntries = lhs.entries.filter:
              (fieldName1, _) => paramList.params.forall { (param:Param) => !(fieldName1 === param.sym.id)}
            FlatPattern.Record(filteredEntries)
          case S(_) | N => lhs
        case S(_) | N => lhs
      case _ => lhs

  inline def apply(split: Split): Split = normalize(split)(using VarSet())
  
  /**
    * Normalize core abstract syntax to MLscript syntax.
    *
    * @param split the split to normalize
    * @return the normalized term
    */ 
  private def normalize(split: Split)(using vs: VarSet): Split = trace(
    pre = s"normalize <<< ${split.prettyPrint}",
    post = (res: Split) => "normalize >>> " + res.prettyPrint,
  ):
    normalizeImpl(split)
  
  def normalizeImpl(split: Split)(using vs: VarSet): Split = split match
    case Split.Cons(Branch(scrutinee, pattern, consequent), alternative) =>
      log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
      val whenTrue = normalize(specialize(consequent ++ alternative.duplicate, +, scrutinee, pattern))
      val whenFalse = normalizeImpl(specialize(alternative, -, scrutinee, pattern).clearFallback)
      Branch(scrutinee, pattern, whenTrue) ~: whenFalse
    case Split.Let(v, _, tail) if vs has v =>
      log(s"LET: SKIP already declared scrutinee $v")
      normalizeImpl(tail)
    case Split.Let(v, rhs, tail) =>
      log(s"LET: $v")
      Split.Let(v, rhs, normalizeImpl(tail)(using vs + v))
    case split @ Split.Else(default) =>
      log(s"DFLT: ${default.showDbg}")
      split
    case Split.End => Split.End
  
  /**
    * Specialize `split` with the assumption that `scrutinee` matches `pattern`.
    *
    * In mode `+` (positive), keeps branches consistent with the assumption:
    *   - Case 1.1.1: Same pattern (`=:=`) → merge continuation and tail via alias bindings.
    *   - Case 1.1.2: Branch pattern is more specific (`thatPattern <:< pattern`) → keep as-is,
    *     mark the specializing pattern as refined, and recurse into the tail so remaining
    *     branches on the same scrutinee are simplified with the known assumption.
    *   - Case 1.1.3: Branch is a fallback → skip to tail.
    *   - Case 1.1.4: Branch is a record → simplify fields already matched by the assumption.
    *   - Case 1.1.5: Specializing pattern is more specific (`pattern <:< thatPattern`) → keep as-is
    *     (the branch always matches when the assumption holds).
    *   - Case 1.1.6: Patterns are unrelated — if provably disjoint (e.g., different literals,
    *     sibling classes under single inheritance), skip; otherwise keep the branch to support
    *     conjunction patterns like `A & B`.
    *
    * In mode `-` (negative), removes branches that the assumption makes unreachable:
    *   - Case 1.2.1: Branch pattern equals or is subsumed by the assumption → remove.
    *   - Case 1.2.2: Unrelated → keep, recurse into tail.
    *
    * Case 2: Different scrutinee → recurse into both continuation and tail.
    */
  private def specialize(
      split: Split,
      mode: Mode,
      scrutinee: Term.Ref,
      pattern: FlatPattern
  )(using VarSet): Split = trace(
    pre = s"S$mode <<< ${scrutinee.showDbg} is ${pattern.showDbg} : ${split.prettyPrint}",
    post = (r: Split) => s"S$mode >>> ${r.prettyPrint}"
  ):
    def rec(split: Split)(using mode: Mode, vs: VarSet): Split = split match
      case Split.End => log("CASE Nil"); split
      case Split.Else(_) => log("CASE Else"); split
      case split @ Split.Let(sym, _, tail) =>
        log(s"CASE Let ${sym}")
        split.copy(tail = rec(tail))
      case split @ Split.Cons(head @ Branch(thatScrutinee, thatPattern, continuation), tail) =>
        log(s"CASE Cons ${head.showDbg}")
        if scrutinee === thatScrutinee then mode match
          case + =>
            log(s"Case 1.1: $scrutinee === $thatScrutinee")
            if thatPattern =:= pattern then
              log(s"Case 1.1.1: $pattern =:= $thatPattern")
              aliasBindings(pattern, thatPattern)(rec(continuation) ++ rec(tail))
            else if thatPattern <:< pattern then
              log(s"Case 1.1.2: $pattern <:< $thatPattern")
              pattern.markAsRefined; split.copy(tail = rec(tail))
            else if split.isFallback then
              log(s"Case 1.1.3: $pattern is unrelated with $thatPattern")
              rec(tail)
            else thatPattern match
            case thatPattern: FlatPattern.Record =>
              log(s"Case 1.1.4: $thatPattern is a record")
              // we can use information if pattern is itself a record, or if it is a constructor with arguments
              val simplifiedRecord = thatPattern assuming pattern
              if simplifiedRecord.entries.isEmpty then
                tail
              else
                Split.Cons(Branch(thatScrutinee, simplifiedRecord, continuation), tail)
            case _ =>
              if pattern <:< thatPattern then
                // TODO: the warning will be useful when we have inheritance information
                // raiseDesugaringWarning(
                //   msg"the pattern always matches" -> thatPattern.toLoc,
                //   msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                //   msg"which is a subtype of ${thatPattern.toString}" -> (pattern match {
                //     case Pattern.Class(cls, _, _) => cls.toLoc
                //     case _ => thatPattern.toLoc
                //   }))
                log(s"case 1.1.5: $pattern <:< $thatPattern")
                split
              else
                if areProvablyDisjoint(pattern, thatPattern) then
                  log(s"Case 1.1.6: $pattern and $thatPattern are provably disjoint")
                  rec(tail)
                else
                  // When patterns are not provably disjoint, we cannot assume
                  // the scrutinee can't match both (e.g., conjunction patterns
                  // like `A & B`). Keep the branch.
                  log(s"Case 1.1.6: $pattern and $thatPattern are not provably disjoint")
                  head.copy(continuation = rec(continuation)) ~: rec(tail)
          case - =>
            log(s"Case 1.2: $scrutinee === $thatScrutinee")
            if thatPattern =:= pattern || thatPattern <:< pattern then
              log(s"Case 1.2.1: $pattern =:= (or <:<) $thatPattern")
              rec(tail)
            else
              log(s"Case 1.2.2: $pattern are unrelated to $thatPattern")
              split.copy(tail = rec(tail))
        else
          log(s"Case 2: $scrutinee =/= $thatScrutinee")
          head.copy(continuation = rec(continuation)) ~: rec(tail)
    end rec
    rec(split)(using mode, summon)
  
  private def aliasBindings(p: FlatPattern, q: FlatPattern): Split => Split = (p, q) match
    case (FlatPattern.ClassLike(_, _, S(ss1), _), FlatPattern.ClassLike(_, _, S(ss2), _)) =>
      ss1.iterator.zip(ss2.iterator).foldLeft(identity[Split]):
        case (acc, (l, r)) if l._1 === r._1 => acc
        case (acc, (l, r)) => innermost => Split.Let(r._1, l._1.safeRef, acc(innermost))
    case (_, _) => identity
  
  import codegen.*, lowering.{term_nonTail, subTerm_nonTail, unreachableFn}
  
  /** Collect terms that appear in multiple `Split.Else` branches. We will share
   *  the corresponding blocks to avoid code duplication. */
  private def createLabelsForDuplicatedBranches(split: Split)(using config: Config): Labels =
    val counts: MutMap[Term, (order: Int, count: Int)] = MutMap.empty
    var fallThroughCount = 0
    def rec(s: Split): Unit = s match
      case Split.End => fallThroughCount += 1
      case Split.Else(els) => counts.updateWith(els):
        case S((n, count)) => S((n, count + 1))
        case N => S((counts.size + 1, 1))
      case Split.Let(_, _, tail) => rec(tail)
      case Split.Cons(Branch(_, _, cons), tail) => rec(cons); rec(tail)
    rec(split)
    val consequents = config.patMatConsequentSharingThreshold match
      case S(threshold) =>
        counts.iterator.filter(kv =>
          kv._2.count > 1 && kv._2.count * kv._1.size > threshold).toSeq.sortBy(_._2.order).zipWithIndex.map:
          case ((term, _), i) => (term, LabelSymbol(S(term), s"split_${i + 1}$$"))
        .toList
      case N => Nil
    val matchError = if fallThroughCount > 1 then S(LabelSymbol(N, s"split_default$$")) else N
    Labels(consequents, matchError)
  
  private def lowerSplit
      (split: Split, cont: Result => Block)
      (using labels: Labels, form: IfLikeForm)
      (using LoweringCtx)
      : Block = split match
    case Split.Let(sym, trm, tl) =>
      LoweringCtx.loweringCtx.collectScopedSym(sym)
      term_nonTail(trm): r =>
        Assign(sym, r, lowerSplit(tl, cont))
    case Split.Cons(Branch(scrut, pat, tail), restSplit) =>
      subTerm_nonTail(scrut): sr =>
        tl.log(s"Binding scrut $scrut to $sr (${summon[LoweringCtx].map})") 
        def mkMatch(cse: Case -> Block) = Match(sr, cse :: Nil,
            S(lowerSplit(restSplit, cont)),
            End()
          )
        pat match
          case FlatPattern.Lit(lit) => mkMatch(Case.Lit(lit) -> lowerSplit(tail, cont))
          case FlatPattern.ClassLike(ctor, symbol, argsOpt, _refined) =>
            for args <- argsOpt; (arg, _) <- args do LoweringCtx.loweringCtx.collectScopedSym(arg)
            /** Make a continuation that creates the match. */
            def k(ctorSym: ClassLikeSymbol, clsParams: Ls[TermSymbol])(st: Path): Block =
              val args = argsOpt.map(_.map(_._1)).getOrElse(Nil)
              // Normalization should reject cases where the user provides
              // more sub-patterns than there are actual class parameters.
              assert(argsOpt.isEmpty || args.length <= clsParams.length, (argsOpt, clsParams))
              def mkArgs(args: Ls[TermSymbol -> BlockLocalSymbol])(using LoweringCtx): Case -> Block = args match
                case Nil =>
                  Case.Cls(ctorSym, st) -> lowerSplit(tail, cont)
                case (param, arg) :: args =>
                  val (cse, blk) = mkArgs(args)
                  (cse, Assign(arg, Select(sr, new Tree.Ident(param.id.name).withLocOf(arg))(S(param)), blk))
              mkMatch(mkArgs(clsParams.iterator.zip(args).toList))
            symbol match
              case cls: ClassSymbol if ctx.builtins.virtualClasses contains cls =>
                // [invariant:0] Some classes (e.g., `Int`) from `Prelude` do
                // not exist at runtime. If we do lowering on `trm`, backends
                // (e.g., `JSBuilder`) will not be able to handle the corresponding selections.
                // In this case the second parameter of `Case.Cls` will not be used.
                // So we do not elaborate `ctor` when the `cls` is virtual
                // and use it `Predef.unreachable` here.
                k(cls, Nil)(unreachableFn)
              case cls: ClassSymbol =>
                subTerm_nonTail(ctor)(k(cls,
                  cls.tree.clsParams.headOption.getOrElse(Nil) // FIXME? case when there are only aux parameter lists
                  ))
              case mod: ModuleOrObjectSymbol =>
                subTerm_nonTail(ctor)(k(mod, Nil))
          case FlatPattern.Tuple(len, inf) => mkMatch(Case.Tup(len, inf) -> lowerSplit(tail, cont))
          case FlatPattern.Record(entries) =>
            for (_, s) <- entries do LoweringCtx.loweringCtx.collectScopedSym(s)
            val objectSym = ctx.builtins.Object
            mkMatch( // checking that we have an object
              Case.Cls(objectSym, Value.Ref(BuiltinSymbol(objectSym.nme, false, false, true, false))),
              entries.foldRight(lowerSplit(tail, cont)):
                case ((fieldName, fieldSymbol), blk) =>
                  mkMatch(
                    Case.Field(fieldName, safe = true), // we know we have an object, no need to check again
                    Assign(fieldSymbol, Select(sr, fieldName)(N), blk)
                  )
            )
    case Split.Else(els) => labels.get(els) match
      case S(label) => Break(label)
      case N => term_nonTail(els, inStmtPos = form.isImperative)(cont)
    case Split.End =>
      // * See comment [comment:1] above
      if form is IfLikeForm.While then End()
      else labels.matchError.fold(throwMatchErrorBlock)(Break(_))
  
  /**
    * Make a block that throws the match error. We might add the information of
    * match failure in the future.
    */
  private def throwMatchErrorBlock =
    Throw(Instantiate(mut = false, Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Error"))(S(ctx.builtins.Error)),
        (Value.Lit(syntax.Tree.StrLit("match error")).asArg :: Nil) :: Nil)) // TODO add failed-match scrutinee info
  
  import syntax.Keyword.{`if`, `while`}
  
  def apply(t: Term.IfLike)(k: Result => Block)(using config: Config)(using LoweringCtx): Block =
    val newSplit = t.split.getExpandedSplit
    scoped("ucs:desugared"):
      log(s"Split with nested patterns:\n${t.split.prettyPrint(t.kw)}")
      log(s"Expanded split with flattened patterns:\n${newSplit.prettyPrint}")
    this(newSplit, t.form, S(t), k)
  
  def apply(t: Term.SynthIf)(k: Result => Block)(using Config, LoweringCtx): Block =
    this(t.split, IfLikeForm.ReturningIf, S(t), k)
  
  def apply(split: Split)(k: Result => Block)(using Config, LoweringCtx): Block =
    this(split, IfLikeForm.ReturningIf, N, k)
  
  private def apply(inputSplit: Split, form: IfLikeForm, t: Opt[Term], k: Result => Block)(using cfg: Config, outerCtx: LoweringCtx) =
    // if it's `while`, we always make sure that loop bodies are proper nested scoped
    // see https://github.com/hkust-taco/mlscript/pull/356#discussion_r2588412258
    val useNestedScoped = form is IfLikeForm.While
    (if useNestedScoped then LoweringCtx.nestScoped else outerCtx).givenIn:
      var usesResTmp = false
      // The symbol of the temporary variable for the result of the `if`-like term.
      // It will be created in one of the following situations.
      // 1. The continuation `k` is not a tail operation.
      // 2. There are shared consequents in the `if`-like term.
      // 3. The term is a `while` and the result is used.
      lazy val l =
        usesResTmp = true
        val res = new TempSymbol(t)
        outerCtx.collectScopedSym(res)
        res
      // The symbol for the loop label if the term is a `while`.
      lazy val loopLabel = new LabelSymbol(t)
      lazy val f =
        val res = new BlockMemberSymbol("while", Nil, false)
        outerCtx.collectScopedSym(res)
        res
      lazy val tSym = TermSymbol.fromFunBms(f, N)
      val normalized = tl.scoped("ucs:normalize"):
        normalize(inputSplit)(using VarSet())
      tl.scoped("ucs:normalized"):
        tl.log(s"Normalized:\n${normalized.prettyPrint}")
      // Collect consequents that are shared in more than one branch.
      given labels: Labels = createLabelsForDuplicatedBranches(normalized)
      lazy val rootBreakLabel = new LabelSymbol(N, "split_root$")
      lazy val breakRoot = if (k is Ret) || (k is Thrw) then k else (r: Result) => Assign(l, r, Break(rootBreakLabel))
      lazy val assignResult = (r: Result) =>
        form match
        case IfLikeForm.ReturningIf => if (k is Ret) || (k is Thrw) then k(r) else Assign(l, r, End())
        case IfLikeForm.ImperativeIf => Assign.discard(r, End())
        case IfLikeForm.While => Assign(State.noSymbol, r, loopCont)
      // NOTE: `shouldRewriteWhile` is not the same as `config.rewriteWhileLoops`
      // as shouldRewriteWhile is always true when effect handler lowering is on
      lazy val loopCont = if config.shouldRewriteWhile
        then Return(Call(Value.Ref(f, S(tSym)), Nil ne_:: Nil)(true, true, false), false)
        else Continue(loopLabel)
      val cont =
        form match
        case IfLikeForm.While =>
          // * Note that if the term is a `while`, the continuation `cont` corresponds to
          // * what happens after each specified branch terminates,
          // * ie, continuation to the next loop iteration.
          (r: Result) => Assign.discard(r, loopCont)
        case IfLikeForm.ImperativeIf =>
          (r: Result) => Assign.discard(r, End())
        case IfLikeForm.ReturningIf =>
          if labels.isEmpty then
            if k.isInstanceOf[TailOp] then
              // If there are no shared consequents and the continuation is a tail
              // operation, we can call it directly.
              k
            else
              // Otherwise, if the continuation is not a tail operation, we should
              // save the result in a temporary variable and call the continuation
              // in the end.
              assignResult
          else
            // When there are shared consequents, we are forced to save the result
            // in the temporary variable nevertheless. Note that `cont` only gets
            // called for non-shared consequents, so we should break to the end of
            // the entire split after the assignment.
            breakRoot
      // When we are not rewriting while loops to tail-recursive functions,
      // whether we need a `Break` to exit the loop at the end of the main block
      // depends on whether there are shared consequents,
      // as shared consequents will be lifted out of the main block and added as separate labelled blocks
      // to jump to, so we cannot simply fall through the end of the main block to exit the loop.
      // Note that when there is a `default` branch and we're in a loop,
      // the semantics of that default branch is to always `continue` the loop,
      // so we don't need to break out of the loop at the end of the main block as well.
      val needsBreakToExitLoop =
        (form is IfLikeForm.While) && !config.shouldRewriteWhile && labels.consequents.nonEmpty //&& labels.default.isEmpty
      // The main block contains the lowered split, where each shared consequent
      // is replaced with a `Break` to the corresponding label.
      val mainBlock =
        val innermostBlock =
          given IfLikeForm = form
          if needsBreakToExitLoop
          then Begin(lowerSplit(normalized, cont), Break(rootBreakLabel))
          else lowerSplit(normalized, cont)
        // Wrap the main block in a labelled block for each shared consequent. The
        // `rest` of each `Label` is the lowered consequent plus a `Break` to the
        // end of the entire `if` term. Otherwise, it will fall through to the outer
        // consequent, which is the wrong semantics.
        val innerBlock: Block = labels.consequents match
          case Nil => innermostBlock
          case all @ (head :: tail) =>
            def wrap(consequents: Ls[(Term, LabelSymbol)]): Block =
              consequents.foldRight(innermostBlock):
                case ((term, label), innerBlock) =>
                  Label(label, false, innerBlock,
                    if form is IfLikeForm.While
                    then term_nonTail(term)(r => Assign.discard(r, loopCont))
                    else term_nonTail(term)(breakRoot))
            // There is no need to generate `break` for the outermost split
            // if we're not generating an additional matchError block at the end.
            if labels.matchError.isEmpty then
              Label(head._2, false, wrap(tail), term_nonTail(head._1)(assignResult))
            else wrap(all)
        if form is IfLikeForm.While
        then if needsBreakToExitLoop
          then Begin(innerBlock, Break(rootBreakLabel))
          else innerBlock
        else labels.matchError match
          case S(label) => Label(label, false, innerBlock, throwMatchErrorBlock)
          case N => innerBlock
      // If there are shared consequents, we need a wrap the entire block in a
      // `Label` so that `Break`s in the shared consequents can jump to the end.
      val body =
        Scoped(
          if useNestedScoped then LoweringCtx.loweringCtx.getCollectedSym else Set.empty,
          if labels.isEmpty && !needsBreakToExitLoop
          then mainBlock
          else Label(rootBreakLabel, false, mainBlock, End()))
      // Embed the `body` into `Label` if the term is a `while`.
      lazy val rest = if usesResTmp then k(Value.Ref(l)) else k(lowering.unit)
      val block =
        if form === IfLikeForm.While then
          // NOTE: `shouldRewriteWhile` is not the same as `config.rewriteWhileLoops`
          // as shouldRewriteWhile is always true when effect handler lowering is on
          if config.shouldRewriteWhile then
            val loopResult = TempSymbol(N)
            val isReturned = TempSymbol(N)
            outerCtx.collectScopedSym(loopResult)
            outerCtx.collectScopedSym(isReturned)
            val loopEnd: Path =
              Select(Value.Ref(State.runtimeSymbol), Tree.Ident("LoopEnd"))(S(State.loopEndSymbol))
            val blk = blockBuilder
              .define(FunDefn(N, f, tSym, PlainParamList(Nil) :: Nil, Begin(body, Return(loopEnd, false)))(configOverride = N, annotations = Nil))
              .assign(loopResult, Call(Value.Ref(f, S(tSym)), Nil ne_:: Nil)(true, true, false))
            if summon[LoweringCtx].mayRet then
              blk
                .assign(isReturned, Call(Value.Ref(State.builtinOpsMap("!==")),
                  (loopResult.asPath.asArg :: loopEnd.asArg :: Nil) ne_:: Nil)(true, false, false))
                .ifthen(Value.Ref(isReturned), Case.Lit(Tree.BoolLit(true)),
                  Return(Value.Ref(loopResult), false),
                  N
                )
                .rest(rest)
            else
              blk.rest(rest)
          else
            Begin(Label(loopLabel, true, body, End()), rest)
        else if labels.isEmpty && k.isInstanceOf[TailOp]
          && !form.isImperative
            // * ^ Generated imperative `if` branches do not always yield a value, so if we removed this,
            // * we would sometimes return `undefined`.
            // * (This could be improved; currently, we fail to preserve the tail call in `fun f() = if false do f()`.)
          then
            body
        else
          Begin(body, rest)
      scoped("ucs:lowered"):
        log(s"Lowered:\n${block.showAsTree}")
      block
end Normalization

object Normalization:
  /** This contains the labels for duplicated consequents and the default
   *  branch which throws match errors. */
  private class Labels(val consequents: Ls[(Term, LabelSymbol)], val matchError: Opt[LabelSymbol]):
    private val map = consequents.toMap
    
    inline def isEmpty: Bool = consequents.isEmpty && matchError.isEmpty
    
    inline def get(term: Term): Opt[LabelSymbol] = map.get(term)
  
  /**
    * Subtyping relations used in normalization and coverage checking.
    */
  def compareCasePattern(lhs: FlatPattern, rhs: FlatPattern)(using ctx: Elaborator.Ctx): Bool =
    import FlatPattern.*, ctx.builtins as blt
    (lhs, rhs) match
    // `Object` is the supertype of all (non-virtual) classes and modules.
    case (ClassLike(_, cs: ClassSymbol, _, _), ClassLike(symbol = blt.`Object`))
        if !ctx.builtins.virtualClasses.contains(cs) => true
    // Class and module are subtypes of `Object`.
    case (ClassLike(_, cs: ModuleOrObjectSymbol, _, _), ClassLike(symbol = blt.`Object`)) => true
    case (Tuple(n1, false), Tuple(n2, false)) if n1 === n2 => true
    case (Tuple(n1, _), Tuple(n2, true)) if n2 <= n1 => true
    // Note: We don't make Int31 compatible with Num, since Int31 needs to know how it should be
    // sign-extended in order to convert into a Num.
    case (ClassLike(symbol = blt.`Int`), ClassLike(symbol = blt.`Num`)) => true
    // TODO(Derppening): Do we limit IntLit to (1 << 31) - 1 for `Int31`?
    case (Lit(Tree.IntLit(_)), ClassLike(symbol = blt.`Int` | blt.`Int31` | blt.`Num`)) => true
    case (Lit(Tree.StrLit(_)), ClassLike(symbol = blt.`Str`)) => true
    case (Lit(Tree.DecLit(_)), ClassLike(symbol = blt.`Num`)) => true
    case (Lit(Tree.BoolLit(_)), ClassLike(symbol = blt.`Bool`)) => true
    case (Record(entries1), Record(entries2)) =>
      entries1.forall { (fieldName1, _) => entries2.exists { (fieldName2, _) => fieldName1 === fieldName2 } }
    case (Record(entries), rhs: ClassLike) =>
      val clsParams = rhs.constructor.symbol.flatMap(_.asCls) match
        case S(symbol) => symbol.defn match
          case S(ClassDef.Parameterized(params = paramList)) => paramList.params
          case S(_) | N => Nil
        case (S(_) | N) => Nil
      entries.forall { (fieldName, _) => clsParams.exists {
        case Param(flags = FldFlags(isVal = isVal), sym = sym) => isVal && fieldName === sym.id
      }}
    // Check user-defined class hierarchy via extends clauses.
    case (ClassLike(_, lhsSym, _, _), ClassLike(_, rhsSym, _, _)) =>
      isSubclassOf(lhsSym, rhsSym)
    case (_: FlatPattern, _: FlatPattern) => false
  
  /**
    * Check if two patterns are provably disjoint, i.e., no value can match both.
    * This is used to safely eliminate branches during specialization.
    * Returns `true` for clear-cut cases (e.g., different literals,
    * incompatible tuple sizes, sibling classes under single inheritance).
    */
  def areProvablyDisjoint(lhs: FlatPattern, rhs: FlatPattern)(using ctx: Elaborator.Ctx): Bool =
    import FlatPattern.*
    (lhs, rhs) match
    case (Lit(l1), Lit(l2)) => !(l1 === l2)
    case (Tuple(n1, false), Tuple(n2, false)) => n1 =/= n2
    case (Tuple(n1, true), Tuple(n2, false)) => n2 < n1
    case (Tuple(n1, false), Tuple(n2, true)) => n1 < n2
    case (Lit(_), _: ClassLike) => !compareCasePattern(lhs, rhs)
    case (_: ClassLike, Lit(_)) => !compareCasePattern(rhs, lhs)
    case (Lit(_), Tuple(_, _)) | (Tuple(_, _), Lit(_)) => true
    case (Record(_), Lit(_)) | (Lit(_), Record(_)) => true
    case (Record(_), Tuple(_, _)) | (Tuple(_, _), Record(_)) => true
    // Under the single-inheritance restriction, two classes where neither is a
    // subclass of the other are provably disjoint. When we add matchable
    // class-like things with multiple inheritance (e.g., interfaces), this check
    // will need to be refined.
    case (ClassLike(_, lhsSym, _, _), ClassLike(_, rhsSym, _, _)) =>
      !isSubclassOf(lhsSym, rhsSym) && !isSubclassOf(rhsSym, lhsSym)
    case _ => false
  
  /** Get the parent class-like symbol from the extends clause of a class or module. */
  private def getParentClassLikeSymbol(sym: ClassSymbol | ModuleOrObjectSymbol)
      : Opt[ClassSymbol | ModuleOrObjectSymbol] =
    val ext: Opt[Term.New] = sym match
      case cls: ClassSymbol => cls.defn.flatMap(_.ext)
      case mod: ModuleOrObjectSymbol => mod.defn.flatMap(_.ext)
    ext.flatMap(nw => nw.cls.symbol.flatMap(_.asClsOrMod))
  
  /** Check if `child` is a subclass of `parent` by traversing the class hierarchy.
    * Uses a visited set to avoid infinite loops in case of cyclic inheritance. */
  private def isSubclassOf(
      child: ClassSymbol | ModuleOrObjectSymbol,
      parent: ClassSymbol | ModuleOrObjectSymbol
  ): Bool =
    def go(sym: ClassSymbol | ModuleOrObjectSymbol,
        visited: Set[ClassSymbol | ModuleOrObjectSymbol]): Bool =
      !visited.contains(sym) && (getParentClassLikeSymbol(sym) match
        case S(parentSym) =>
          parentSym === parent || go(parentSym, visited + sym)
        case N => false)
    go(child, Set.empty)

  final case class VarSet(declared: Set[BlockLocalSymbol]):
    def +(nme: BlockLocalSymbol): VarSet = copy(declared + nme)
    infix def has(nme: BlockLocalSymbol): Bool = declared.contains(nme)
    def showDbg: Str = declared.iterator.mkString("{", ", ", "}")

  object VarSet:
    def apply(): VarSet = VarSet(Set())

  /** Specialization mode */
  enum Mode:
    case +
    case -
