package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.{Literal, Tree, Keyword}, utils.*
import Message.MessageContext
import Elaborator.{Ctx, State, ctx}
import codegen.Lowering


class Normalization(lowering: Lowering)(using tl: TL)(using Raise, Ctx, State, Config) extends TermSynthesizer:
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
        case Split.Else(_) => softAssert(false); those
        case Split.End => those
        case Split.LetSplit(sym, tail) => Split.LetSplit(sym, tail ++ those)
        case Split.UseSplit(_) => these) // UseSplit is terminal; fullness determined by referenced body
  
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

  inline def apply(split: Split): Split =
    given SpecializedSplitCtx = SpecializedSplitCtx()
    val (normalized, refs) = normalize(split)(using VarSet(), JoinPointCtx.empty)
    bindSpecializedJoinPoints(normalized, refs)

  /**
    * Normalize a split by specializing branches that test the same scrutinee
    * and introducing join points (`LetSplit`/`UseSplit`) to share duplicated
    * alternatives.
    *
    * @param split the split to normalize
    * @return a pair of (1) the normalized split and (2) the set of `SplitSymbol`s
    *         whose `UseSplit` references survive in the result but whose `LetSplit`
    *         bindings have not yet been placed — these are propagated upward so
    *         that the caller (an enclosing `normalizeImpl`) can place the
    *         `LetSplit` at the lowest common ancestor.
    */
  private def normalize(split: Split)(using vs: VarSet, jpctx: JoinPointCtx, spctx: SpecializedSplitCtx): (Split, Set[SplitSymbol]) = trace(
    pre = s"normalize <<< ${split.prettyPrint}",
    post = (res: (Split, Set[SplitSymbol])) => "normalize >>> " + res._1.prettyPrint,
  ):
    normalizeImpl(split)

  private def shouldShareJoinPoint(body: Split, refCount: Int): Bool =
    refCount > 1 && (config.patMatConsequentSharingThreshold match
      case S(threshold) => body.size * refCount > threshold
      case N => false)

  private def bindSpecializedJoinPoints(split: Split, refs: Set[SplitSymbol])(using spctx: SpecializedSplitCtx): Split =
    refs.iterator.filter(spctx.contains).foldLeft(split):
      case (acc, sym) =>
        val refCount = acc.countUseSplit(sym)
        if shouldShareJoinPoint(sym.body, refCount) then
          Split.LetSplit(sym, acc)
        else
          inlineUseSplit(acc, sym, sym.body)
  
  extension (split: Split)
    /** Check if any branch in the split tests the given scrutinee. */
    private def referencesScrutinee(scrutinee: Term.Ref): Bool = split match
      case Split.Cons(Branch(thatScrutinee, _, continuation), tail) =>
        (scrutinee === thatScrutinee) || continuation.referencesScrutinee(scrutinee) || tail.referencesScrutinee(scrutinee)
      case Split.Let(_, _, tail) => tail.referencesScrutinee(scrutinee)
      case Split.Else(_) | Split.End => false
      case Split.LetSplit(_, tail) => tail.referencesScrutinee(scrutinee)
      case Split.UseSplit(_) => false

    /** Check if a split is trivial (not worth creating a join point for). */
    private def isTrivial: Bool = split match
      case Split.End => true
      case Split.UseSplit(_) => true
      case _ => false

    /** Count the number of `UseSplit(sym)` references in `split`. */
    private def countUseSplit(sym: SplitSymbol): Int = split match
      case Split.Cons(Branch(_, _, cons), tail) =>
        cons.countUseSplit(sym) + tail.countUseSplit(sym)
      case Split.Let(_, _, tail) => tail.countUseSplit(sym)
      case Split.Else(_) | Split.End => 0
      case Split.LetSplit(_, tail) => tail.countUseSplit(sym)
      case Split.UseSplit(s) => if s eq sym then 1 else 0

    /** Whether every leaf of `split` unconditionally transfers control away
      * (no fall-through). `End` compiles to `throw`, explicit `return`/`throw`
      * terms are abortive, and `UseSplit` compiles to a `Break`. */
    private def alwaysTerminates: Bool = split match
      case Split.End => true
      case Split.Else(t) => t match
        case _: Term.Ret | _: Term.Throw => true
        case _ => false
      case Split.Cons(Branch(_, _, cons), tail) =>
        cons.alwaysTerminates && tail.alwaysTerminates
      case Split.Let(_, _, tail) => tail.alwaysTerminates
      case Split.LetSplit(_, tail) => tail.alwaysTerminates
      case Split.UseSplit(_) => true

  /** Replace all `UseSplit(sym)` references in `split` with a duplicate of `body`. */
  private def inlineUseSplit(split: Split, sym: SplitSymbol, body: Split): Split = split match
    case Split.Cons(Branch(scrut, pat, cons), tail) =>
      Split.Cons(Branch(scrut, pat, inlineUseSplit(cons, sym, body)), inlineUseSplit(tail, sym, body))
    case Split.Let(v, rhs, tail) => Split.Let(v, rhs, inlineUseSplit(tail, sym, body))
    case Split.Else(_) | Split.End => split
    case Split.LetSplit(s, tail) => Split.LetSplit(s, inlineUseSplit(tail, sym, body))
    case Split.UseSplit(s) => if s eq sym then body.duplicate else split

  /** Workhorse of `normalize`. Returns the same pair: the normalized split
    * and the set of unbound `SplitSymbol`s whose `LetSplit` placement is
    * deferred to an ancestor. */
  private def normalizeImpl(split: Split)(using vs: VarSet, jpctx: JoinPointCtx, spctx: SpecializedSplitCtx): (Split, Set[SplitSymbol]) = split match
    case Split.Cons(Branch(scrutinee, pattern, consequent), alternative) =>
      log(s"MATCH: ${scrutinee.showDbg} is ${pattern.showDbg}")
      if alternative.isTrivial || alternative.referencesScrutinee(scrutinee) then
        // The alternative is trivial (End or UseSplit — no code worth sharing),
        // or it references the same scrutinee (so positive and negative
        // specialization may transform it differently on each side, making
        // sharing unsound). Duplicate and specialize separately.
        // TODO: detect when both specializations agree and share even here.
        val positiveSplit = consequent ++ alternative.duplicate
        val (whenTrue, trueRefs) = normalize(specialize(positiveSplit, +, scrutinee, pattern).getOrElse(positiveSplit))
        val negativeSplit = alternative
        val (whenFalse, falseRefs) = normalizeImpl(specialize(negativeSplit, -, scrutinee, pattern).getOrElse(negativeSplit).clearFallback)
        (Branch(scrutinee, pattern, whenTrue) ~: whenFalse, trueRefs | falseRefs)
      else
        // The alternative doesn't reference the same scrutinee, so specialization
        // is a no-op on it in both modes. Create a join point symbol wrapping
        // the normalized alternative; append UseSplit as a placeholder fallback
        // in the consequent, then check whether specialization + normalization
        // kept or discarded it.
        val (normalizedAlt, _) = normalize(alternative)(using vs, JoinPointCtx.empty)
        val sym = new SplitSymbol(normalizedAlt, "σ")
        val useSplit = Split.UseSplit(sym)
        val combinedSplit = consequent ++ useSplit
        val (whenTrue, trueRefs) = normalize(specialize(combinedSplit, +, scrutinee, pattern).getOrElse(combinedSplit))(using vs, jpctx + sym)
        if trueRefs.contains(sym) then
          // The UseSplit survived in the true branch, meaning the alternative
          // is reachable from both sides. Count the surviving references and
          // decide whether sharing via LetSplit is worthwhile: only share when
          // the alternative is referenced more than once AND it's large enough
          // to be worth a join point, per the configured threshold.
          val refCount = whenTrue.countUseSplit(sym)
          val shouldShare = shouldShareJoinPoint(normalizedAlt, refCount)
          if shouldShare then
            (Split.LetSplit(sym, Branch(scrutinee, pattern, whenTrue) ~: useSplit), trueRefs - sym)
          else
            // Either only a single reference survives (no real sharing) or the
            // alternative is too small to justify a join point — inline all
            // UseSplit references back into the true branch.
            val inlinedTrue = inlineUseSplit(whenTrue, sym, normalizedAlt)
            (Branch(scrutinee, pattern, inlinedTrue) ~: normalizedAlt, trueRefs - sym)
        else
          // The consequent was exhaustive after specialization, so the UseSplit
          // was discarded. No sharing needed — use the alternative directly
          // as the false branch.
          (Branch(scrutinee, pattern, whenTrue) ~: normalizedAlt, trueRefs)
    case Split.Let(v, _, tail) if vs has v =>
      log(s"LET: SKIP already declared scrutinee $v")
      normalizeImpl(tail)
    case Split.Let(v, rhs, tail) =>
      log(s"LET: $v")
      val (normalizedTail, refs) = normalizeImpl(tail)(using vs + v, jpctx)
      (Split.Let(v, rhs, normalizedTail), refs)
    case split @ Split.Else(default) =>
      log(s"DFLT: ${default.showDbg}")
      (split, Set.empty)
    case Split.End => (Split.End, Set.empty)
    case Split.LetSplit(sym, tail) =>
      val (normalizedTail, refs) = normalizeImpl(tail)
      (Split.LetSplit(sym, normalizedTail), refs)
    case split @ Split.UseSplit(sym) =>
      (split, if jpctx.contains(sym) || spctx.contains(sym) then Set(sym) else Set.empty)
  
  /**
    * Specialize `split` with the assumption that `scrutinee` matches `pattern`.
    *
    * Returns `N` when the split is completely unchanged by specialization (no
    * branch in the split tests `scrutinee`), or `S(result)` when at least one
    * branch was modified, merged, or removed. Callers use this to detect
    * whether a `UseSplit` body was affected by specialization — if not, the
    * `UseSplit` reference is preserved to maintain join-point sharing.
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
  )(using VarSet, SpecializedSplitCtx): Opt[Split] = trace(
    pre = s"S$mode <<< ${scrutinee.showDbg} is ${pattern.showDbg} : ${split.prettyPrint}",
    post = (r: Opt[Split]) => s"S$mode >>> ${r.fold("(unchanged)")(_.prettyPrint)}"
  ):
    def rec(split: Split)(using mode: Mode, vs: VarSet): Opt[Split] = split match
      case Split.End => log("CASE Nil"); N
      case Split.Else(_) => log("CASE Else"); N
      case split @ Split.Let(sym, _, tail) =>
        log(s"CASE Let ${sym}")
        rec(tail).map(newTail => split.copy(tail = newTail))
      case split @ Split.Cons(head @ Branch(thatScrutinee, thatPattern, continuation), tail) =>
        log(s"CASE Cons ${head.showDbg}")
        if scrutinee === thatScrutinee then mode match
          case + =>
            log(s"Case 1.1: $scrutinee === $thatScrutinee")
            if thatPattern =:= pattern then
              log(s"Case 1.1.1: $pattern =:= $thatPattern")
              S(aliasBindings(pattern, thatPattern)(rec(continuation).getOrElse(continuation) ++ rec(tail).getOrElse(tail)))
            else if thatPattern <:< pattern then
              log(s"Case 1.1.2: $pattern <:< $thatPattern")
              pattern.markAsRefined
              rec(tail).map(newTail => split.copy(tail = newTail))
            else if split.isFallback then
              log(s"Case 1.1.3: $pattern is unrelated with $thatPattern")
              S(rec(tail).getOrElse(tail))
            else thatPattern match
            case thatPattern: FlatPattern.Record =>
              log(s"Case 1.1.4: $thatPattern is a record")
              // we can use information if pattern is itself a record, or if it is a constructor with arguments
              val simplifiedRecord = thatPattern assuming pattern
              if simplifiedRecord.entries.isEmpty then
                S(tail)
              else
                S(Split.Cons(Branch(thatScrutinee, simplifiedRecord, continuation), tail))
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
                N
              else
                if areProvablyDisjoint(pattern, thatPattern) then
                  log(s"Case 1.1.6: $pattern and $thatPattern are provably disjoint")
                  S(rec(tail).getOrElse(tail))
                else
                  // When patterns are not provably disjoint, we cannot assume
                  // the scrutinee can't match both (e.g., conjunction patterns
                  // like `A & B`). Keep the branch.
                  log(s"Case 1.1.6: $pattern and $thatPattern are not provably disjoint")
                  (rec(continuation), rec(tail)) match
                    case (N, N) => N
                    case (optCont, optTail) =>
                      S(head.copy(continuation = optCont.getOrElse(continuation)) ~: optTail.getOrElse(tail))
          case - =>
            log(s"Case 1.2: $scrutinee === $thatScrutinee")
            if thatPattern =:= pattern || thatPattern <:< pattern then
              log(s"Case 1.2.1: $pattern =:= (or <:<) $thatPattern")
              S(rec(tail).getOrElse(tail))
            else
              log(s"Case 1.2.2: $pattern are unrelated to $thatPattern")
              rec(tail).map(newTail => split.copy(tail = newTail))
        else
          log(s"Case 2: $scrutinee =/= $thatScrutinee")
          (rec(continuation), rec(tail)) match
            case (N, N) => N
            case (optCont, optTail) =>
              S(head.copy(continuation = optCont.getOrElse(continuation)) ~: optTail.getOrElse(tail))
      case split @ Split.LetSplit(sym, tail) =>
        log(s"CASE LetSplit ${sym.nme}")
        rec(tail).map(newTail => split.copy(tail = newTail))
      case split @ Split.UseSplit(sym) =>
        log(s"CASE UseSplit ${sym.nme}")
        // UseSplit references a shared body. If the body mentions the current
        // scrutinee, specialize it once and reuse the specialized split for
        // all identical uses in this specialization pass; otherwise keep the
        // reference. When rec returns N (body unchanged), the original UseSplit
        // is preserved to maintain sharing via the original join point.
        if !sym.body.referencesScrutinee(scrutinee) then N
        else summon[SpecializedSplitCtx].get(sym, mode, scrutinee, pattern) match
          case S(S(specializedSym)) => S(Split.UseSplit(specializedSym))
          case S(N) => N
          case N =>
            rec(sym.body) match
              case N =>
                summon[SpecializedSplitCtx].put(sym, mode, scrutinee, pattern, N)
                N
              case S(specializedBody) =>
                val specializedSym = new SplitSymbol(specializedBody, sym.nme)
                summon[SpecializedSplitCtx].put(sym, mode, scrutinee, pattern, S(specializedSym))
                S(Split.UseSplit(specializedSym))
    end rec

    rec(split)(using mode, summon)
  
  private def aliasBindings(p: FlatPattern, q: FlatPattern): Split => Split = (p, q) match
    case (FlatPattern.ClassLike(_, _, S(ss1), _), FlatPattern.ClassLike(_, _, S(ss2), _)) =>
      ss1.iterator.zip(ss2.iterator).foldLeft(identity[Split]):
        case (acc, (l, r)) if l._1 === r._1 => acc
        case (acc, (l, r)) => innermost => Split.Let(r._1, l._1.safeRef, acc(innermost))
    case (_, _) => identity
  
  import codegen.*, lowering.{term_nonTail, subTerm_nonTail, unreachableFn}
  
  private def lowerSplit
      (split: Split, cont: Result => Block)
      (using form: IfLikeForm)
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
    case Split.Else(els) =>
      term_nonTail(els, inStmtPos = form.isImperative)(cont)
    case Split.End =>
      // * See comment [comment:1] above
      if form is IfLikeForm.While then End()
      else throwMatchErrorBlock
    case Split.LetSplit(sym, tail) =>
      // Lower the join point: the body goes into the Label's `rest`, and
      // UseSplit generates Break(joinLabel) to reach it.
      val joinLabel = new LabelSymbol(N, sym.nme)
      sym.label = S(joinLabel)
      // When every leaf of both sides transfers control away (explicit
      // `return`/`throw`, `UseSplit` → break, or `End` → throw), no value
      // can flow into `cont`, so the exit-label wrapper is unnecessary even
      // when `cont` is not a TailOp.
      if (cont eq Ret) || (cont eq Thrw) || (form is IfLikeForm.While) ||
          (sym.body.alwaysTerminates && tail.alwaysTerminates) then
        val bodyBlock = lowerSplit(sym.body, cont)
        Label(joinLabel, false, lowerSplit(tail, cont), bodyBlock)
      else
        // Other continuations (including ImplctRet, which generates `expr;`
        // without `return`) can fall through the Label body into the rest.
        // Wrap with an exit label and temp variable so every path stores its
        // result, breaks to exitLabel, then the original cont runs once.
        val exitLabel = new LabelSymbol(N, sym.nme + "$x")
        val tmp = new TempSymbol(N)
        LoweringCtx.loweringCtx.collectScopedSym(tmp)
        val exitCont: Result => Block = r => Assign(tmp, r, Break(exitLabel))
        val bodyBlock = lowerSplit(sym.body, exitCont)
        val tailBlock = lowerSplit(tail, exitCont)
        Label(exitLabel, false,
          Label(joinLabel, false, tailBlock, bodyBlock),
          cont(Value.Ref(tmp)))
    case Split.UseSplit(sym) =>
      sym.label match
        case S(label) => Break(label)
        case N => lowerSplit(sym.body, cont) // fallback: inline if no label
  
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
        given SpecializedSplitCtx = SpecializedSplitCtx()
        val (normalizedSplit, refs) = normalize(inputSplit)(using VarSet(), JoinPointCtx.empty)
        bindSpecializedJoinPoints(normalizedSplit, refs)
      tl.scoped("ucs:normalized"):
        tl.log(s"Normalized:\n${normalized.prettyPrint}")
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
          if k.isInstanceOf[TailOp] then k
          else assignResult
      val mainBlock =
        given IfLikeForm = form
        lowerSplit(normalized, cont)
      val body =
        Scoped(
          if useNestedScoped then LoweringCtx.loweringCtx.getCollectedSym else Set.empty,
          mainBlock)
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
        else if k.isInstanceOf[TailOp]
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

  /** Immutable context tracking pending join point symbols whose LetSplit
    * placement is deferred to the lowest common ancestor of their UseSplit references. */
  case class JoinPointCtx(pending: Set[SplitSymbol]):
    def +(sym: SplitSymbol): JoinPointCtx = JoinPointCtx(pending + sym)
    def contains(sym: SplitSymbol): Bool = pending.contains(sym)
  object JoinPointCtx:
    val empty: JoinPointCtx = JoinPointCtx(Set.empty)

  final case class SpecializedSplitEntry(
      sym: SplitSymbol,
      mode: Mode,
      scrutinee: Term.Ref,
      pattern: FlatPattern,
      result: Opt[SplitSymbol]
  )

  final class SpecializedSplitCtx:
    private val entries = collection.mutable.ListBuffer.empty[SpecializedSplitEntry]
    private val symbols = collection.mutable.HashSet.empty[SplitSymbol]

    def contains(sym: SplitSymbol): Bool = symbols.contains(sym)

    def get(
        sym: SplitSymbol,
        mode: Mode,
        scrutinee: Term.Ref,
        pattern: FlatPattern
    ): Opt[Opt[SplitSymbol]] =
      entries.find(entry =>
        (entry.sym eq sym) &&
          entry.mode == mode &&
          (entry.scrutinee === scrutinee) &&
          entry.pattern == pattern
      ).map(_.result)

    def put(
        sym: SplitSymbol,
        mode: Mode,
        scrutinee: Term.Ref,
        pattern: FlatPattern,
        result: Opt[SplitSymbol]
    ): Unit =
      entries += SpecializedSplitEntry(sym, mode, scrutinee, pattern, result)
      result.foreach: symbol =>
        symbols += symbol

  object SpecializedSplitCtx:
    def apply(): SpecializedSplitCtx = new SpecializedSplitCtx

  /** Specialization mode */
  enum Mode:
    case +
    case -
