package hkmc2
package semantics
package ups

import hkmc2.utils.*, shorthands.*
import scala.annotation.tailrec
import syntax.Tree, Tree.{BoolLit, Ident, IntLit, UnitLit}
import Elaborator.{Ctx, State, ctx}, utils.TL
import Message.MessageContext
import ucs.{FlatPattern, TermSynthesizer, warn, safeRef}
import semantics.Pattern as SP
import Pattern.*, Context.*
import Compiler.ResultMode

object FixedPointCompiler:
  /** One alternative of the context pattern that descends into the hole.
    * @param holeIndex the index of the constructor argument holding the
    *        recursive context occurrence (the "hole")
    * @param sides the non-trivial side patterns guarding this alternative,
    *        paired with the index of the constructor argument they test;
    *        they are guaranteed to be transform-free
    */
  final case class AltInfo(holeIndex: Int, sides: Ls[(Int, Pat)])

  /** A constructor through which the context pattern descends, together with
    * its (ordered) descent alternatives. */
  final case class ClassInfo(index: Int, symbol: ClassSymbol, paramCount: Int, alts: Ls[AltInfo])

  /** The compiled fixed-point matcher. The `unapply` body is assembled by
    * `Lowering` as: evaluate `prelude`, run `loop` as a `while` form (the loop
    * exits when no branch of the split matches), then return `result`. */
  final case class Machine(params: ParamList, prelude: Ls[Statement], loop: Split, result: Term)

  /** The outcome of `compile` on a fixed-point-shaped pattern. */
  enum Outcome:
    /** The compiled machine, paired with the output sub-pattern of the
      * match-site shorthand (`x is @compile S(q)`). For non-catch-all
      * definitions, `fallback` holds the pattern with which a failed machine
      * run must be retried — the naive backtracking translation implements
      * the deepest-first try order on intermediate results that the machine
      * does not keep around. */
    case Compiled(machine: Machine, outputPattern: Opt[SP], fallback: Opt[SP])
    /** The pattern is fixed-point shaped but not supported by the machine
      * compilation; a warning has been reported and the caller should use the
      * naive backtracking translation. */
    case Unsupported

  // The machine's control modes. `find` searches the focus for a redex going
  // downwards; `up` re-examines the frame on top of the context stack after
  // the focus has been exhausted; `done` matches no branch of the loop split,
  // which makes the `while` form exit.
  private val ModeFind = 0
  private val ModeUp = 1
  private val ModeDone = 2

/** Compiles "fixed-point" pattern definitions — patterns that pipe their own
  * output back into themselves through a chain pattern, such as
  *
  * {{{
  * pattern Steps = Step as Steps | _
  * }}}
  *
  * — into an iterative matcher that does *not* restart the redex search from
  * the root of the scrutinee after every rewriting step.
  *
  * Note that `as` binds tighter than `|`, so the definition above reads
  * `(Step as Steps) | _`: the `Step as Steps` alternative iterates the step
  * until no further step is possible, and the trailing `_` keeps the result.
  * Since the alternatives are left-biased and `_` is total, the matcher
  * always succeeds, outputting the normal form of the scrutinee — which is
  * the scrutinee itself when not even one rewriting step applies.
  *
  * The recognized shape is `pattern S = P as S | a1 | ... | ak | _`, read as
  * `(P as S) | a1 | ... | ak | _` — the middle alternatives `a1 ... ak` are
  * optional and, since the recursive alternative fails exactly when `P`
  * cannot step, are matched once against the final normal form — where `P`
  * instantiates (possibly through synonyms) to a self-recursive "evaluation
  * context" disjunction whose alternatives are, in order:
  *
  *   1. *redex alternatives*: patterns that do not mention the recursive
  *      context (typically transform patterns rewriting a focused subterm); and
  *   2. *descent alternatives*: constructor patterns with exactly one direct
  *      argument holding the recursive context occurrence (the hole), all
  *      other arguments being transform-free side conditions.
  *
  * Such a definition denotes normalization of the scrutinee with respect to
  * the rewrite rules (1) under the strategy (2). The naive compilation
  * re-decomposes the whole term after each contraction, costing O(steps ×
  * redex depth). Instead, we compile the definition to a small abstract
  * machine in the style of Danvy and Nielsen's *refocusing* transformation
  * ("Refocusing in Reduction Semantics", BRICS RS-04-26): the machine keeps
  * the current decomposition as explicit state — a focused subterm plus a
  * stack of one-hole frames — and resumes the search at the rewrite site.
  *
  * Soundness rests on the locality of rewriting: facts established away from
  * the focus (a sibling is a `Value`, an ancestor's head constructor) persist
  * across a contraction at the focus, because the side conditions are
  * transform-free. After popping back into a frame the machine re-tests only
  * what a contraction below could have changed: whether the rebuilt node is
  * now itself a redex, and which descent alternatives become enabled. Subtrees
  * the machine has popped out of are inert (in normal form with respect to
  * the strategy) and are skipped via per-frame inertness flags, which is what
  * makes the total cost proportional to the initial term size plus the sizes
  * of the contracta, rather than steps × depth.
  *
  * Caveat (the usual refocusing side condition): if the context grammar does
  * not decompose terms uniquely — e.g. a contractum can simultaneously make
  * an ancestor a redex *and* contain a reachable redex itself — the machine
  * may pick a different (still valid) redex than the naive backtracking
  * order. For non-overlapping grammars such as CBV evaluation contexts the
  * two agree.
  *
  * Like the rest of the efficient pattern compilation, this is opt-in via
  * the `@compile` pattern annotation — either at a match site
  * (`x is @compile Steps`) or on the definition's right-hand side
  * (`pattern Steps = @compile (Step as Steps | _)`), in which case the
  * generated `unapply` method embeds the machine and every match site
  * benefits. Patterns that are not fixed-point shaped proceed with the
  * regular multi-matcher compilation; fixed-point-shaped patterns that the
  * machine compilation does not support get a warning and fall back to the
  * naive backtracking translation.
  */
class FixedPointCompiler(using tl: TL)(using State, Ctx, Raise) extends TermSynthesizer:
  import FixedPointCompiler.*, tl.*

  /** Try to compile the given `@compile`-annotated pattern into a fixed-point
    * machine. Two shapes are recognized:
    *
    *   - A reference to a pattern definition whose body is fixed-point
    *     shaped, used at a match site: `x is @compile S` (also with the
    *     output-matching shorthand, `x is @compile S(q)`).
    *   - The fixed-point body itself, when the annotation is placed on a
    *     definition's right-hand side: `pattern S = @compile (P as S | _)`.
    *     The `unapply` translation then reaches this method with the body.
    *
    * Returns `N` when the pattern is not fixed-point shaped — in which case
    * the caller should proceed with the regular efficient compilation. */
  def compile(pattern: SP): Opt[Outcome] = pattern match
    case SP.Constructor(target, arguments) =>
      target.resolvedSym.flatMap(_.asPat).flatMap: patternSymbol =>
        patternSymbol.defn match
          case S(defn) if defn.patternParams.isEmpty && defn.extractionParams.isEmpty =>
            val outputPattern = arguments match
              case N | S(Nil) => S(N)
              case S(sole :: Nil) => S(S(sole))
              // Several arguments are not understood by fixed-point
              // patterns; let the regular path report the mismatch.
              case S(_) => N
            outputPattern.flatMap: outputPattern =>
              def compiled(machine: Machine, needsFallback: Bool): Opt[Outcome] =
                S(Outcome.Compiled(machine, outputPattern, if needsFallback then S(pattern) else N))
              patternSymbol.fixedPointMachine match
                case S((machine, needsFallback)) => compiled(machine, needsFallback)
                case N =>
                  val shape = recognizeShape(stripAnnotations(defn.pattern))
                  val recognized = shape.filter(_._1 is patternSymbol).flatMap:
                    (_, stepPattern, rest, requireProgress) =>
                      classifyRest(rest).map((middles, catchAll) =>
                        (stepPattern, middles, catchAll, requireProgress))
                  val machine = recognized match
                    case S((stepPattern, middles, catchAll, requireProgress)) =>
                      scoped("ucs:fixpoint")(compileMachine(stepPattern, middles, catchAll, requireProgress))
                        .map((_, !catchAll))
                    case N =>
                      // The definition may instead be a link of an indirect
                      // recursion cycle.
                      recognizeCycle(patternSymbol).flatMap: links =>
                        scoped("ucs:fixpoint")(compileAlternatingMachine(links))
                          .map((_, links.exists(!_._4)))
                  machine match
                    case S((machine, needsFallback)) =>
                      patternSymbol.fixedPointMachine = S((machine, needsFallback))
                      compiled(machine, needsFallback)
                    case N => unsupported(recognized.isDefined, shape.isDefined, pattern.toLoc)
          case _ => N
    case body: (SP.Chain | SP.Composition) =>
      // The body-annotated form. The body must belong to the very definition
      // its self-references refer to — `(P as Other) | _` with a foreign
      // `Other` is not a fixed point. The `eq` check suffices because the
      // `unapply` translation passes the definition's own body node down to
      // here.
      def isOwnBody(patternSymbol: PatternSymbol): Bool =
        patternSymbol.defn.exists(defn =>
          (stripAnnotations(defn.pattern) eq body) &&
            defn.patternParams.isEmpty && defn.extractionParams.isEmpty)
      recognizeShape(body) match
        case S((patternSymbol, stepPattern, rest, requireProgress)) if isOwnBody(patternSymbol) =>
          val recognized = classifyRest(rest)
          val machine = recognized.flatMap: (middles, catchAll) =>
            scoped("ucs:fixpoint")(compileMachine(stepPattern, middles, catchAll, requireProgress))
              .map((_, !catchAll))
          machine match
            case S((machine, needsFallback)) =>
              patternSymbol.fixedPointMachine = S((machine, needsFallback))
              S(Outcome.Compiled(machine, N, if needsFallback then S(body) else N))
            case N => unsupported(recognized.isDefined, true, body.toLoc)
        case S((tailSymbol, _, _, _)) =>
          // The body may be a link of an indirect recursion cycle; its tail
          // then refers to the next link rather than the definition itself.
          // Locate the definition the body belongs to in the cycle and
          // rotate its link to the front.
          val machine = recognizeCycle(tailSymbol).flatMap: links =>
            links.indexWhere((symbol, _, _, _) =>
              symbol.defn.exists(defn => stripAnnotations(defn.pattern) eq body)) match
              case -1 => N
              case index =>
                val rotated = links.drop(index) ::: links.take(index)
                scoped("ucs:fixpoint")(compileAlternatingMachine(rotated)).map: machine =>
                  (rotated.head._1, machine, links.exists(!_._4))
          machine match
            case S((owner, machine, needsFallback)) =>
              owner.fixedPointMachine = S((machine, needsFallback))
              S(Outcome.Compiled(machine, N, if needsFallback then S(body) else N))
            case N => unsupported(false, true, body.toLoc)
        case N => N
    case _ => N

  /** Handle a pattern the machine compilation rejected: when it is
    * fixed-point shaped, report a warning (unless the rejection point already
    * did) and route the caller to the naive translation, which handles all
    * such shapes; otherwise leave it to the regular efficient compilation. */
  private def unsupported(alreadyWarned: Bool, shaped: Bool, loc: Opt[Loc]): Opt[Outcome] =
    if alreadyWarned then S(Outcome.Unsupported)
    else if shaped then
      warn(msg"This fixed-point pattern is not supported by the machine compilation." -> loc,
        msg"Falling back to the naive translation." -> N)
      S(Outcome.Unsupported)
    else N

  /** Remove `Annotated` wrappers (such as the `@compile` marking itself). */
  @tailrec private def stripAnnotations(pattern: SP): SP = pattern match
    case SP.Annotated(pattern, _) => stripAnnotations(pattern)
    case _ => pattern

  /** Flatten nested disjunctions into the list of their alternatives,
    * stripping `Annotated` wrappers so an annotation on an alternative does
    * not defeat the shape checks. */
  private def disjuncts(pattern: SP): Ls[SP] = stripAnnotations(pattern) match
    case SP.Composition(true, left, right) => disjuncts(left) ::: disjuncts(right)
    case stripped => stripped :: Nil

  /** Classify the alternatives following the recursive ones into the middle
    * alternatives and the optional trailing wildcard. */
  private def classifyRest(rest: Ls[SP]): Opt[(Ls[SP], Bool)] =
    if rest.isEmpty then N
    else
      val catchAll = rest.last.isInstanceOf[SP.Wildcard]
      val middles = if catchAll then rest.init else rest
      // Reject non-trailing wildcards (they make later alternatives
      // unreachable) and chains (recursive alternatives must be leading).
      if middles.exists(p => p.isInstanceOf[SP.Wildcard] || p.isInstanceOf[SP.Chain]) then N
      else S((middles, catchAll))

  /** Recognize a fixed-point shape, discovering the pattern symbol `S` the
    * recursive alternatives refer to (the definition itself, or the next link
    * of an indirect recursion cycle). Two shapes are recognized, differing
    * only in whether a first step is required — `as` binds tighter than `|`,
    * so the grouping (and hence which shape it is) follows from the
    * parentheses:
    *
    *   - `(P1 as S) | ... | (Pn as S) | rest` — the *zero-or-more* shape
    *     (written `P1 as S | ... | Pn as S | rest`): the steps `P1 ... Pn` are
    *     tried in order at each iteration, and since the trailing alternatives
    *     `rest` are disjuncts of the whole chains rather than of their tails,
    *     zero steps are allowed — `rest` then processes the original
    *     scrutinee.
    *   - `P as (S | rest)` — the *one-or-more* shape: the chain requires the
    *     first `P` step, so a run with zero steps is a match failure. The
    *     parentheses around `S | rest` are what distinguish it.
    *
    * Return the symbol, the step pattern (the disjunction of the steps), the
    * trailing alternatives (to be validated with `classifyRest`), and whether
    * at least one step is required. */
  private def recognizeShape(pattern: SP): Opt[(PatternSymbol, SP, Ls[SP], Bool)] =
    pattern match
      case SP.Chain(stepPattern, tail) => disjuncts(tail) match
        case SP.Constructor(target, N) :: rest =>
          target.resolvedSym.flatMap(_.asPat).map((_, stepPattern, rest, true))
        case _ => N
      case composition: SP.Composition => disjuncts(composition) match
        case SP.Chain(_, SP.Constructor(target, N)) :: _ =>
          target.resolvedSym.flatMap(_.asPat).map: symbol =>
            def isSelf(target: Term): Bool =
              target.resolvedSym.flatMap(_.asPat).exists(_ is symbol)
            val (selfChains, rest) = disjuncts(composition).span:
              case SP.Chain(_, SP.Constructor(target, N)) => isSelf(target)
              case _ => false
            val steps = selfChains.collect { case SP.Chain(step, _) => step }
            (symbol, steps.reduceLeft(SP.Composition(true, _, _)), rest, false)
        case _ => N
      case _ => N

  /** Recognize an indirect recursion cycle of fixed-point definitions
    * starting from `start`: each body is `(step as Next) | rest` where
    * `Next` refers to the following definition, and the last one refers back
    * to `start`. The semantics is left-biased alternation: the steps fire in
    * cycle order, and whenever a step fails, the failing link's alternatives
    * process the current term — the original scrutinee when even the first
    * step fails. Returns the links in cycle order, beginning with `start`'s
    * own. */
  private def recognizeCycle(start: PatternSymbol)
      : Opt[Ls[(PatternSymbol, SP, Ls[SP], Bool)]] =
    @tailrec def walk(
        current: PatternSymbol,
        acc: Ls[(PatternSymbol, SP, Ls[SP], Bool)]
    ): Opt[Ls[(PatternSymbol, SP, Ls[SP], Bool)]] =
      val linkOpt = current.defn match
        case S(defn) if defn.patternParams.isEmpty && defn.extractionParams.isEmpty =>
          recognizeShape(stripAnnotations(defn.pattern)) match
            case S((next, stepPattern, rest, _)) =>
              classifyRest(rest).map: (middles, catchAll) =>
                (next, (current, stepPattern, middles, catchAll))
            case _ => N
        case _ => N
      linkOpt match
        case S((next, link)) =>
          if next is start then S((link :: acc).reverse)
          else if (next is current) || acc.exists(_._1 is next) then N
          else walk(next, link :: acc)
        case N => N
    // Cycles of length one are the direct shape, handled in `compile`.
    walk(start, Nil).filter(_.sizeIs > 1)

  /** Does `pattern` mention the given instantiation anywhere? Used to locate
    * the recursive occurrences of the context pattern (the "holes"). */
  private def mentions(pattern: Pat, target: Instantiation): Bool = pattern match
    case Synonym(inst) => (inst == target) || inst.arguments.exists(mentions(_, target))
    case ClassLike(_, arguments) => arguments.exists(_.valuesIterator.exists(mentions(_, target)))
    case MatchedClassLike(_, entries) => entries.valuesIterator.exists(mentions(_, target))
    case Record(entries) => entries.valuesIterator.exists(mentions(_, target))
    case Tuple(leading, spread) => leading.exists(mentions(_, target)) || spread.exists:
      case (_, middle, trailing) => mentions(middle, target) || trailing.exists(mentions(_, target))
    case And(patterns) => patterns.exists(mentions(_, target))
    case Or(patterns) => patterns.exists(mentions(_, target))
    case Not(pattern) => mentions(pattern, target)
    case Rename(pattern, _) => mentions(pattern, target)
    case Extract(pattern, _, _) => mentions(pattern, target)
    case Literal(_) => false

  /** Instantiate the pattern groups with a shared `Instantiator`,
    * monomorphizing higher-order patterns such as `Ctx(Redex)` into
    * first-order synonyms. Each instantiation returns a context built from
    * the instantiator's cumulative progress, so the context of the last one
    * — which is returned — covers them all. */
  private def instantiateGroups(groups: Ls[Ls[SP]]): (Ls[Ls[Pat]], Context) =
    val instantiator = new Instantiator
    val results = groups.map(_.map(instantiator(_)))
    (results.map(_.map(_._1)), results.flatten.last._2)

  /** The post pattern processes the final normal form; the definition's
    * trailing wildcard, when present, makes it total. */
  private def postPattern(middles: Ls[Pat], catchAll: Bool): Opt[Pat] =
    if catchAll then
      if middles.isEmpty then N else S(Or(middles :+ Wildcard))
    else S(Or(middles))

  private def compileMachine(stepPattern: SP, middles: Ls[SP], catchAll: Bool, requireProgress: Bool): Opt[Machine] =
    val (instantiated, context) = instantiateGroups((stepPattern :: middles) :: Nil)
    val entry = instantiated.head.head
    val post = postPattern(instantiated.head.tail, catchAll)
    given Context = context
    // Walk through synonym definitions until we find a self-recursive one:
    // that instantiation is the evaluation context.
    @tailrec def chase(pattern: Pat, visited: Set[Instantiation]): Opt[(Instantiation, Pat)] =
      pattern match
        case Synonym(inst) if !visited.contains(inst) =>
          val body = inst.body
          if mentions(body, inst) then S((inst, body)) else chase(body, visited + inst)
        case _ => N
    chase(entry, Set.empty) match
      case N =>
        // The step pattern is not built from a recursive context. The fixed
        // point degenerates to a flat contraction loop: keep applying the
        // step pattern to its own output until it fails.
        log(s"No recursive context; compiling a flat contraction loop.")
        S(assemble(entry, Nil, post, requireProgress))
      case S((ctxInst, body)) =>
        log(s"Recursive context: ${ctxInst.showDbg}")
        val alternatives = body match
          case Or(alternatives) => alternatives
          case pattern => pattern :: Nil
        classify(ctxInst, alternatives).map: (redexAlternatives, classes) =>
          val redexPattern = redexAlternatives match
            case single :: Nil => single
            case multiple => Or(multiple)
          assemble(redexPattern, classes, post, requireProgress)

  /** Split the context's alternatives into the leading redex alternatives and
    * the trailing descent alternatives, validating the restrictions of the
    * machine compilation. Returns `N` (with warnings) if anything is off. */
  private def classify(ctxInst: Instantiation, alternatives: Ls[Pat])(using Context)
      : Opt[(Ls[Pat], Ls[ClassInfo])] =
    val (redexAlternatives, descentAlternatives) =
      alternatives.span(pattern => !mentions(pattern, ctxInst))
    def parse(pattern: Pat): Opt[(ClassSymbol, Int, AltInfo)] = pattern match
      case ClassLike(cls: ClassSymbol, S(arguments)) =>
        val entries = arguments.toList
        val holes = entries.iterator.zipWithIndex.collect:
          case ((_, argument), index) if mentions(argument, ctxInst) => (index, argument)
        .toList
        holes match
          case (holeIndex, Synonym(inst)) :: Nil if inst == ctxInst =>
            val arity = cls.defn.flatMap(_.paramsOpt).fold(0)(_.params.size)
            val sides = entries.iterator.zipWithIndex.collect:
              case ((_, argument), index) if index != holeIndex && argument != Wildcard =>
                (index, argument)
            .toList
            if arity != entries.size then
              warn(msg"Cannot rebuild `${cls.nme}` because not all of its parameters are accessible." -> pattern.toLoc)
              N
            else if !sides.forall((_, side) => side.preservesOriginalScrutinee) then
              warn(msg"Side patterns of a context alternative must be transform-free." -> pattern.toLoc)
              N
            else S((cls, entries.size, AltInfo(holeIndex, sides)))
          case _ =>
            warn(msg"The recursive context must occur as exactly one direct constructor argument." -> pattern.toLoc)
            N
      case _ =>
        warn(msg"This alternative is not supported by fixed-point pattern compilation." -> pattern.toLoc)
        N
    if redexAlternatives.isEmpty then
      // Without a redex alternative no rewriting step can ever fire: the
      // naive pattern never matches, and a machine — whose redex matcher
      // would degenerate to a catch-all — would search forever.
      warn(msg"The recursive context has no redex alternative, so no rewriting step can apply." -> ctxInst.toLoc)
      N
    else if descentAlternatives.exists(pattern => !mentions(pattern, ctxInst)) then
      warn(msg"Redex alternatives must precede all recursive context alternatives." -> ctxInst.toLoc)
      N
    else
      val parsed = descentAlternatives.map(parse)
      if parsed.contains(N) then N
      else
        val flat = parsed.flatten
        // Group the alternatives by their head constructor, preserving both
        // the first-occurrence order of constructors and the relative order
        // of alternatives sharing a constructor. The latter is what the
        // machine's phase scan replays.
        val order = flat.map(_._1).distinct
        val classes = order.iterator.zipWithIndex.map: (cls, index) =>
          val altsFor = flat.collect { case (`cls`, paramCount, alt) => (paramCount, alt) }
          ClassInfo(index, cls, altsFor.head._1, altsFor.map(_._2))
        .toList
        S((redexAlternatives, classes))

  private def setStmt(symbol: LocalVarSymbol, value: Term): Statement =
    Term.Assgn(symbol.safeRef, value)

  /** A leaf of a loop split: execute the state updates; the `while` form
    * then re-enters the loop from the top. */
  private def perform(stmts: Statement*): Split =
    Split.Else(Term.Blk(stmts.toList, Term.Lit(UnitLit(false))))

  private def intPattern(value: Int): FlatPattern = FlatPattern.Lit(IntLit(BigInt(value)))

  private def callMatcher(matcher: LocalVarSymbol, argument: Term, label: Str): Term =
    app(matcher.safeRef, tup(fld(argument)), label)

  private def refEq(left: Term, right: Term): Term =
    app(State.builtinOpsMap("===").ref(Ident("===")), tup(fld(left), fld(right)), "reference equality")

  /** Run `make` with a thunk producing the `rest` split. When the thunk is
    * invoked more than once, `rest` is bound as a join point and every
    * invocation yields only a `UseSplit` reference, so the generated split
    * tree stays linear in the number of alternatives. */
  private def join(rest: Split, uses: Int)(make: (() => Split) => Split): Split =
    if uses > 1 then
      val symbol = new SplitSymbol(rest, "alt")
      Split.LetSplit(symbol, make(() => Split.UseSplit(symbol)))
    else make(() => rest)

  /** Compile an indirect recursion cycle. Each link contributes its step
    * pattern and its trailing alternatives, turned into a post pattern as in
    * `compileMachine`. */
  private def compileAlternatingMachine(links: Ls[(PatternSymbol, SP, Ls[SP], Bool)]): Opt[Machine] =
    val (instantiated, context) = instantiateGroups(links.map((_, step, middles, _) => step :: middles))
    val compiled = instantiated.zip(links).map: (patterns, link) =>
      (patterns.head, postPattern(patterns.tail, link._4))
    given Context = context
    S(assembleAlternating(compiled))

  /** Assemble the flat alternation loop for an indirect recursion cycle: in
    * phase `i`, step `i` is applied to the current term; on success the
    * machine moves to the next phase in the cycle, and on failure it records
    * the failing phase and exits. The failing link's alternatives then process
    * the current term — which is the original scrutinee when the very first
    * step fails, so zero steps are allowed, exactly as for the direct shape.
    * When those alternatives don't match either, the run fails and the caller
    * retries it with the naive translation, which performs the deepest-first
    * backtracking through the intermediate terms. */
  private def assembleAlternating(links: Ls[(Pat, Opt[Pat])])(using Context): Machine =
    // Like in `assemble`, every matcher gets its own compiler instance
    // because the matcher memoization is instance-bound.
    val matchers = links.map: (step, post) =>
      val stepCompiler = new Compiler
      val (stepMatcher, stepImpls) = stepCompiler.buildMatcher(step, ResultMode.Full)
      val postMatcherOpt = post.map: postPattern =>
        val postCompiler = new Compiler
        postCompiler.buildMatcher(postPattern, ResultMode.Full)
      (stepMatcher, stepImpls, postMatcherOpt)

    val inputSymbol = VarSymbol(Ident("input"))
    val phaseSymbol = TempSymbol(N, "phase")
    val focusSymbol = TempSymbol(N, "focus")
    // The phase whose step failed, selecting the link whose alternatives
    // process the final term. Since the loop only ever exits through a step
    // failure, it is always set before `result` runs.
    val failPhaseSymbol = TempSymbol(N, "failPhase")
    val size = links.size

    val loop = matchers.iterator.zipWithIndex.foldRight(Split.End: Split):
      case (((stepMatcher, _, _), index), rest) =>
        val resultSym = TempSymbol(N, s"step$index$$Result")
        val outputSym = TempSymbol(N, "stepOutput")
        Branch(phaseSymbol.safeRef, intPattern(index),
          Split.Let(resultSym, callMatcher(stepMatcher, focusSymbol.safeRef, "step result"),
            Branch(resultSym.safeRef, matchSuccessPattern(S(outputSym :: Nil)),
              perform(
                setStmt(focusSymbol, outputSym.safeRef),
                setStmt(phaseSymbol, int((index + 1) % size)))
            // The step failed: record this phase and exit (no phase matches
            // `size`, which makes the `while` form exit).
            ) ~: perform(
                setStmt(failPhaseSymbol, int(index)),
                setStmt(phaseSymbol, int(size))))
        ) ~: rest

    val result = Term.SynthIf(
      matchers.iterator.zipWithIndex.foldRight(Split.Else(makeMatchFailure()): Split):
        case (((_, _, postMatcherOpt), index), rest) =>
          val success = postMatcherOpt match
            case S((postMatcher, _)) =>
              callMatcher(postMatcher, focusSymbol.safeRef, "post-processed result")
            case N => makeMatchSuccess(focusSymbol.safeRef)
          Branch(failPhaseSymbol.safeRef, intPattern(index), Split.Else(success)) ~: rest)

    val prelude =
      matchers.flatMap((_, stepImpls, postMatcherOpt) =>
        stepImpls ::: postMatcherOpt.fold(Nil)(_._2)
      ).flatMap: (symbol, params, body) =>
        LetDecl(symbol, Nil) :: DefineVar(symbol, Term.Lam(params, body)) :: Nil
      ::: List(
        LetDecl(phaseSymbol, Nil), DefineVar(phaseSymbol, int(0)),
        LetDecl(focusSymbol, Nil), DefineVar(focusSymbol, inputSymbol.safeRef),
        LetDecl(failPhaseSymbol, Nil), DefineVar(failPhaseSymbol, int(-1)))

    Machine(paramList(param(inputSymbol)), prelude, loop, result)

  /** Assemble the machine: matcher functions for the redex and the side
    * conditions (reusing the non-backtracking `ups.Compiler`), the state
    * variables, and the `find`/`up` transition split executed in a loop. */
  private def assemble(redexPattern: Pat, classes: Ls[ClassInfo], post: Opt[Pat], requireProgress: Bool)(using Context): Machine =
    // The redex matcher runs in `Full` mode: on success it returns
    // `MatchSuccess(contractum, bindings)` where the output is the rewritten
    // subterm. Side conditions only need Booleans (`MatchOnly`). The two
    // modes produce differently-shaped functions and the compiler's matcher
    // memoization is mode-unaware, so we use two separate instances.
    val redexCompiler = new Compiler
    val (redexMatcher, redexImpls) = redexCompiler.buildMatcher(redexPattern, ResultMode.Full)
    val sideCompiler = new Compiler
    val sideMatchers: Map[Pat, LocalVarSymbol] =
      classes.iterator.flatMap(_.alts.iterator.flatMap(_.sides.iterator.map(_._2)))
        .toList.distinct.map: side =>
          side -> sideCompiler.buildMatcher(side, ResultMode.MatchOnly)._1
        .toMap
    val sideImpls = sideCompiler.implementations.iterator.map:
      case (symbol, (params, body)) => (symbol, params, body)
    .toList
    // The post matcher processes the final normal form. It is total (the
    // definition's trailing wildcard is among its alternatives), so it always
    // returns a `MatchSuccess` that the `unapply` can yield directly.
    val postMatcherOpt = post.map: postPattern =>
      val postCompiler = new Compiler
      val (postMatcher, postImpls) = postCompiler.buildMatcher(postPattern, ResultMode.Full)
      (postMatcher, postImpls)

    log(s"Classes: ${classes.map(cls => s"${cls.symbol.nme}(${cls.alts})").mkString(", ")}")

    // ---- Machine state ----
    val inputSymbol = VarSymbol(Ident("input"))
    val modeSymbol = TempSymbol(N, "mode")
    val focusSymbol = TempSymbol(N, "focus")
    val stackSymbol = TempSymbol(N, "stack")
    val resultSymbol = TempSymbol(N, "finalResult")
    // Whether at least one contraction has fired. Only the one-or-more shape
    // (`P as (S | _)`) tracks it: it requires the first step to succeed, so a
    // run with zero contractions is a match failure.
    val progressedSymbol = TempSymbol(N, "progressed")

    def bool(value: Bool): Term = Term.Lit(BoolLit(value))
    def markProgress: Ls[Statement] =
      if requireProgress then setStmt(progressedSymbol, bool(true)) :: Nil else Nil
    def constructorTerm(cls: ClassInfo): Term =
      Compiler.reference(cls.symbol, N).getOrElse(Term.Error())
    def classPattern(cls: ClassInfo, children: Ls[TempSymbol]): FlatPattern =
      FlatPattern.ClassLike(constructorTerm(cls), cls.symbol, S(children.map(_ -> N)), false)(Tree.Dummy)

    // ---- Context frames ----
    // A frame is a record reifying a one-hole context layer: the constructor
    // (as an integer tag), the current children, one inertness flag per child
    // position (true when that subtree is known to be strategy-normal), the
    // node the frame decomposes (so plugging an unchanged child back can
    // reuse it instead of allocating), the hole position we descended into,
    // and the rest of the stack.
    def childField(index: Int) = s"c$index"
    def inertField(index: Int) = s"i$index"
    def mkFrame(cls: ClassInfo, hole: Int, child: Int => Term, inert: Int => Term, node: Term, tail: Term): Term =
      Term.Rcd(false,
        RcdField(str("tag"), int(cls.index)) ::
        List.tabulate(cls.paramCount)(index => RcdField(str(childField(index)), child(index))) :::
        List.tabulate(cls.paramCount)(index => RcdField(str(inertField(index)), inert(index))) :::
        RcdField(str("n"), node) ::
        RcdField(str("h"), int(hole)) ::
        RcdField(str("t"), tail) :: Nil)

    /** Chain the side-condition tests of one alternative. `failure` is
      * invoked at every failure point; callers bind it as a join point (see
      * `join`) when that would otherwise duplicate the remaining chain. */
    def sideChecks(sides: Ls[(Int, Pat)], child: Int => Term, success: Split, failure: () => Split): Split =
      sides match
        case Nil => success
        case (index, side) :: rest =>
          val okSymbol = TempSymbol(N, "sideOk")
          Split.Let(okSymbol, callMatcher(sideMatchers(side), child(index), "side condition"),
            Branch(okSymbol.safeRef, sideChecks(rest, child, success, failure)) ~: failure())

    /** Call the redex matcher on `scrutinee` and branch on its result. */
    def matchRedex(scrutinee: Term, onSuccess: TempSymbol => Split, onFailure: Split): Split =
      val resultSym = TempSymbol(N, "redexResult")
      val outputSym = TempSymbol(N, "contractum")
      Split.Let(resultSym, callMatcher(redexMatcher, scrutinee, "redex match"),
        Branch(resultSym.safeRef, matchSuccessPattern(S(outputSym :: Nil)),
          onSuccess(outputSym)) ~: onFailure)

    // ---- `find` mode: search the focus downwards for a redex ----
    // The focus is exhausted: switch to `up` mode to re-examine the parent.
    def goUp(): Split = perform(setStmt(modeSymbol, int(ModeUp)))
    def findDescend(cls: ClassInfo, children: Ls[TempSymbol]): Split =
      cls.alts.foldRight(goUp()): (alt, rest) =>
        val push = perform(
          setStmt(stackSymbol, mkFrame(cls, alt.holeIndex,
            index => children(index).safeRef, _ => bool(false),
            focusSymbol.safeRef, stackSymbol.safeRef)),
          setStmt(focusSymbol, children(alt.holeIndex).safeRef))
        join(rest, alt.sides.length): failure =>
          sideChecks(alt.sides, index => children(index).safeRef, push, failure)
    val findSplit =
      val classChain = classes.foldRight(goUp()): (cls, rest) =>
        val children = List.tabulate(cls.paramCount)(index => TempSymbol(N, s"scrut$index"))
        Branch(focusSymbol.safeRef, classPattern(cls, children), findDescend(cls, children)) ~: rest
      matchRedex(focusSymbol.safeRef,
        // A contraction: refocus on the contractum and keep searching. This
        // is the step that avoids restarting from the root.
        contractum => perform((
          setStmt(focusSymbol, contractum.safeRef) :: markProgress)*),
        classChain)

    // ---- `up` mode: the focus is inert; re-examine the topmost frame ----
    // We re-test only what the contraction(s) below may have changed: whether
    // the rebuilt node is now a redex (the hole alternative would fire first
    // on a naive restart) and which descent alternatives become enabled.
    // Positions marked inert are skipped — their subtrees were exhausted by
    // earlier descents and cannot have changed since.
    def upHole(cls: ClassInfo, hole: Int, children: Ls[TempSymbol], inerts: Ls[TempSymbol], nodeSym: TempSymbol, tailSym: TempSymbol): Split =
      def child(index: Int): Term =
        if index == hole then focusSymbol.safeRef else children(index).safeRef
      def inert(index: Int): Term =
        if index == hole then bool(true) else inerts(index).safeRef
      val rebuiltSymbol = TempSymbol(N, "rebuilt")
      val pop = perform(
        setStmt(stackSymbol, tailSym.safeRef),
        setStmt(focusSymbol, rebuiltSymbol.safeRef))
      val altChain = cls.alts.foldRight(pop): (alt, rest) =>
        // The position we just returned from is inert by construction.
        if alt.holeIndex == hole then rest
        else
          val move = perform(
            setStmt(stackSymbol, mkFrame(cls, alt.holeIndex, child, inert,
              rebuiltSymbol.safeRef, tailSym.safeRef)),
            setStmt(focusSymbol, child(alt.holeIndex)),
            setStmt(modeSymbol, int(ModeFind)))
          join(rest, alt.sides.length + 1): failure =>
            Branch(inerts(alt.holeIndex).safeRef, FlatPattern.Lit(BoolLit(false)),
              sideChecks(alt.sides, child, move, failure)) ~: failure()
      // Plugging preserves identity: when no contraction happened below the
      // frame, the focus is still the very child we descended into, and the
      // frame's node can be reused instead of allocating a rebuilt copy.
      val unchangedSymbol = TempSymbol(N, "unchanged")
      Split.Let(unchangedSymbol, refEq(focusSymbol.safeRef, children(hole).safeRef),
        Split.Let(rebuiltSymbol,
          Term.SynthIf(
            Branch(unchangedSymbol.safeRef, Split.Else(nodeSym.safeRef)) ~:
            Split.Else(`new`(constructorTerm(cls), tup(List.tabulate(cls.paramCount)(child)) :: Nil, s"rebuilt ${cls.symbol.nme}"))),
          matchRedex(rebuiltSymbol.safeRef,
            contractum => perform((
              setStmt(stackSymbol, tailSym.safeRef) ::
              setStmt(focusSymbol, contractum.safeRef) ::
              setStmt(modeSymbol, int(ModeFind)) :: markProgress)*),
            altChain)))
    def upClass(cls: ClassInfo): Split =
      val children = List.tabulate(cls.paramCount)(index => TempSymbol(N, s"frameChild$index"))
      val inerts = List.tabulate(cls.paramCount)(index => TempSymbol(N, s"frameInert$index"))
      val nodeSym = TempSymbol(N, "frameNode")
      val tailSym = TempSymbol(N, "frameTail")
      val core = cls.alts.map(_.holeIndex).distinct match
        case only :: Nil => upHole(cls, only, children, inerts, nodeSym, tailSym)
        case multiple =>
          val holeSymbol = TempSymbol(N, "frameHole")
          Split.Let(holeSymbol, sel(stackSymbol.safeRef, "h"),
            multiple.init.foldRight(upHole(cls, multiple.last, children, inerts, nodeSym, tailSym)): (hole, rest) =>
              Branch(holeSymbol.safeRef, intPattern(hole),
                upHole(cls, hole, children, inerts, nodeSym, tailSym)) ~: rest)
      val withTail = Split.Let(tailSym, sel(stackSymbol.safeRef, "t"), core)
      val withNode = Split.Let(nodeSym, sel(stackSymbol.safeRef, "n"), withTail)
      val withInerts = inerts.iterator.zipWithIndex.foldRight(withNode):
        case ((symbol, index), rest) =>
          Split.Let(symbol, sel(stackSymbol.safeRef, inertField(index)), rest)
      children.iterator.zipWithIndex.foldRight(withInerts):
        case ((symbol, index), rest) =>
          Split.Let(symbol, sel(stackSymbol.safeRef, childField(index)), rest)
    val upSplit =
      // An empty stack means the whole scrutinee is normal: we are done.
      val done = perform(
        setStmt(resultSymbol, focusSymbol.safeRef),
        setStmt(modeSymbol, int(ModeDone)))
      val frameDispatch = classes match
        case Nil => Split.End // No frames are ever pushed.
        case only :: Nil => upClass(only)
        case multiple =>
          val tagSymbol = TempSymbol(N, "frameTag")
          Split.Let(tagSymbol, sel(stackSymbol.safeRef, "tag"),
            multiple.init.foldRight(upClass(multiple.last)): (cls, rest) =>
              Branch(tagSymbol.safeRef, intPattern(cls.index), upClass(cls)) ~: rest)
      Branch(stackSymbol.safeRef, FlatPattern.Lit(UnitLit(true)), done) ~: frameDispatch

    // When the mode is `ModeDone`, no branch matches and the loop exits.
    val loop =
      Branch(modeSymbol.safeRef, intPattern(ModeFind), findSplit) ~:
      Branch(modeSymbol.safeRef, intPattern(ModeUp), upSplit) ~:
      Split.End

    val prelude =
      (redexImpls ::: sideImpls ::: postMatcherOpt.fold(Nil)(_._2)).flatMap: (symbol, params, body) =>
        LetDecl(symbol, Nil) :: DefineVar(symbol, Term.Lam(params, body)) :: Nil
      ::: List(
        LetDecl(modeSymbol, Nil), DefineVar(modeSymbol, int(ModeFind)),
        LetDecl(focusSymbol, Nil), DefineVar(focusSymbol, inputSymbol.safeRef),
        LetDecl(stackSymbol, Nil), DefineVar(stackSymbol, `null`),
        LetDecl(resultSymbol, Nil), DefineVar(resultSymbol, `null`))
      ::: (if requireProgress then
        LetDecl(progressedSymbol, Nil) :: DefineVar(progressedSymbol, bool(false)) :: Nil
      else Nil)

    // Succeed with the normal form, post-processed by the trailing
    // alternatives when present. In the one-or-more shape the first step is
    // required, so a run with zero contractions fails instead; in the
    // zero-or-more shape, zero contractions are fine and the trailing
    // alternatives process the original scrutinee.
    val success = postMatcherOpt match
      case S((postMatcher, _)) =>
        callMatcher(postMatcher, resultSymbol.safeRef, "post-processed result")
      case N => makeMatchSuccess(resultSymbol.safeRef)
    val result = Term.SynthIf(
      if requireProgress then
        Branch(progressedSymbol.safeRef, Split.Else(success)) ~:
        Split.Else(makeMatchFailure())
      else Split.Else(success))

    Machine(paramList(param(inputSymbol)), prelude, loop, result)
