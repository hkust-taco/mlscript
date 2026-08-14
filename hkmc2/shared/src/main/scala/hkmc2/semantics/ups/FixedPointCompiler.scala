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
  final case class ClassInfo(index: Int, head: ClassLikeHead, symbol: ClassSymbol, paramCount: Int, alts: Ls[AltInfo])

  /** The compiled fixed-point matcher. The `unapply` body is assembled by
    * `Lowering` as: evaluate `prelude`, run `loop` as a `while` form (the loop
    * exits when no branch of the split matches), then return `result`. */
  final case class Machine(params: ParamList, prelude: Ls[Statement], loop: Split, result: Term)

  /** One link of an indirect recursion cycle: the definition it comes from,
    * its steps, its trailing alternatives, and whether they end in a
    * wildcard. */
  private type Link = (PatternSymbol, Ls[Ls[SP]], Ls[SP], Bool)

  /** What `compile` makes of a pattern: `N` when it is not fixed-point shaped
    * at all, so the regular compilation should take over; `L` with the reason
    * when the shape is recognized but rejected before any machine is built,
    * which `unsupported` reports at the pattern that asked for it; `R(N)` when
    * a build was attempted and gave up, having reported its own diagnostic
    * with its own locations; and `R(S(_))` when it succeeded. */
  private type Attempt[A] = Opt[Message \/ Opt[A]]

  /** Why a fixed-point definition cannot be machine-compiled, as the bits to
    * append to the warning. A rejection always names two patterns that are
    * not adjacent in the source, and a `Loc` is a single contiguous range, so
    * each gets a bit of its own rather than one message over a location
    * spanning everything in between. */
  private type Rejection = Ls[(Message, Opt[Loc])]

  /** The outcome of `compile` on a fixed-point-shaped pattern. */
  enum Outcome:
    /** The compiled machine, paired with the output sub-pattern of the
      * match-site shorthand (`x is @compile S(q)`). A compiled machine is
      * always a *complete* implementation of the pattern: a failed run means
      * the match failed, never that something else should be tried. This is
      * what keeps `@compile` from performing any rewriting step twice. */
    case Compiled(machine: Machine, outputPattern: Opt[SP])
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
  * A trailing wildcard is not required: `pattern S = P as S | a` is also a
  * fixed point. Its naive meaning, however, is subtler than "normalize, then
  * match `a`" — the alternatives are disjuncts of the whole chains rather
  * than of their tails, so `a` is tried against *every* intermediate result,
  * latest first. The machine only ever produces the normal form, so it
  * implements such a definition only when no intermediate could have matched
  * `a` anyway; `unmatchedIntermediates` decides that and rejects the machine
  * compilation otherwise. Rejecting is the point: compiling a machine and
  * retrying a failed run naively — which is what this used to do — performs
  * every rewriting step twice, and for a definition whose own `unapply`
  * embeds the machine, the retry re-enters it once per step, for a quadratic
  * number of contractions. Both are observable as soon as a transformation
  * has side effects.
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
              patternSymbol.fixedPointMachine match
                case S(machine) => S(Outcome.Compiled(machine, outputPattern))
                case N =>
                  // A self-recursive body is the definition's own fixed point;
                  // otherwise the definition may be a link of an indirect
                  // recursion cycle.
                  val machine: Attempt[Machine] =
                    recognizeShape(stripAnnotations(defn.pattern)).map:
                      (tailSymbol, steps, rest, requireProgress) =>
                        if tailSymbol is patternSymbol then
                          classifyRest(rest).map: (middles, catchAll) =>
                            scoped("ucs:fixpoint")(compileMachine(
                              steps, middles, catchAll, requireProgress, pattern.toLoc))
                        else recognizeCycle(patternSymbol).map: links =>
                          scoped("ucs:fixpoint")(compileAlternatingMachine(links, pattern.toLoc))
                  machine match
                    case S(R(S(machine))) =>
                      patternSymbol.fixedPointMachine = S(machine)
                      S(Outcome.Compiled(machine, outputPattern))
                    // A machine build that was *attempted* and gave up has
                    // already reported a specific diagnostic of its own.
                    case S(R(N)) => S(Outcome.Unsupported)
                    case S(L(reason)) => unsupported(reason, pattern.toLoc)
                    case N => N
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
      val machine: Attempt[(PatternSymbol, Machine)] = recognizeShape(body).map:
        case (patternSymbol, steps, rest, requireProgress) if isOwnBody(patternSymbol) =>
          classifyRest(rest).map: (middles, catchAll) =>
            scoped("ucs:fixpoint")(compileMachine(
              steps, middles, catchAll, requireProgress, body.toLoc))
              .map((patternSymbol, _))
        case (tailSymbol, _, _, _) =>
          // The body may be a link of an indirect recursion cycle; its tail
          // then refers to the next link rather than the definition itself.
          // Locate the definition the body belongs to in the cycle and
          // rotate its link to the front.
          recognizeCycle(tailSymbol).flatMap: links =>
            links.indexWhere((symbol, _, _, _) =>
              symbol.defn.exists(defn => stripAnnotations(defn.pattern) eq body)) match
              case -1 => L(
                msg"`@compile` has to be placed on the whole body of a definition " +
                  msg"taking part in the recursion through `${tailSymbol.nme}`.")
              case index =>
                val rotated = links.drop(index) ::: links.take(index)
                R(scoped("ucs:fixpoint")(compileAlternatingMachine(rotated, body.toLoc))
                  .map((rotated.head._1, _)))
      machine match
        case S(R(S((owner, machine)))) =>
          owner.fixedPointMachine = S(machine)
          S(Outcome.Compiled(machine, N))
        case S(R(N)) => S(Outcome.Unsupported)
        case S(L(reason)) => unsupported(reason, body.toLoc)
        case N => N
    case _ => N

  /** Report a fixed-point-shaped pattern the machine compilation rejected
    * before it got as far as building anything, and route the caller to the
    * naive translation, which handles all such shapes. Rejections found during
    * the build report themselves, with their own locations. */
  private def unsupported(reason: Message, loc: Opt[Loc]): Opt[Outcome] =
    warn(msg"This fixed-point pattern is not supported by pattern compilation." -> loc,
      reason -> N, msg"Falling back to the naive translation." -> N)
    S(Outcome.Unsupported)

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
    * alternatives and the optional trailing wildcard, or say why they cannot
    * be. */
  private def classifyRest(rest: Ls[SP]): Message \/ (Ls[SP], Bool) =
    if rest.isEmpty then
      L(msg"It has only recursive alternatives, so a match can never finish.")
    else
      val catchAll = rest.last.isInstanceOf[SP.Wildcard]
      val middles = if catchAll then rest.init else rest
      // Reject non-trailing wildcards (they make later alternatives
      // unreachable) and chains (recursive alternatives must be leading).
      if middles.exists(_.isInstanceOf[SP.Wildcard]) then
        L(msg"A wildcard alternative makes the alternatives after it unreachable.")
      else if middles.exists(_.isInstanceOf[SP.Chain]) then
        L(msg"Its recursive alternatives must come before its other alternatives.")
      else R((middles, catchAll))

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
    * Return the symbol, the steps, the trailing alternatives (to be validated
    * with `classifyRest`), and whether at least one step is required.
    *
    * A step is returned as the list of its own alternatives, and the steps are
    * kept apart rather than merged into one disjunction: instantiation maps
    * `|` to the flattening `or` combinator, which loses both the grouping the
    * rejection checks depend on and the source pattern their diagnostics point
    * at. The grouping matters because only *distinct* steps branch the naive
    * search — a step written as a disjunction commits to the first of its
    * alternatives that applies (see `unmatchedIntermediates`). */
  private def recognizeShape(pattern: SP): Opt[(PatternSymbol, Ls[Ls[SP]], Ls[SP], Bool)] =
    pattern match
      case SP.Chain(stepPattern, tail) => disjuncts(tail) match
        case SP.Constructor(target, N) :: rest =>
          target.resolvedSym.flatMap(_.asPat).map((_, disjuncts(stepPattern) :: Nil, rest, true))
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
            (symbol, steps.map(disjuncts), rest, false)
        case _ => N
      case _ => N

  /** Recognize an indirect recursion cycle of fixed-point definitions
    * starting from `start`: each body is `(step as Next) | rest` where
    * `Next` refers to the following definition, and the last one refers back
    * to `start`. The semantics is left-biased alternation: the steps fire in
    * cycle order, and whenever a step fails, the failing link's alternatives
    * process the current term — the original scrutinee when even the first
    * step fails. Returns the links in cycle order, beginning with `start`'s
    * own.
    *
    * One-or-more links (`step as (Next | rest)`) are rejected: they fail
    * outright when their step does not apply, whereas `assembleAlternating`
    * has no notion of required progress and would let the failing link's
    * alternatives process the term regardless. */
  private def recognizeCycle(start: PatternSymbol): Message \/ Ls[Link] =
    @tailrec def walk(current: PatternSymbol, acc: Ls[Link]): Message \/ Ls[Link] =
      val linkOpt = current.defn match
        case S(defn) if defn.patternParams.isEmpty && defn.extractionParams.isEmpty =>
          recognizeShape(stripAnnotations(defn.pattern)) match
            case S((next, steps, rest, requireProgress)) =>
              classifyRest(rest).flatMap: (middles, catchAll) =>
                if requireProgress then L(
                  msg"`${current.nme}` does not match unless its first pattern does, " +
                    msg"which is not supported for mutually recursive definitions.")
                else R((next, (current, steps, middles, catchAll)))
            case N => L(
              msg"`${current.nme}` does not recurse back, so this pattern applies once rather than repeatedly.")
        case _ => L(
          msg"The recursion goes through `${current.nme}`, which is not a parameterless pattern definition.")
      linkOpt match
        case R((next, link)) =>
          if next is start then R((link :: acc).reverse)
          else if (next is current) || acc.exists(_._1 is next) then
            L(msg"The recursion goes through `${current.nme}` but never comes back to `${start.nme}`.")
          else walk(next, link :: acc)
        case L(reason) => L(reason)
    walk(start, Nil) match
      // Cycles of length one are the direct shape, handled in `compile`.
      case R(_ :: Nil) => L(
        msg"`${start.nme}` is recursive and must be compiled as a whole" +
          msg" (rather than just part of it).")
      case recognized => recognized

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

  /** A fixed-point definition's two halves — its steps, of which there is
    * always at least one, each given as its own alternatives, and its trailing
    * alternatives — with every source pattern paired with its instantiation.
    * The rejection checks work on the instantiated patterns, while their
    * diagnostics point at the source ones: instantiated patterns are rebuilt
    * nodes, most of which carry no location, and a synonym's is its definition
    * rather than its use. */
  private case class Halves(steps: Ls[Ls[(SP, Pat)]], alternatives: Ls[(SP, Pat)], catchAll: Bool):
    /** The pattern the machine takes its rewriting steps with. */
    val entry: Pat = steps.iterator.flatten.map(_._2).reduceLeft(_ or _)
    /** The pattern processing the final normal form. */
    val post: Opt[Pat] = postPattern(alternatives.map(_._2), catchAll)

  /** Split `items` into consecutive runs of the given sizes. */
  private def regroup[A](sizes: Ls[Int], items: Ls[A]): Ls[Ls[A]] = sizes match
    case Nil => Nil
    case size :: rest =>
      val (group, remaining) = items.splitAt(size)
      group :: regroup(rest, remaining)

  /** Instantiate the halves of each definition, sharing one `Instantiator`
    * across them all as `instantiateGroups` does. */
  private def instantiateHalves(groups: Ls[(Ls[Ls[SP]], Ls[SP], Bool)]): (Ls[Halves], Context) =
    val (instantiated, context) =
      instantiateGroups(groups.map((steps, middles, _) => steps.flatten ::: middles))
    val halves = instantiated.zip(groups).map: (patterns, group) =>
      val (steps, middles, catchAll) = group
      val sizes = steps.map(_.size)
      val (stepPatterns, middlePatterns) = patterns.splitAt(sizes.sum)
      val stepGroups = steps.zip(regroup(sizes, stepPatterns)).map((sources, instantiated) =>
        sources.zip(instantiated))
      Halves(stepGroups, middles.zip(middlePatterns), catchAll)
    (halves, context)

  /** Can a single value match both patterns? Conservatively `true` whenever
    * disjointness cannot be proved, reusing the same subtyping knowledge the
    * UCS normalizer applies to branch elimination. */
  private def mayOverlap(left: Pat, right: Pat)(using Context): Bool =
    // Only the symbol and the literal matter to `areProvablyDisjoint`; the
    // constructor term of a `FlatPattern.ClassLike` is never inspected by it.
    def flatten(head: Head): FlatPattern = head match
      case lit: syntax.Literal => FlatPattern.Lit(lit)
      case head: ClassLikeHead => flattenClassLike(head)
    def flattenClassLike(head: ClassLikeHead): FlatPattern =
      FlatPattern.ClassLike(
        Compiler.preservedReference(head.constructor), head.symbol, N, false)(Tree.Dummy)
    (left.matchableHeads, right.matchableHeads) match
      case (S(leftHeads), S(rightHeads)) => leftHeads.exists: leftHead =>
        rightHeads.exists: rightHead =>
          !ucs.Normalization.areProvablyDisjoint(flatten(leftHead), flatten(rightHead))
      case _ => true

  /** Whether the single post-pattern test the machine performs — against the
    * final normal form — accounts for the whole naive search, and if it does
    * not, the rejection to report.
    *
    * The naive translation of `P as S | a` tries `a` against *every*
    * intermediate result, latest first: it returns `a(x_k)` for the largest
    * `k` such that `a` matches, where `x_0` is the scrutinee, `x_{i+1}` is the
    * result of one `P` step on `x_i`, and `x_n` is the normal form. The
    * machine, on the other hand, only ever produces `x_n`. Two things can
    * therefore go missing, and both are checked here.
    *
    *  1. The strict intermediates `x_k` (`k < n`). Each of them is in the
    *     domain of `P` — that is precisely why a further step was taken from
    *     it — so it is enough that `P` and `a` cannot match the same value.
    *     That is the common case: a step peels a wrapper that `a` rejects.
    *
    *  2. With several recursive alternatives, `P1 as S | ... | Pm as S | a`,
    *     the naive search is a *tree* rather than a chain: `Chain` hands the
    *     enclosing alternative to both of its halves, so when the whole
    *     subtree under `P1` fails, `P2` is retried on the very same term, and
    *     the leaves it leads to are candidates for `a` too. The machine
    *     follows the leftmost path only, so we additionally require the steps
    *     to be mutually exclusive, which collapses the tree back into that
    *     path.
    *
    *     Only *distinct* alternatives branch this way. A single step written
    *     as a disjunction, `(P1 | P2) as S | a`, receives the continuation as
    *     a whole: it commits to the first of its alternatives that applies and
    *     does not reconsider when the rest of the chain fails, so it stays a
    *     chain and needs no mutual exclusion of its own. That is why the steps
    *     arrive here grouped, and are compared group by group. Both readings
    *     are pinned in `RecursionAlternatives.mls`.
    *
    * When either check fails we give up rather than compile a machine and
    * retry a failed run naively: that retry would perform every rewriting
    * step a second time, which is not merely wasteful but observable, since
    * transformations may have side effects. */
  private def unmatchedIntermediates(halves: Halves)(using Context): Opt[Rejection] =
    // Two disjunctions overlap exactly when two of their alternatives do, so
    // taking them apart loses no precision and lets the diagnostics name the
    // two patterns actually in conflict.
    def overlapping(left: Ls[(SP, Pat)], right: Ls[(SP, Pat)]): Opt[(SP, SP)] =
      (for
        (leftSource, leftPattern) <- left.iterator
        (rightSource, rightPattern) <- right.iterator
        if mayOverlap(leftPattern, rightPattern)
      yield (leftSource, rightSource)).nextOption()
    val overlappingSteps = halves.steps.tails.flatMap:
      case first :: rest => rest.iterator.flatMap(overlapping(first, _))
      case Nil => Iterator.empty
    .nextOption()
    overlappingSteps match
      case S((step, other)) =>
        val ol = other.toLoc
        val sl = step.toLoc orElse ol
        S:
          msg"Some recursive alternatives can rewrite the same term in more than one way${
            if sl.isEmpty then msg"" else msg", including this one"}" -> step.toLoc ::
          (if ol.isEmpty then Nil else
            msg"and this one." -> other.toLoc :: Nil)
      // Every alternative of every step is checked against the trailing
      // alternatives: a strict intermediate is one some step produced, whichever.
      case N => overlapping(halves.steps.flatten, halves.alternatives).map: (step, alternative) =>
        msg"A term this pattern can still rewrite" -> step.toLoc ::
        msg"can also be matched by a trailing alternative." -> alternative.toLoc :: Nil

  /** Report a rejection. The head bit states the failure at `origin`, the
    * pattern whose `@compile` asked for the machine — that is where the
    * warning comes from, and where a definition used at several match sites
    * produces one warning per site. The rejection's own bits then point at the
    * individual patterns at fault, which live in the definition. */
  private def warnUnmatchedIntermediates(rejection: Rejection, origin: Opt[Loc]): Unit =
    warn(msg"This fixed-point pattern is not supported by pattern compilation." -> origin ::
      rejection ::: (msg"Falling back to the naive translation." -> N) :: Nil*)
  
  private def compileMachine(steps: Ls[Ls[SP]], middles: Ls[SP], catchAll: Bool,
      requireProgress: Bool, origin: Opt[Loc]): Opt[Machine] =
    val (halves, context) = instantiateHalves((steps, middles, catchAll) :: Nil)
    val definition = halves.head
    val entry = definition.entry
    val post = definition.post
    given Context = context
    // Walk through synonym definitions until we find a self-recursive one:
    // that instantiation is the evaluation context.
    @tailrec def chase(pattern: Pat, visited: Set[Instantiation]): Opt[(Instantiation, Pat)] =
      pattern match
        case Synonym(inst) if !visited.contains(inst) =>
          val body = inst.body
          if mentions(body, inst) then S((inst, body)) else chase(body, visited + inst)
        case _ => N
    // A total post pattern — which the definition's trailing wildcard, when
    // present, guarantees — always accepts the machine's own normal form, so
    // no intermediate is ever consulted.
    val missing = if post.forall(_.isTotal) then N else unmatchedIntermediates(definition)
    missing match
      case S(rejection) =>
        warnUnmatchedIntermediates(rejection, origin)
        N
      case N => chase(entry, Set.empty) match
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
    def parse(pattern: Pat): Opt[(ClassLikeHead, ClassSymbol, Int, AltInfo)] = pattern match
      case ClassLike(head, S(arguments)) => head.symbol match
        case cls: ClassSymbol =>
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
              else S((head, cls, entries.size, AltInfo(holeIndex, sides)))
            case _ =>
              warn(msg"The recursive context must occur as exactly one direct constructor argument." -> pattern.toLoc)
              N
        case _: ModuleOrObjectSymbol =>
          warn(msg"This alternative is not supported by fixed-point pattern compilation." -> pattern.toLoc)
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
        val classes = order.iterator.zipWithIndex.map: (head, index) =>
          val altsFor = flat.collect { case (`head`, cls, paramCount, alt) => (cls, paramCount, alt) }
          val (cls, paramCount, _) = altsFor.head
          ClassInfo(index, head, cls, paramCount, altsFor.map(_._3))
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

  /** Compile an indirect recursion cycle. Each link contributes its steps and
    * its trailing alternatives, turned into a post pattern as in
    * `compileMachine`. */
  private def compileAlternatingMachine(links: Ls[Link], origin: Opt[Loc]): Opt[Machine] =
    val (halves, context) =
      instantiateHalves(links.map((_, steps, middles, catchAll) => (steps, middles, catchAll)))
    val compiled = halves.map(link => (link.entry, link.post))
    given Context = context
    // The naive translation of a cycle tries link `i`'s alternatives against
    // every intermediate reached after `i` steps, latest first; the machine
    // only ever reaches the last one and consults the link whose step failed.
    // The two agree either because the machine cannot fail — every link's
    // alternatives are total — or, as in `compileMachine`, because no link's
    // alternatives can match a term that link's own step can still rewrite.
    // A mixture of the two is not enough: a partial link can fail on the final
    // term while a total link would have accepted an earlier intermediate,
    // which is why a total link is reported here rather than skipped.
    def isTotal(post: Opt[Pat]): Bool = post.forall(_.isTotal)
    // A total link is at fault as a whole rather than through one of its
    // patterns — its alternatives are just the wildcard — so the declaration
    // it comes from is what the diagnostic points at.
    def declarationOf(symbol: PatternSymbol): Opt[Loc] = symbol.defn.flatMap(_.pattern.toLoc)
    if halves.forall(link => isTotal(link.post)) then S(assembleAlternating(compiled))
    else
      val zipped = halves.zip(links)
      val offending = zipped.iterator.collectFirst:
        Function.unlift: (link, source) =>
          val (symbol, _, _, _) = source
          if isTotal(link.post) then
            // Not every link is total, or we would not be here.
            zipped.collectFirst:
              case (other, (otherSymbol, _, _, _)) if !isTotal(other.post) =>
                msg"One of its recursive parts accepts any term" -> declarationOf(symbol) ::
                msg"while another can fail." -> declarationOf(otherSymbol) :: Nil
          else unmatchedIntermediates(link)
      offending match
        case S(rejection) =>
          warnUnmatchedIntermediates(rejection, origin)
          N
        case N => S(assembleAlternating(compiled))
  
  /** Assemble the flat alternation loop for an indirect recursion cycle: in
    * phase `i`, step `i` is applied to the current term; on success the
    * machine moves to the next phase in the cycle, and on failure it records
    * the failing phase and exits. The failing link's alternatives then process
    * the current term — which is the original scrutinee when the very first
    * step fails, so zero steps are allowed, exactly as for the direct shape.
    * When those alternatives don't match either, the run fails and so does the
    * match: `compileAlternatingMachine` only assembles a machine for cycles
    * whose earlier intermediates could not have matched anyway. */
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
      Compiler.preservedReference(cls.head.constructor)
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
