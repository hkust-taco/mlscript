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
    * exits when no branch of the split matches), then return `result`. When
    * `naiveFallback` is set (non-catch-all definitions), a failed machine run
    * must be retried with the naive backtracking translation, which
    * implements the deepest-first try order on intermediate results. */
  final case class Machine(params: ParamList, prelude: Ls[Statement], loop: Split, result: Term, naiveFallback: Bool)

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
  * Note that `as` binds looser than `|`, so the definition above reads
  * `Step as (Steps | _)`: one step must succeed, after which the iteration
  * continues until no further step is possible. Hence the compiled matcher
  * fails when not even one rewriting step applies, and otherwise outputs the
  * normal form of the scrutinee.
  *
  * The recognized shape is `pattern S = P as (S | a1 | ... | ak | _)` — the
  * middle alternatives `a1 ... ak` are optional and, since the recursive
  * alternative fails exactly when `P` cannot step, are matched once against
  * the final normal form — where `P` instantiates (possibly through synonyms)
  * to a self-recursive "evaluation context" disjunction whose alternatives
  * are, in order:
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
  * regular multi-matcher compilation; fixed-point-shaped patterns whose
  * context alternatives are unsupported get a warning and fall back.
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
    *     The `unapply` translation then reaches this method with the chain.
    *
    * Returns the machine paired with the optional output sub-pattern, or `N`
    * when the pattern is not fixed-point shaped — in which case the caller
    * should proceed with the regular efficient compilation. */
  def compile(pattern: SP): Opt[(Machine, Opt[SP])] = pattern match
    case SP.Constructor(target, arguments) =>
      target.resolvedSym.flatMap(_.asPat).flatMap: patternSymbol =>
        patternSymbol.defn match
          case S(defn) if defn.patternParams.isEmpty && defn.extractionParams.isEmpty =>
            recognizeBody(stripAnnotations(defn.pattern), patternSymbol).flatMap: (stepPattern, middles, catchAll) =>
              val outputPattern = arguments match
                case N | S(Nil) => S(N)
                case S(sole :: Nil) => S(S(sole))
                // Several arguments are not understood by fixed-point
                // patterns; let the regular path report the mismatch.
                case S(_) => N
              outputPattern.flatMap: outputPattern =>
                scoped("ucs:fixpoint")(compileMachine(stepPattern, middles, catchAll)).map((_, outputPattern))
          case _ => N
    case chain: SP.Chain =>
      // The body-annotated form. The chain must be the body of the very
      // definition its tail refers to — `P as (Other | _)` with a foreign
      // `Other` is a plain chain, not a fixed point. The `eq` check suffices
      // because the `unapply` translation passes the definition's own body
      // node down to here.
      def isOwnBody(patternSymbol: PatternSymbol): Bool =
        patternSymbol.defn.exists(defn =>
          (stripAnnotations(defn.pattern) eq chain) &&
            defn.patternParams.isEmpty && defn.extractionParams.isEmpty)
      selfRefSymbol(chain) match
        case S(patternSymbol) if isOwnBody(patternSymbol) =>
          recognizeBody(chain, patternSymbol).flatMap: (stepPattern, middles, catchAll) =>
            scoped("ucs:fixpoint")(compileMachine(stepPattern, middles, catchAll)).map((_, N))
        case _ => N
    case _ => N

  /** Remove `Annotated` wrappers (such as the `@compile` marking itself). */
  @tailrec private def stripAnnotations(pattern: SP): SP = pattern match
    case SP.Annotated(pattern, _) => stripAnnotations(pattern)
    case _ => pattern

  /** Flatten nested disjunctions into the list of their alternatives. */
  private def disjuncts(pattern: SP): Ls[SP] = pattern match
    case SP.Composition(true, left, right) => disjuncts(left) ::: disjuncts(right)
    case _ => pattern :: Nil

  /** If the pattern is a chain of the form `P as (S | ...)`, return the
    * pattern symbol `S` refers to. */
  private def selfRefSymbol(pattern: SP): Opt[PatternSymbol] = pattern match
    case SP.Chain(_, tail) => disjuncts(tail) match
      case SP.Constructor(target, N) :: _ => target.resolvedSym.flatMap(_.asPat)
      case _ => N
    case _ => N

  /** Recognize `P as (S | a1 | ... | ak | _)` — with the trailing wildcard
    * being optional — where `S` is the given pattern symbol, and return `P`,
    * the middle alternatives `a1 ... ak`, and whether the wildcard is
    * present. Since the recursive alternative fails exactly when `P` cannot
    * step, the middle alternatives are matched once, against the final
    * normal form. Without the wildcard, the naive semantics additionally
    * backtracks to the latest intermediate result matching an alternative,
    * which the machine handles by retrying with the naive translation.
    * Note that `as` binds looser than `|`, so this is what
    * `pattern S = P as S | a1 | ... | ak | _` parses to. */
  private def recognizeBody(pattern: SP, self: PatternSymbol): Opt[(SP, Ls[SP], Bool)] = pattern match
    case SP.Chain(stepPattern, tail) => disjuncts(tail) match
      case SP.Constructor(target, N) :: rest
          if target.resolvedSym.flatMap(_.asPat).exists(_ is self) && rest.nonEmpty =>
        val catchAll = rest.last.isInstanceOf[SP.Wildcard]
        val middles = if catchAll then rest.init else rest
        if middles.exists(_.isInstanceOf[SP.Wildcard]) then N
        else S((stepPattern, middles, catchAll))
      case _ => N
    case _ => N

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

  private def compileMachine(stepPattern: SP, middles: Ls[SP], catchAll: Bool): Opt[Machine] =
    // Instantiate the step pattern, monomorphizing higher-order patterns such
    // as `Ctx(Redex)` into first-order synonyms. The middle alternatives are
    // instantiated with the same instantiator so that the last returned
    // context covers all of them.
    val instantiator = new Instantiator
    val (entry, context0) = instantiator(stepPattern)
    var context = context0
    val middlePatterns = middles.map: middle =>
      val (middlePattern, newerContext) = instantiator(middle)
      context = newerContext
      middlePattern
    // The post pattern processes the final normal form; the definition's
    // trailing wildcard, when present, makes it total.
    val post =
      if catchAll then
        if middlePatterns.isEmpty then N else S(Or(middlePatterns :+ Wildcard))
      else S(Or(middlePatterns))
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
        S(assemble(entry, Nil, post, !catchAll))
      case S((ctxInst, body)) =>
        log(s"Recursive context: ${ctxInst.showDbg}")
        val alternatives = body match
          case Or(alternatives) => alternatives
          case pattern => pattern :: Nil
        classify(ctxInst, alternatives).map: (redexAlternatives, classes) =>
          val redexPattern = redexAlternatives match
            case single :: Nil => single
            case multiple => Or(multiple)
          assemble(redexPattern, classes, post, !catchAll)

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
    if descentAlternatives.exists(pattern => !mentions(pattern, ctxInst)) then
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

  /** Assemble the machine: matcher functions for the redex and the side
    * conditions (reusing the non-backtracking `ups.Compiler`), the state
    * variables, and the `find`/`up` transition split executed in a loop. */
  private def assemble(redexPattern: Pat, classes: Ls[ClassInfo], post: Opt[Pat], naiveFallback: Bool)(using Context): Machine =
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
    // Whether at least one contraction has fired. The chain `P as (S | _)`
    // requires the first step to succeed, so a run with zero contractions is
    // a match failure.
    val progressedSymbol = TempSymbol(N, "progressed")

    def setStmt(symbol: LocalVarSymbol, value: Term): Statement = Term.Assgn(symbol.safeRef, value)
    // A leaf of the loop split: execute the state updates; the `while` form
    // then re-enters the loop from the top.
    def perform(stmts: Statement*): Split =
      Split.Else(Term.Blk(stmts.toList, Term.Lit(UnitLit(false))))
    def bool(value: Bool): Term = Term.Lit(BoolLit(value))
    def intPattern(value: Int): FlatPattern = FlatPattern.Lit(IntLit(BigInt(value)))
    def constructorTerm(cls: ClassInfo): Term =
      Compiler.reference(cls.symbol, N).getOrElse(Term.Error)
    def classPattern(cls: ClassInfo, children: Ls[TempSymbol]): FlatPattern =
      FlatPattern.ClassLike(constructorTerm(cls), cls.symbol, S(children.map(_ -> N)), false)(Tree.Dummy)
    def callMatcher(matcher: LocalVarSymbol, argument: Term, label: Str): Term =
      app(matcher.safeRef, tup(fld(argument)), label)

    // ---- Context frames ----
    // A frame is a record reifying a one-hole context layer: the constructor
    // (as an integer tag), the current children, one inertness flag per child
    // position (true when that subtree is known to be strategy-normal), the
    // hole position we descended into, and the rest of the stack.
    def childField(index: Int) = s"c$index"
    def inertField(index: Int) = s"i$index"
    def mkFrame(cls: ClassInfo, hole: Int, child: Int => Term, inert: Int => Term, tail: Term): Term =
      Term.Rcd(false,
        RcdField(str("tag"), int(cls.index)) ::
        List.tabulate(cls.paramCount)(index => RcdField(str(childField(index)), child(index))) :::
        List.tabulate(cls.paramCount)(index => RcdField(str(inertField(index)), inert(index))) :::
        RcdField(str("h"), int(hole)) ::
        RcdField(str("t"), tail) :: Nil)

    /** Chain the side-condition tests of one alternative. `failure` is
      * re-invoked at every failure point so the generated split tree never
      * shares nodes (sharing would confuse later passes). */
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
      val bindingsSym = TempSymbol(N, "contractumBindings")
      Split.Let(resultSym, callMatcher(redexMatcher, scrutinee, "redex match"),
        Branch(resultSym.safeRef, matchSuccessPattern(S(outputSym :: bindingsSym :: Nil)),
          onSuccess(outputSym)) ~: onFailure)

    // ---- `find` mode: search the focus downwards for a redex ----
    // The focus is exhausted: switch to `up` mode to re-examine the parent.
    def goUp(): Split = perform(setStmt(modeSymbol, int(ModeUp)))
    def findDescend(cls: ClassInfo, children: Ls[TempSymbol]): Split =
      val chain = cls.alts.foldRight(() => goUp()): (alt, rest) =>
        () =>
          val push = perform(
            setStmt(stackSymbol, mkFrame(cls, alt.holeIndex,
              index => children(index).safeRef, _ => bool(false), stackSymbol.safeRef)),
            setStmt(focusSymbol, children(alt.holeIndex).safeRef))
          sideChecks(alt.sides, index => children(index).safeRef, push, rest)
      chain()
    val findSplit =
      val classChain = classes.foldRight(goUp()): (cls, rest) =>
        val children = List.tabulate(cls.paramCount)(index => TempSymbol(N, s"scrut$index"))
        Branch(focusSymbol.safeRef, classPattern(cls, children), findDescend(cls, children)) ~: rest
      matchRedex(focusSymbol.safeRef,
        // A contraction: refocus on the contractum and keep searching. This
        // is the step that avoids restarting from the root.
        contractum => perform(
          setStmt(focusSymbol, contractum.safeRef),
          setStmt(progressedSymbol, bool(true))),
        classChain)

    // ---- `up` mode: the focus is inert; re-examine the topmost frame ----
    // We re-test only what the contraction(s) below may have changed: whether
    // the rebuilt node is now a redex (the hole alternative would fire first
    // on a naive restart) and which descent alternatives become enabled.
    // Positions marked inert are skipped — their subtrees were exhausted by
    // earlier descents and cannot have changed since.
    def upHole(cls: ClassInfo, hole: Int, children: Ls[TempSymbol], inerts: Ls[TempSymbol], tailSym: TempSymbol): Split =
      def child(index: Int): Term =
        if index == hole then focusSymbol.safeRef else children(index).safeRef
      def inert(index: Int): Term =
        if index == hole then bool(true) else inerts(index).safeRef
      val rebuiltSymbol = TempSymbol(N, "rebuilt")
      val pop = () => perform(
        setStmt(stackSymbol, tailSym.safeRef),
        setStmt(focusSymbol, rebuiltSymbol.safeRef))
      val altChain = cls.alts.foldRight(pop): (alt, rest) =>
        // The position we just returned from is inert by construction.
        if alt.holeIndex == hole then rest
        else () =>
          val move = perform(
            setStmt(stackSymbol, mkFrame(cls, alt.holeIndex, child, inert, tailSym.safeRef)),
            setStmt(focusSymbol, child(alt.holeIndex)),
            setStmt(modeSymbol, int(ModeFind)))
          Branch(inerts(alt.holeIndex).safeRef, FlatPattern.Lit(BoolLit(false)),
            sideChecks(alt.sides, child, move, rest)) ~: rest()
      Split.Let(rebuiltSymbol,
        `new`(constructorTerm(cls), tup(List.tabulate(cls.paramCount)(child)) :: Nil, s"rebuilt ${cls.symbol.nme}"),
        matchRedex(rebuiltSymbol.safeRef,
          contractum => perform(
            setStmt(stackSymbol, tailSym.safeRef),
            setStmt(focusSymbol, contractum.safeRef),
            setStmt(modeSymbol, int(ModeFind)),
            setStmt(progressedSymbol, bool(true))),
          altChain()))
    def upClass(cls: ClassInfo): Split =
      val children = List.tabulate(cls.paramCount)(index => TempSymbol(N, s"frameChild$index"))
      val inerts = List.tabulate(cls.paramCount)(index => TempSymbol(N, s"frameInert$index"))
      val tailSym = TempSymbol(N, "frameTail")
      val core = cls.alts.map(_.holeIndex).distinct match
        case only :: Nil => upHole(cls, only, children, inerts, tailSym)
        case multiple =>
          val holeSymbol = TempSymbol(N, "frameHole")
          Split.Let(holeSymbol, sel(stackSymbol.safeRef, "h"),
            multiple.init.foldRight(upHole(cls, multiple.last, children, inerts, tailSym)): (hole, rest) =>
              Branch(holeSymbol.safeRef, intPattern(hole),
                upHole(cls, hole, children, inerts, tailSym)) ~: rest)
      val withTail = Split.Let(tailSym, sel(stackSymbol.safeRef, "t"), core)
      val withInerts = inerts.iterator.zipWithIndex.foldRight(withTail):
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
        LetDecl(resultSymbol, Nil), DefineVar(resultSymbol, `null`),
        LetDecl(progressedSymbol, Nil), DefineVar(progressedSymbol, bool(false)))

    // Succeed with the normal form if at least one contraction fired —
    // post-processed by the middle alternatives when present; otherwise the
    // first step failed, so the whole chain fails.
    val success = postMatcherOpt match
      case S((postMatcher, _)) =>
        callMatcher(postMatcher, resultSymbol.safeRef, "post-processed result")
      case N => makeMatchSuccess(resultSymbol.safeRef)
    val result = Term.SynthIf(
      Branch(progressedSymbol.safeRef, Split.Else(success)) ~:
      Split.Else(makeMatchFailure()))

    Machine(paramList(param(inputSymbol)), prelude, loop, result, naiveFallback)
