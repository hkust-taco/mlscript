package hkmc2
package semantics
package ups

import hkmc2.utils.*, shorthands.*

import syntax.Tree, Tree.StrLit
import Elaborator.{Ctx, State, ctx}, utils.TL
import Message.MessageContext, ucs.error
import Pattern.*

import collection.mutable.{Buffer, Map as MutMap, LinkedHashMap, Set as MutSet}

/** Compiles the string fragment of patterns — sequential compositions (`~`),
  * character classes, string literals, alternations, bindings, transforms, and
  * (mutually) tail-recursive pattern references — into a finite automaton that
  * is executed by the runtime engine `Runtime.StrPat`.
  *
  * ## Semantics implemented
  *
  * Recognition is relational: a concatenation matches if *some* split of the
  * scrutinee matches, regardless of how greedy sub-patterns are. Among all
  * successful parses, the committed one (which determines bindings, transform
  * applications, and outputs) is the parse that a recursive-descent matcher
  * with unlimited backtracking would find first, trying alternatives from left
  * to right ("leftmost-greedy by alternation order"). Transforms run exactly
  * once, and only on the committed parse.
  *
  * ## Execution scheme
  *
  * We follow the two-pass scheme of Frisch and Cardelli ("Greedy Regular
  * Expression Matching", ICALP 2004):
  *
  *  1. A *backward* pass runs the determinized reverse automaton from the end
  *     of the input, recording for each position the set of NFA states that
  *     can still reach acceptance by consuming the remaining suffix.
  *  2. A *forward* pass walks the prioritized NFA deterministically: at every
  *     choice point it takes the first branch that the backward pass proved
  *     viable. Value operations (slices, bindings, transform calls) execute on
  *     this committed walk only.
  *
  * Recognition alone (`ResultMode.MatchOnly`-style call sites) only needs the
  * backward automaton, run in a rolling fashion with no allocation.
  *
  * ## Recursion
  *
  * After instantiation, pattern definitions form a grammar whose nonterminals
  * are `Pattern.Instantiation`s. A strongly connected component of that
  * grammar can be compiled to a finite automaton iff every reference to a
  * member of the same SCC sits in *tail position* of its defining body (the
  * grammar is right-linear modulo non-recursive content, cf. Mohri and
  * Nederhof's "strongly regular" grammars). Such references become plain
  * ε-transitions (tail calls compile to gotos). Self-embedding references are
  * rejected with a compile-time error and nothing is compiled.
  *
  * Value operations that syntactically follow a tail call (e.g. the binding
  * and transform in `((L as h) ~ (Tail as t)) => [h, ...t]`) cannot run on the
  * transition itself — the automaton never "returns". They are recorded as
  * deferred frames (`Op.Defer`) carrying the values they capture, and executed
  * innermost-first when the recursive component is finally exited
  * (`Op.Enter`/`Op.Exit` bracket the component).
  */
object StringCompiler:

  /** An inclusive range of UTF-16 code units. Matching is code-unit-based,
    * mirroring the previous runtime helpers (`Str.get`/`startsWith`). */
  type CharRange = (Int, Int)

  val MaxUnit: Int = 0xFFFF

  val AnyChar: Ls[CharRange] = (0, MaxUnit) :: Nil

  /** Value operations attached to ε-transitions. Executed only on the
    * committed forward walk. The value stack discipline is: evaluating a
    * pattern with `needValue` pushes exactly one value (its output).
    */
  enum Op:
    /** Push the current input position onto the mark stack. */
    case Mark
    /** Pop a mark; push the input slice from it to the current position. */
    case Slice
    /** Pop two values; push their string concatenation. */
    case Add
    /** Pop one value. */
    case Drop
    /** Store the top of the value stack (without popping) into a binding slot. */
    case Bind(slot: Int)
    /** Push the result of calling an action closure on the given slots. */
    case Call(actionId: Int, argSlots: Ls[Int])
    /** Push a sentinel delimiting a recursive component's deferred frames. */
    case Enter
    /** Pop and execute deferred frames down to the sentinel, innermost first. */
    case Exit
    /** Record the ops to run at `Exit` time, capturing the listed slots now. */
    case Defer(ops: Ls[Op], captured: Ls[Int])
    /** Record the current position as the start of the remaining string. */
    case Rem

  /** Whether the automaton must consume the entire scrutinee or only a
    * prefix of it (for `unapplyStringPrefix`). */
  enum Mode:
    case Whole, Prefix

  /** The result of compiling one string region.
    *
    * @param table the encoded automaton program (see `encode` for the layout)
    * @param matchTable the recognition-only program for `matchWhole`: just
    *        the reverse scan, omitting the NFA, the operation pool, and the
    *        viability matrix — call sites that only ask *whether* the
    *        scrutinee matches should embed this much smaller table
    * @param actions transform closures, in `actionId` order
    * @param visibleSlots the root-visible bindings and their slot indices, in
    *        the order the caller should destructure them
    * @param pure true when the region carries no value operations at all, so
    *        recognition suffices and a whole-match output is the scrutinee
    */
  final case class Compiled(
      table: Str,
      matchTable: Str,
      actions: Ls[Term],
      visibleSlots: Ls[(VarSymbol, Int)],
      pure: Bool,
  ):
    /** Whether the recognition-only entry point (`matchWhole`) suffices: the
      * region carries no operations at all, or nothing demands its value, its
      * bindings, or its transform effects. Transforms always force the
      * parsing entry point — they run exactly once, on the committed parse,
      * even when the match is only used as a condition (pinned by
      * `ups/regex/CompiledSemantics.mls`). Both region call sites must
      * consult this one predicate so they cannot drift apart. */
    def recognitionSuffices(valueNeeded: Bool): Bool =
      pure || (!valueNeeded && visibleSlots.isEmpty && actions.isEmpty)

  /** Extract the string-shaped fragment of an expanded pattern: everything a
    * `Str`-headed multi-matcher branch should try to match. Non-string leaves
    * become `Never` (they cannot match a string scrutinee).
    */
  def stringFragment(pattern: ExPat)(using Ctx): Pat = pattern.map:
    case pattern: (Concat | CharClass) => pattern
    case pattern @ Literal(_: StrLit) => pattern
    case Literal(_) => Never
    case pattern @ ClassLike(sym, _) =>
      if sym is ctx.builtins.Str then pattern else Never
    case _: (Record | Tuple) => Never
    case _: MatchedClassLike => lastWords("MatchedClassLike encountered in stringFragment")

  /** Whether an expanded pattern contains a string-sequencing node at a
    * position visible to head specialization. Used by the multi-matcher to
    * decide whether string-shaped patterns should be absorbed into a single
    * `Str` head backed by an automaton.
    */
  def containsStringNode(pattern: ExPat): Bool = pattern.reduce[Bool](_.exists(identity)):
    case _: (Concat | CharClass) => true

class StringCompiler(using context: Context)(using tl: TL)(using Ctx, State, Raise):
  import StringCompiler.*, tl.*

  // ------------------------------------------------------------------------
  // Grammar analysis
  // ------------------------------------------------------------------------

  /** Bodies of all instantiations reachable from the region root. */
  private val bodies = LinkedHashMap.empty[Instantiation, Pat]

  /** Walk all sub-patterns in string position. Arguments of dead (non-string)
    * nodes are not traversed: they can never match within a string region. */
  private def stringPositions(pattern: Pat)(f: Pat => Unit): Unit =
    f(pattern)
    pattern match
      case Concat(ps) => ps.foreach(stringPositions(_)(f))
      case Or(ps) => ps.foreach(stringPositions(_)(f))
      case And(ps) => ps.foreach(stringPositions(_)(f))
      case Not(p) => stringPositions(p)(f)
      case Rename(p, _) => stringPositions(p)(f)
      case Extract(p, _, _) => stringPositions(p)(f)
      case _: (Literal | CharClass | ClassLike | MatchedClassLike | Record | Tuple | Synonym) => ()

  private def collectBodies(pattern: Pat): Unit =
    stringPositions(pattern):
      case Synonym(inst) =>
        if !bodies.contains(inst) then
          bodies += inst -> context.get(inst)
          collectBodies(bodies(inst))
      case _ => ()

  private def references(pattern: Pat): Ls[Instantiation] =
    val buffer = Buffer.empty[Instantiation]
    stringPositions(pattern):
      case Synonym(inst) => buffer += inst
      case _ => ()
    buffer.toList

  /** Strongly connected components of the nonterminal reference graph,
    * computed with Tarjan's algorithm. `sccOf` maps each instantiation to its
    * component id; `recursiveSccs` contains components that are actually
    * recursive (more than one member, or a self-loop). */
  private val sccOf = MutMap.empty[Instantiation, Int]
  private val recursiveSccs = MutSet.empty[Int]

  private def computeSccs(): Unit =
    val indices = MutMap.empty[Instantiation, Int]
    val lowLinks = MutMap.empty[Instantiation, Int]
    val onStack = MutSet.empty[Instantiation]
    val stack = Buffer.empty[Instantiation]
    var nextIndex = 0
    var nextScc = 0
    def strongConnect(v: Instantiation): Unit =
      indices(v) = nextIndex
      lowLinks(v) = nextIndex
      nextIndex += 1
      stack += v
      onStack += v
      references(bodies(v)).foreach: w =>
        if !indices.contains(w) then
          strongConnect(w)
          lowLinks(v) = lowLinks(v) min lowLinks(w)
        else if onStack contains w then
          lowLinks(v) = lowLinks(v) min indices(w)
      if lowLinks(v) == indices(v) then
        val sccId = nextScc
        nextScc += 1
        var done = false
        var size = 0
        while !done do
          val w = stack.remove(stack.size - 1)
          onStack -= w
          sccOf(w) = sccId
          size += 1
          if w == v then done = true
        // A single-member component is recursive only if it references itself.
        if size > 1 || references(bodies(v)).contains(v) then
          recursiveSccs += sccId
    bodies.keysIterator.foreach: inst =>
      if !indices.contains(inst) then strongConnect(inst)

  /** Check that every reference to a member of the same (recursive) SCC is in
    * tail position of the body it occurs in: nothing may be consumed after it.
    * References may still sit under alternations and under binding/transform
    * wrappers (whose pending operations are deferred at run time).
    *
    * On failure, the offending reference is pinned in an error message and
    * compilation of the whole region is abandoned.
    */
  private def checkTailPositions(): Unit =
    def check(owner: Instantiation, pattern: Pat, tail: Bool): Unit = pattern match
      case Synonym(inst) =>
        if sccOf.get(inst) == sccOf.get(owner) && !tail then
          failed = true
          error(
            msg"This recursive use of pattern `${inst.symbol.nme}` is not in tail position." -> inst.toLoc,
            msg"Only self references at the end of a string sequence can be compiled to a finite string matcher." -> N,
            msg"The recursion involves this pattern." -> owner.toLoc)
      case Concat(ps) => ps match
        case Nil => ()
        case _ =>
          ps.init.foreach(check(owner, _, false))
          check(owner, ps.last, tail)
      case Or(ps) => ps.foreach(check(owner, _, tail))
      case Rename(p, _) => check(owner, p, tail)
      case Extract(p, _, _) => check(owner, p, tail)
      case And(ps) => ps.foreach(check(owner, _, false))
      case Not(p) => check(owner, p, false)
      case _: (Literal | CharClass | ClassLike | MatchedClassLike | Record | Tuple) => ()
    bodies.foreach: (inst, body) =>
      if sccOf.get(inst).exists(recursiveSccs.contains) then
        check(inst, body, true)

  /** A pattern is pure when matching it involves no value operations: no
    * bindings, no transforms, transitively through pattern references. The
    * output of a pure whole-match is the scrutinee itself, and the consumed
    * part of a pure sub-match is a single slice of the input. Cycles are
    * treated as pure so the traversal stays well-founded; a cycle only ends
    * up pure if every body on it is operation-free. */
  private val pureMemo = MutMap.empty[Instantiation, Bool]

  /** The purity of `pattern`, paired with whether the answer relied on the
    * optimistic assumption made for a cycle. Such an answer is only valid for
    * the query that introduced the assumption, so it must not be memoized:
    * doing so used to let one query's optimistic `true` leak into another's,
    * which made purity depend on the order alternatives happened to be written
    * in (an impure component could be compiled as pure, and the pure-subtree
    * shortcut would then emit an `Op.Mark` whose `Op.Slice` sits on a state the
    * tail-call goto can never reach). Note that the traversal deliberately does
    * not short-circuit on the first impure element: it must visit every branch
    * to learn whether any of them consulted the assumption. */
  private def isPureDeep(pattern: Pat): Bool =
    def all(patterns: Ls[Pat], visiting: Set[Instantiation]): (Bool, Bool) =
      patterns.foldLeft((true, false)):
        case ((pure, assumed), pattern) =>
          val (pure2, assumed2) = loop(pattern, visiting)
          (pure && pure2, assumed || assumed2)
    def loop(pattern: Pat, visiting: Set[Instantiation]): (Bool, Bool) = pattern match
      case _: (Rename[?] | Extract[?]) => (false, false)
      case Concat(ps) => all(ps, visiting)
      case Or(ps) => all(ps, visiting)
      case And(ps) => all(ps, visiting)
      case Not(p) => loop(p, visiting)
      case Synonym(inst) =>
        if visiting contains inst then (true, true)
        else pureMemo.get(inst) match
          case S(pure) => (pure, false)
          case N =>
            val (pure, assumed) = loop(context.get(inst), visiting + inst)
            if !assumed then pureMemo(inst) = pure
            (pure, assumed)
      case _: (Literal | CharClass | ClassLike | MatchedClassLike | Record | Tuple) => (true, false)
    loop(pattern, Set.empty)._1

  // ------------------------------------------------------------------------
  // NFA construction
  // ------------------------------------------------------------------------

  private enum Edge:
    case Chr(ranges: Ls[CharRange], target: Int)
    case Eps(target: Int, ops: Ls[Op])

  private val states = Buffer.empty[Buffer[Edge]]

  private def newState(): Int =
    states += Buffer.empty
    states.size - 1

  private def addChr(from: Int, ranges: Ls[CharRange], target: Int): Unit =
    states(from) += Edge.Chr(ranges, target)

  private def addEps(from: Int, target: Int, ops: Ls[Op]): Unit =
    if ops.nonEmpty then anyOps = true
    states(from) += Edge.Eps(target, ops)

  /** Binding slots, keyed by the bound symbol. */
  private val slots = LinkedHashMap.empty[VarSymbol, Int]

  private def slotOf(symbol: VarSymbol): Int =
    slots.getOrElseUpdate(symbol, slots.size)

  /** Transform closures, in `actionId` order. */
  private val actions = Buffer.empty[Term]

  /** The transform terms backing `actions`, for interning by identity. */
  private val actionSources = Buffer.empty[Term]

  private var failed = false
  private var anyOps = false

  private def fail(messages: (Message, Opt[Loc])*): Unit =
    failed = true
    error(messages*)

  /** The slots that deferred operations read before writing them locally:
    * their values must be captured when the deferred frame is created, not
    * when it is executed (later iterations overwrite the global slots). */
  private def capturedSlots(ops: Ls[Op]): Ls[Int] =
    val written = MutSet.empty[Int]
    val captured = Buffer.empty[Int]
    ops.foreach:
      case Op.Bind(slot) => written += slot
      case Op.Call(_, argSlots) =>
        argSlots.foreach: slot =>
          if !written.contains(slot) && !captured.contains(slot) then captured += slot
      case Op.Defer(_, _) => lastWords("nested deferred operations")
      case _ => ()
    captured.toList

  /** When building the body of a recursive SCC copy, references to members of
    * the same SCC resolve to the copy's entry states. */
  private final case class SccContext(sccId: Int, entries: Map[Instantiation, Int], pure: Bool)

  /** Build the NFA fragment for `pattern`.
    *
    * Completion protocol: every path through the fragment either reaches
    * `cont` via ε-edges that carry the pattern's value operations (pushing
    * exactly one value if `needValue`) followed by `exitOps`, or jumps to a
    * same-SCC entry with those pending operations packaged in a deferred
    * frame.
    */
  private def build(pattern: Pat, cont: Int, needValue: Bool, exitOps: Ls[Op], scc: Opt[SccContext]): Int =
    // Pure subtrees need no internal operations even when their value is
    // demanded: the consumed part is a single slice of the input.
    if (needValue || exitOps.nonEmpty) && isPureDeep(pattern) then
      val sliceOps = if needValue then Op.Slice :: exitOps else exitOps
      val exit = newState()
      addEps(exit, cont, sliceOps)
      val inner = build(pattern, exit, false, Nil, scc)
      if needValue then
        val entry = newState()
        addEps(entry, inner, Op.Mark :: Nil)
        entry
      else inner
    else pattern match
      case Literal(StrLit(value)) =>
        // The value ops (if any) were handled by the pure-subtree shortcut.
        softAssert(!needValue && exitOps.isEmpty, "literal with pending value operations")
        value.foldRight(cont): (unit, next) =>
          val entry = newState()
          addChr(entry, (unit.toInt, unit.toInt) :: Nil, next)
          entry
      case CharClass(lo, hi) =>
        softAssert(!needValue && exitOps.isEmpty, "character class with pending value operations")
        val entry = newState()
        addChr(entry, (lo, hi) :: Nil, cont)
        entry
      case And(Nil) =>
        // The wildcard in string position matches any string, preferring to
        // consume as much as possible (the consuming edge comes first).
        softAssert(!needValue && exitOps.isEmpty, "wildcard with pending value operations")
        val entry = newState()
        addChr(entry, AnyChar, entry)
        addEps(entry, cont, Nil)
        entry
      case ClassLike(sym, arguments) if sym is ctx.builtins.Str =>
        // `Str` with arguments is reported and degraded to `Never` by
        // `Instantiator`, so only the bare form arrives here: it literally
        // means all strings, like a wildcard. (The naive translation used to
        // consume exactly one character here, which made `Str ~ "!"`
        // unmatchable against "ab!".)
        softAssert(arguments.isEmpty,
          "`Str` with arguments must have been rejected during instantiation")
        softAssert(!needValue && exitOps.isEmpty, "Str with pending value operations")
        val entry = newState()
        addChr(entry, AnyChar, entry)
        addEps(entry, cont, Nil)
        entry
      case Or(Nil) => newState() // `Never` matches nothing: a dead state.
      case Or(patterns) =>
        val entry = newState()
        patterns.foreach: p =>
          addEps(entry, build(p, cont, needValue, exitOps, scc), Nil)
        entry
      case Concat(patterns) => patterns match
        case Nil =>
          // An empty sequence matches the empty string. The pure-subtree
          // shortcut has already handled any pending value operations.
          val entry = newState()
          addEps(entry, cont, Nil)
          entry
        case _ =>
          if needValue then
            // Each element contributes its value; concatenate left to right.
            // Elements after the first are followed by an `Add`, and the last
            // one additionally carries the pending exit operations.
            def go(patterns: Ls[Pat], first: Bool): Int = patterns match
              case last :: Nil =>
                val ops = if first then exitOps else Op.Add :: exitOps
                build(last, cont, true, ops, scc)
              case p :: rest =>
                val next = go(rest, false)
                build(p, next, true, if first then Nil else Op.Add :: Nil, scc)
              case Nil => lastWords("unreachable: empty concatenation")
            go(patterns, true)
          else
            def go(patterns: Ls[Pat]): Int = patterns match
              case last :: Nil => build(last, cont, false, exitOps, scc)
              case p :: rest => build(p, go(rest), false, Nil, scc)
              case Nil => lastWords("unreachable: empty concatenation")
            go(patterns)
      case And(_) =>
        fail(msg"Conjunctions are not supported within string patterns yet." -> pattern.diagnosticLoc)
        newState()
      case Not(_) =>
        fail(msg"Negations are not supported within string patterns yet." -> pattern.diagnosticLoc)
        newState()
      case Rename(p, symbol) =>
        val ops = Op.Bind(slotOf(symbol)) :: (if needValue then exitOps else Op.Drop :: exitOps)
        build(p, cont, true, ops, scc)
      case Extract(p, correspondence, term) =>
        // The same transform can be reached several times within one region:
        // expansion shares definition bodies, and references to definitions
        // outside the current recursive component are inlined per reference.
        // Each transform must nevertheless yield exactly one closure — its
        // parameters are the correspondence symbols shared by all copies of
        // the pattern, so duplicating the lambda would define those symbols
        // twice in the lowered block (which `SymbolRefresher` asserts
        // against). Closures are therefore interned by the identity of the
        // transform term.
        //
        // TODO: Interning is per-region, so two regions in one block that
        // reach the same definition's transform still produce two closures
        // sharing parameter symbols. This only trips the refresher when a
        // simplifier pass duplicates a subtree containing both. The principled
        // fix is to host each definition's transforms as methods on the
        // pattern object (compiled once, next to `unapply`) and reference
        // them from regions by selection.
        // The transform's parameters are exactly the symbols the definition
        // itself binds — the ones `correspondence` maps. `p.symbols` can
        // contain more: instantiation substitutes pattern arguments into the
        // body, and a binding inside an argument (`Wrap(("x" as w))`) is
        // visible here but is no parameter of the transform term. Both the
        // parameter list and the argument slots must be derived from the
        // same filtered list: they define the calling convention together,
        // and the closure is interned only once while `argSlots` used to be
        // recomputed per occurrence, so deriving them from `p.symbols` let
        // two instantiations of one definition disagree on arity.
        val transformSymbols = p.symbols.filter(correspondence.contains)
        val actionId = actionSources.indexWhere(_ eq term) match
          case -1 =>
            val params = transformSymbols.map: symbol =>
              Param(FldFlags.empty, correspondence(symbol), N, Modulefulness.none)
            actionSources += term
            actions += Term.Lam(PlainParamList(params), term.mkClone)
            actions.size - 1
          case index => index
        val argSlots = transformSymbols.map(slotOf)
        val ops = Op.Call(actionId, argSlots) :: (if needValue then exitOps else Op.Drop :: exitOps)
        build(p, cont, false, ops, scc)
      case Synonym(inst) => scc match
        case S(sccContext) if sccOf.get(inst).contains(sccContext.sccId) =>
          // A tail call within the current SCC copy compiles to a goto. Any
          // pending operations run when the component is exited.
          val entry = sccContext.entries.getOrElse(inst, lastWords("missing SCC entry"))
          val valueAdjust =
            // Impure SCC copies canonically produce a value; drop it if this
            // reference does not want one.
            if !sccContext.pure && !needValue then Op.Drop :: Nil else Nil
          softAssert(!(sccContext.pure && (needValue || exitOps.nonEmpty)),
            "value operations inside a pure recursive component")
          val pending = valueAdjust ::: exitOps
          val gotoState = newState()
          if pending.isEmpty then addEps(gotoState, entry, Nil)
          else addEps(gotoState, entry, Op.Defer(pending, capturedSlots(pending)) :: Nil)
          gotoState
        case _ => buildReference(inst, cont, needValue, exitOps)
      case _: (Literal | ClassLike | MatchedClassLike | Record | Tuple) =>
        // Non-string patterns can never match within a string region. This
        // mirrors the naive translation, which silently rejected them.
        newState()

  /** Build a reference to an instantiation from outside its SCC. */
  private def buildReference(inst: Instantiation, cont: Int, needValue: Bool, exitOps: Ls[Op]): Int =
    val sccId = sccOf.getOrElse(inst, lastWords("missing SCC id"))
    if !recursiveSccs.contains(sccId) then
      // Non-recursive definitions are inlined at the reference.
      build(bodies(inst), cont, needValue, exitOps, N)
    else if isPureDeep(Synonym(inst)) then
      // Pure recursive components carry no operations; their bodies are
      // recognition-only and tail calls are plain gotos.
      softAssert(!needValue && exitOps.isEmpty,
        "the pure-subtree shortcut should have handled value operations")
      buildSccCopy(inst, sccId, cont, pure = true)
    else
      // Impure recursive components: bracket the copy with Enter/Exit so that
      // frames deferred at internal tail calls unwind exactly here. The
      // pending operations of this reference itself must be deferred too, as
      // the outermost frame of the activation: they may read slots bound
      // before the recursion (e.g. `head` in
      // `(S as head) ~ "," ~ (CommaSep(S) as tail) => head :: tail`
      // when this occurrence sits outside the recursive component), and the
      // recursion overwrites those slots — so their values are captured now
      // and the operations run after all inner frames have unwound.
      val exitState = newState()
      addEps(exitState, cont, Op.Exit :: Nil)
      val copyEntry = buildSccCopy(inst, sccId, exitState, pure = false)
      val entry = newState()
      val pending = (if needValue then Nil else Op.Drop :: Nil) ::: exitOps
      val entryOps = Op.Enter ::
        (if pending.isEmpty then Nil else Op.Defer(pending, capturedSlots(pending)) :: Nil)
      addEps(entry, copyEntry, entryOps)
      entry

  /** Materialize one copy of a recursive SCC, returning the entry state of
    * `inst`. All members share the continuation: since internal references
    * are tail calls, completing any member's body completes the component. */
  private def buildSccCopy(inst: Instantiation, sccId: Int, cont: Int, pure: Bool): Int =
    val members = bodies.keysIterator.filter(sccOf.get(_).contains(sccId)).toList
    val entries = members.map(_ -> newState()).toMap
    val sccContext = SccContext(sccId, entries, pure)
    members.foreach: member =>
      val bodyEntry = build(bodies(member), cont, needValue = !pure, Nil, S(sccContext))
      addEps(entries(member), bodyEntry, Nil)
    entries(inst)

  // ------------------------------------------------------------------------
  // NFA reduction
  // ------------------------------------------------------------------------

  private def edgeTarget(edge: Edge): Int = edge match
    case Edge.Chr(_, target) => target
    case Edge.Eps(target, _) => target

  private def retarget(edge: Edge, target: Int): Edge = edge match
    case Edge.Chr(ranges, _) => Edge.Chr(ranges, target)
    case Edge.Eps(_, ops) => Edge.Eps(target, ops)

  /** Rewrite the target of every edge through `f`; returns whether any
    * edge changed. */
  private def retargetAll(edges: Buffer[Edge])(f: Int => Int): Bool =
    var changed = false
    var i = 0
    while i < edges.size do
      val edge = edges(i)
      val target = edgeTarget(edge)
      val mapped = f(target)
      if mapped != target then
        edges(i) = retarget(edge, mapped)
        changed = true
      i += 1
    changed

  /** Shrink the NFA in place before encoding; returns the renumbered
    * (start, accept) pair. Three semantics-preserving reductions run to a
    * fixed point, then unreachable states are pruned:
    *
    *  1. Edges into states that cannot reach `accept` are dropped. No path
    *     through them completes for any input, so neither recognition nor
    *     the committed parse changes (the forward walk would refuse them
    *     via the viability oracle anyway, at run-time cost).
    *  2. States whose entire content is a single operation-free ε-edge are
    *     contracted: in-edges are redirected to the ε-target. No choice
    *     point and no operation is involved, so priorities are unaffected.
    *  3. States with identical ordered edge lists are merged: they have
    *     identical futures, including alternation priorities. The accept
    *     state is never merged away (acceptance is not visible in edges).
    *
    * The construction above is deliberately generous with ε-plumbing, and
    * cross-SCC references are inlined per reference, so this typically
    * removes a quarter of the states. Size matters twice: the encoded NFA
    * section shrinks linearly and the viability matrix — one bit per
    * (reverse state, NFA state) pair — shrinks with the state count.
    */
  private def reduceStates(start: Int, accept: Int): (Int, Int) =
    var entry = start
    def dropDeadEdges(): Bool =
      val live = new Array[Bool](states.size)
      val preds = Array.fill(states.size)(Buffer.empty[Int])
      states.iterator.zipWithIndex.foreach: (edges, source) =>
        edges.foreach(edge => preds(edgeTarget(edge)) += source)
      val worklist = Buffer(accept)
      live(accept) = true
      while worklist.nonEmpty do
        val state = worklist.remove(worklist.size - 1)
        preds(state).foreach: source =>
          if !live(source) then
            live(source) = true
            worklist += source
      var changed = false
      states.foreach: edges =>
        val kept = edges.filter(edge => live(edgeTarget(edge)))
        if kept.size != edges.size then
          changed = true
          edges.clear()
          edges ++= kept
      changed
    def contractTrivial(): Bool =
      val next = Array.fill(states.size)(-1)
      states.iterator.zipWithIndex.foreach: (edges, source) =>
        if source != accept && edges.size == 1 then edges(0) match
          case Edge.Eps(target, Nil) if target != source => next(source) = target
          case _ => ()
      // Follow chains of trivial states; the path set guards against cycles
      // (an all-trivial ε-cycle is dead and gets dismantled by the other
      // reductions, but resolution must not hang on it meanwhile).
      def resolve(state: Int): Int =
        val path = MutSet.empty[Int]
        var cur = state
        while next(cur) != -1 && path.add(cur) do cur = next(cur)
        cur
      var changed = false
      states.foreach: edges =>
        changed |= retargetAll(edges)(resolve)
      val resolvedEntry = resolve(entry)
      if resolvedEntry != entry then
        entry = resolvedEntry
        changed = true
      changed
    def mergeIdentical(): Bool =
      val representative = MutMap.empty[(Bool, Ls[Edge]), Int]
      val rep = Array.tabulate(states.size)(identity)
      states.iterator.zipWithIndex.foreach: (edges, state) =>
        val key = (state == accept, edges.toList)
        representative.get(key) match
          case S(canonical) => rep(state) = canonical
          case N => representative(key) = state
      var changed = false
      states.foreach: edges =>
        changed |= retargetAll(edges)(rep(_))
      if rep(entry) != entry then
        entry = rep(entry)
        changed = true
      changed
    var changed = true
    while changed do
      changed = false
      changed |= dropDeadEdges()
      changed |= contractTrivial()
      changed |= mergeIdentical()
    // Prune states unreachable from the entry and renumber the survivors.
    // The accept state is kept even if unreachable (a never-matching region):
    // the encoding refers to it. It seeds the worklist rather than being
    // force-kept afterwards, so the kept set is closed under edges by
    // construction — were the accept state ever given outgoing edges, a
    // force-kept accept would silently retarget them through the
    // zero-initialized `renumber` slots of their dropped targets.
    val keep = new Array[Bool](states.size)
    keep(entry) = true
    keep(accept) = true
    val worklist = Buffer(entry, accept)
    while worklist.nonEmpty do
      val state = worklist.remove(worklist.size - 1)
      states(state).foreach: edge =>
        val target = edgeTarget(edge)
        if !keep(target) then
          keep(target) = true
          worklist += target
    val renumber = new Array[Int](states.size)
    var nextId = 0
    states.indices.foreach: state =>
      if keep(state) then
        renumber(state) = nextId
        nextId += 1
    val compacted = Buffer.empty[Buffer[Edge]]
    states.iterator.zipWithIndex.foreach: (edges, state) =>
      if keep(state) then
        retargetAll(edges)(renumber(_))
        compacted += edges
    states.clear()
    states ++= compacted
    (renumber(entry), renumber(accept))

  // ------------------------------------------------------------------------
  // Reverse determinization (the viability oracle)
  // ------------------------------------------------------------------------

  /** Split the alphabet into equivalence classes: within a class, all
    * character edges behave identically. Returns the ordered upper boundaries;
    * `classOf(u)` is the number of boundaries that are ≤ u.
    *
    * A boundary at 0 is dropped: class 0 would then be `[0, 0)`, i.e. empty,
    * so it would cost a column in every reverse-transition row and a bit per
    * state in the viability matrix while `classOf` could never return it. */
  private def computeBounds(): Ls[Int] =
    val points = MutSet.empty[Int]
    states.foreach: edges =>
      edges.foreach:
        case Edge.Chr(ranges, _) =>
          ranges.foreach: (lo, hi) =>
            if lo > 0 then points += lo
            if hi < MaxUnit then points += hi + 1
        case _ => ()
    points.toList.sorted

  private def classCount(bounds: Ls[Int]): Int = bounds.size + 1

  /** A representative code unit for each class. */
  private def classRepresentative(bounds: Ls[Int], classId: Int): Int =
    if classId == 0 then 0 else bounds(classId - 1)

  private def rangesContain(ranges: Ls[CharRange], unit: Int): Bool =
    ranges.exists((lo, hi) => lo <= unit && unit <= hi)

  /** Subset-construct the determinized *reverse* automaton. State `R_i` of a
    * run over positions n..0 is the set of NFA states that can reach the
    * accept state by consuming `input[i..n)`. The forward walk then only
    * follows transitions into states proved viable by this oracle.
    *
    * @return (transition table by [revState * nClasses + class], the subset
    *         of NFA states denoted by each reverse state in id order, seed
    *         state id)
    */
  private def reverseDeterminize(accept: Int, bounds: Ls[Int]): (Buffer[Int], Ls[Set[Int]], Int) =
    val stateCount = states.size
    val classes = classCount(bounds)
    // Reverse ε-adjacency: epsPre(t) lists the sources of ε-edges into t.
    val epsPre = Array.fill(stateCount)(Buffer.empty[Int])
    // Reverse char-adjacency per class: chrPre(c)(t) lists sources of
    // class-c character edges into t.
    val chrPre = Array.fill(classes)(MutMap.empty[Int, Buffer[Int]])
    states.iterator.zipWithIndex.foreach: (edges, source) =>
      edges.foreach:
        case Edge.Eps(target, _) => epsPre(target) += source
        case Edge.Chr(ranges, target) =>
          var classId = 0
          while classId < classes do
            if rangesContain(ranges, classRepresentative(bounds, classId)) then
              chrPre(classId).getOrElseUpdate(target, Buffer.empty) += source
            classId += 1
    def close(seed: Set[Int]): Set[Int] =
      val worklist = Buffer.from(seed)
      val result = MutSet.from(seed)
      while worklist.nonEmpty do
        val state = worklist.remove(worklist.size - 1)
        epsPre(state).foreach: source =>
          if result.add(source) then worklist += source
      result.toSet
    val ids = LinkedHashMap.empty[Set[Int], Int]
    val worklist = Buffer.empty[Set[Int]]
    def idOf(set: Set[Int]): Int = ids.getOrElseUpdate(set, {
      worklist += set
      ids.size
    })
    val seed = close(Set(accept))
    val seedId = idOf(seed)
    val transitions = Buffer.empty[Int]
    while worklist.nonEmpty do
      val set = worklist.remove(0)
      val id = ids(set)
      // Rows may be discovered out of order; grow the table as needed.
      while transitions.size < (id + 1) * classes do transitions += 0
      var classId = 0
      while classId < classes do
        val pre = chrPre(classId)
        val next = close(set.iterator.flatMap(t => pre.get(t).iterator.flatMap(_.iterator)).toSet)
        transitions(id * classes + classId) = idOf(next)
        classId += 1
    (transitions, ids.keysIterator.toList, seedId)

  // ------------------------------------------------------------------------
  // Encoding
  // ------------------------------------------------------------------------

  private def encodeOps(ops: Ls[Op], pool: Buffer[Ls[Int]]): Int =
    val encoded = ops.flatMap:
      case Op.Mark => 0 :: Nil
      case Op.Slice => 1 :: Nil
      case Op.Add => 2 :: Nil
      case Op.Drop => 3 :: Nil
      case Op.Bind(slot) => 4 :: slot :: Nil
      case Op.Call(actionId, argSlots) => 5 :: actionId :: argSlots.size :: argSlots
      case Op.Enter => 6 :: Nil
      case Op.Exit => 7 :: Nil
      case Op.Rem => 8 :: Nil
      case Op.Defer(deferred, captured) =>
        9 :: encodeOps(deferred, pool) :: captured.size :: captured
    pool.indexOf(encoded) match
      case -1 =>
        pool += encoded
        pool.size - 1
      case index => index

  /** The alphabet for bit-packed sections: six bits per character, highest
    * bit first, using the standard Base64 characters — they need no escaping
    * in string literals and clash with neither the `;` section separator nor
    * the `,` integer separator. */
  private val packAlphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

  private def packBits(bits: Iterator[Bool]): Str =
    val packed = new StringBuilder
    var value = 0
    var count = 0
    bits.foreach: bit =>
      value = value * 2 + (if bit then 1 else 0)
      count += 1
      if count == 6 then
        packed += packAlphabet.charAt(value)
        value = 0
        count = 0
    if count > 0 then
      while count < 6 do
        value = value * 2
        count += 1
      packed += packAlphabet.charAt(value)
    packed.result()

  /** Encode the program as semicolon-separated sections of comma-separated
    * integers (except the last section). The full parsing table:
    *
    *  0. header: stateCount, start, accept, slotCount, classCount,
    *     revStateCount, seedRevState
    *  1. class boundaries (classCount - 1 integers)
    *  2. NFA: per state: edgeCount, then per edge either
    *     0, target, rangeCount, lo, hi, ... (character edge) or
    *     1, target, opsId (ε-edge, -1 when it carries no operations)
    *  3. operation pool: entryCount, then per entry: length, integers
    *  4. reverse transitions (revStateCount * classCount integers)
    *  5. viability: one bit per (revState, state) pair, row-major,
    *     bit-packed six per character (see `packAlphabet`)
    *
    * Recognition alone runs only the reverse scan, so `matchWhole` call
    * sites embed a much smaller table instead:
    *
    *  0. header: classCount, seedRevState
    *  1. class boundaries
    *  2. reverse transitions
    *  3. one '0'/'1' character per reverse state: whether its subset
    *     contains the start state (the whole-match acceptance test)
    *
    * String literals are interned by the JavaScript engine, so the runtime
    * caches the decoded program keyed by this very string: the table is built
    * once per program, not once per call.
    *
    * @return (the full parsing table, the recognition-only table)
    */
  private def encode(start: Int, accept: Int): (Str, Str) =
    val bounds = computeBounds()
    val (revTransitions, revSets, seedId) = reverseDeterminize(accept, bounds)
    val classes = classCount(bounds)
    val opsPool = Buffer.empty[Ls[Int]]
    val nfa = Buffer.empty[Int]
    states.foreach: edges =>
      nfa += edges.size
      edges.foreach:
        case Edge.Chr(ranges, target) =>
          nfa += 0
          nfa += target
          nfa += ranges.size
          ranges.foreach: (lo, hi) =>
            nfa += lo
            nfa += hi
        case Edge.Eps(target, ops) =>
          nfa += 1
          nfa += target
          nfa += (if ops.isEmpty then -1 else encodeOps(ops, opsPool))
    val opsSection = Buffer.empty[Int]
    opsSection += opsPool.size
    opsPool.foreach: entry =>
      opsSection += entry.size
      opsSection ++= entry
    val stateCount = states.size
    val viability = packBits:
      revSets.iterator.flatMap: set =>
        (0 until stateCount).iterator.map(set.contains)
    val header = stateCount :: start :: accept :: slots.size :: classes ::
      revSets.size :: seedId :: Nil
    val table = Iterator(
      header.mkString(","),
      bounds.mkString(","),
      nfa.mkString(","),
      opsSection.mkString(","),
      revTransitions.mkString(","),
      viability,
    ).mkString(";")
    val starts = revSets.iterator.map(set => if set contains start then '1' else '0').mkString
    val matchTable = Iterator(
      s"$classes,$seedId",
      bounds.mkString(","),
      revTransitions.mkString(","),
      starts,
    ).mkString(";")
    (table, matchTable)

  // ------------------------------------------------------------------------
  // Entry point
  // ------------------------------------------------------------------------

  /** Compile a string region rooted at `root`. Returns `N` when the region
    * cannot be compiled (an error has been reported and the caller should
    * compile nothing). */
  def compile(root: Pat, mode: Mode): Opt[Compiled] = scoped("ucs:string-compiler"):
    collectBodies(root)
    computeSccs()
    checkTailPositions()
    if failed then N else
      val rootIsPure = isPureDeep(root)
      // Pre-allocate slots for the root-visible bindings so the caller can
      // rely on their presence even if some binding branches are dead.
      val visible = root.symbols.map(symbol => symbol -> slotOf(symbol))
      val accept = newState()
      val entry = mode match
        case Mode.Whole =>
          build(root, accept, needValue = !rootIsPure, Nil, N)
        case Mode.Prefix =>
          // A prefix match is a whole match of `root ~ lazy-Σ*`: the trailing
          // star prefers not to consume, so the split point is exactly the
          // committed greedy parse of `root` alone. The boundary is recorded
          // as the start of the remaining string.
          val star = newState()
          addEps(star, accept, Nil)
          addChr(star, AnyChar, star)
          val boundary = newState()
          addEps(boundary, star, Op.Rem :: Nil)
          build(root, boundary, needValue = true, Nil, N)
      if failed then N else
        val builtCount = states.size
        val (reducedEntry, reducedAccept) = reduceStates(entry, accept)
        log(s"String region: ${states.size} states (built $builtCount), " +
          s"${slots.size} slots, ${actions.size} actions")
        val (table, matchTable) = encode(reducedEntry, reducedAccept)
        log(s"Encoded table (${table.length} characters): $table")
        log(s"Encoded match table (${matchTable.length} characters): $matchTable")
        S(Compiled(table, matchTable, actions.toList, visible,
          pure = !anyOps && slots.isEmpty && actions.isEmpty))
