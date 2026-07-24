# PR #540 "Optimized compilation of string patterns" — review findings

Reviewed branch `compiled-string-patterns` against its base `hkust-taco/hkmc2`
(merge base `c9bb0edd`). Upstream PR: <https://github.com/hkust-taco/mlscript/pull/540>.

## Method

Nine reviewers each took one dimension of the change (NFA construction, NFA
reduction, reverse determinization and encoding, the `Runtime.StrPat` engine,
`SplitCompiler` gating, the multi-matcher and `specialize`, `Instantiator` and
`Pattern`, tests and goldens, performance and AGENTS.md conformance). Every
finding they raised was then handed to three independent verifiers instructed
to *refute* it, each with a different lens: does the code actually do this, is
the path reachable from surface syntax, and is the defect introduced by this PR
or pre-existing. A finding is listed below only if at most one of the three
could refute it. 61 findings were raised, 50 survived; the 11 that did not are
listed at the end so they are not re-litigated.

## Test status

The whole suite is green on this branch — 814 tests including the WASM ones
(these need `npm install` first, to pick up the custom Binaryen build), with no
golden rewrites. That is precisely the situation AGENTS.md warns about: passing
tests are not the bar, and every regression below is invisible to the suite.

## Confirmed regressions against `hkust-taco/hkmc2`

Each of these was run on this branch and again on a worktree of the base ref.

| Program | base | this PR |
|---|---|---|
| `pattern Y = ("a" ~ X) \| (("b"~"c") => "T")`, `pattern X = ("d" ~ Y) \| "e"`; `"zae" is ("z" ~ Y) as r` | `"zae"` | `"()z"` |
| `pattern Funny = "" ~ "" ~ ""`; `42 is Funny` | `TypeError` | `true` |
| `pattern Half = ("a" ..< "z") ~ "!"`; `"z!" is Half` | `false` | `true` |
| `pattern Listed = (((Digit as h) ~ (Listed as t)) => h+","+t) \| ("" => "$")`; `"123" is Listed` | `"1,2,3,$"` | `"3,2,3,$"` |
| `@compile (("a" => print("ran")) ~ "b")` in condition position | clean "unsupported" error | transform silently never runs |
| `pattern P2 = Box(T ~ "c") \| Box(T ~ "d")` under `@compile` | clean "unsupported" error | `AssertionError: already defined: w` |
| `Bracket(Str) as v`, for `pattern Bracket(pattern P, inner) = "[" ~ (P as inner) ~ "]"` | `"no"` | `"[ab]"` (should be `"ab"`) |

All seven are pinned as `:expect` + `:fixme` blocks in
`hkmc2/shared/src/test/mlscript/ups/regex/CompiledBugs.mls`.

## Pre-existing issues surfaced along the way

Not caused by this PR, but relevant to the areas it touches:

- `rightInclusive` is ignored for `IntLit` ranges in `Instantiator` too, exactly
  as for string ranges.
- The same unguarded `correspondence(symbol)` lookup pre-exists at
  `Compiler.scala:616` and crashes the same way for a non-string `@compile`d
  pattern.
- Dropping `Extract` in `ResultMode.MatchOnly` is base behaviour for every
  pattern shape, not just string ones — so the inline-vs-`@compile` divergence
  for effectful transforms in condition position predates the PR.
- Extraction arguments on parametric string patterns (`Bracket(Str, x)`) never
  worked, on either branch.
- `unapplyStringPrefix` discards bindings entirely (its own `TODO: Use
  pd.extractionParams`).
- `Negation` in prefix position is `RejectPrefixSplit`: it silently never
  matches, with no diagnostic.
- `Pattern.symbols` on `Or` takes only the first non-`Never` alternative's
  symbols.
- `makeStringPrefixMatchSplit`'s conjunction case carries a `TODO: Implement the
  correct backtracking behavior`.
- Generated JS uses `.at(i)` rather than `[i]` throughout, and re-creates lifted
  closures per call — a backend lowering artifact visible in untouched files.
- The `[a b c]` golden in `UpsBugsBacklog.mls` reflects a known array-printing
  bug tracked in `backlog/ToTriage.mls`.

---


# CRITICAL (8)

## C1. `pureMemo` caches the optimistic in-cycle answer, so an impure recursive component can be compiled as pure — silently wrong output

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:281` — *miscompilation*, refuted 0/3

**What's wrong.**

`isPureDeep`'s `loop` treats a `Synonym` whose instantiation is already in `visiting` as pure (line 280) so the traversal terminates. That optimistic `true` is fine *for the query that introduced the assumption*, but line 281 memoizes the result of every nested instantiation into the region-wide `pureMemo`, including instantiations whose `true` answer was derived from an ancestor's optimistic assumption.

Concretely, `Or(ps) => ps.forall(...)` (line 276) short-circuits on the first `false`. If a body `Y` has an alternative that reaches `X` *before* the alternative that carries the `Extract`, then while computing `pureMemo(Y)` we descend into `X` with `visiting = {Y}`; `X`'s only reference back into the SCC is `Synonym(Y)`, which returns `true` optimistically, so `pureMemo(X) := true` is written. Only afterwards does `Y`'s second alternative return `false`, giving `pureMemo(Y) = false`. Now two members of the *same* SCC disagree about purity, and `X` is recorded as pure even though the cycle it sits on contains a transform.

Both consumers of that answer then break the completion protocol documented above `build`:

* the pure-subtree shortcut (line 355) fires for a pattern containing a same-SCC tail reference, emitting `Op.Mark` on the way in and an `Op.Slice` on an `exit` state that the goto can never reach (the automaton never returns from a tail call). `reduceStates` prunes that unreachable `exit`, so the `Mark` is pushed with no matching `Slice`, the fragment pushes **zero** values instead of the promised one, and the pending `exitOps` (typically `Op.Add`) are turned into a `Op.Defer(Op.Drop :: Nil, …)` at line 485 that *discards* the component's value at `Op.Exit` time. The stack then underflows in the enclosing deferred `Op.Add` (`valStack.pop()` on an empty array yields `undefined`).
* `buildReference` (line 499) picks `buildSccCopy(..., pure = true)` for `X` while another reference picks `pure = false` for `Y`, i.e. two copies of one SCC with incompatible value disciplines.

No diagnostic is emitted: the `softAssert` at line 480 only guards `sccContext.pure && needValue`, which is exactly the combination that does *not* occur in this path (`sccContext.pure` is `false` there, and `needValue` was reset to `false` by the shortcut).

Note also that `isPureDeep` therefore returns order-dependent answers within one region, which is a correctness hazard independent of this particular manifestation.

**Scenario.**

```
:js
pattern Y = ("a" ~ X) | (("b" ~ "c") => "T")
pattern X = ("d" ~ Y) | "e"

if "zae" is ("z" ~ Y) as r then r
```
Produces `"()z"` (JS `undefined + "z"`) instead of `"zae"`, with no error or warning. Verified by running the diff-test runner on this input.

The *same grammar* with the alternatives of `Y` written in the other order compiles correctly, which pins the cause on the memo/`forall` evaluation order rather than on the grammar:
```
pattern Y2 = (("b" ~ "c") => "T") | ("a" ~ X2)
pattern X2 = ("d" ~ Y2) | "e"

if "zae" is ("z" ~ Y2) as r then r   // = "zae"  (correct)
```

**Suggested fix.**

Purity is a property of the SCC condensation, not of an individual traversal. Compute it once, bottom-up: after `computeSccs()`, mark an SCC impure iff any member body contains a `Rename`/`Extract` outside a nested pure sub-tree or references an impure SCC, then propagate along the condensation DAG to a fixed point. `isPureDeep(Synonym(inst))` then just reads `sccPure(sccOf(inst))`, which is by construction consistent for all members of an SCC and independent of visit order. If the recursive formulation is kept, do not write to `pureMemo` when the computation consulted the `visiting` short-circuit (thread a "used an assumption" flag out of `loop` and only memoize when it is false). Additionally, add a hard guard for the invariant that was silently violated: the pure-subtree shortcut must not be entered for a pattern that can reach a same-SCC `Synonym` (see the companion finding).

## C2. Pattern transforms are invoked from uninstrumented runtime code, so an algebraic effect raised in a `=>` transform silently corrupts the parse

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:350` — *miscompilation*, refuted 0/3

**What's wrong.**

`Runtime.mls` is compiled by `CompileTestRunnerBase` with `Config.default`, i.e. `effectHandlers = N` (hkmc2/shared/src/main/scala/hkmc2/Config.scala:76), so nothing in `StrPat.parseRun` is handler-lowered — there is no `runtime.curEffect` check anywhere in the generated `parseRun` (verified in Runtime.mjs:836-1002).

But `parseRun` is now the place where user transforms run: `execValueOp` case 5 does `actions.[actionId].apply(null, args)` (line 350), and the `actions` are `Term.Lam(params, term.mkClone)` built from the user's `=>` bodies (`SplitCompiler.makeStringRegionSplit` / `Compiler.multiMatcherStringBranch` via `TermSynthesizer.actionsTuple`). Those lambdas ARE handler-lowered, because they live in the user's module. Under `:effectHandlers`, a lambda that performs an effect sets `runtime.curEffect` and returns a placeholder instead of a value.

`parseRun` has no way to notice. It pushes the placeholder onto `valStack`, keeps walking, and executes every remaining transform on the committed path with that placeholder as an argument, mutates `bindings`, and finally returns a structurally corrupt result array. Only afterwards does the caller (the call site of `parseWhole`, which is correctly *not* `@mayNotRaiseEffects`) observe `curEffect != null` and unwind — at which point the transforms that ran after the effect have already had their side effects, and on resume the whole match is not re-run; `resumeValue` replaces the entire result.

This is a regression: the pre-PR translation built the transform lambda and applied it *inline in the generated user block* (`SplitCompiler.scala:800-830`, `Compiler.scala:602-625`), so the application went through handler lowering and effects worked.

Note that the annotation split is right in intent (`matchWhole` is `@mayNotRaiseEffects` and never touches user code; the parse entry points are not annotated) but the annotation on the entry points buys nothing, because the suspension has to happen *inside* `parseRun`, which cannot suspend.

**Scenario.**

Reproduced directly against the shipped engine, using the real `CommaSep(Email)` table from the golden output of hkmc2/shared/src/test/mlscript/ups/regex/EmailAddress.mls (action 1 = `head => Cons(head, Nil)` made "effectful"):

```js
const efActions = [
  (h,t) => ({cons:[h,t]}),                                   // head::tail
  (h)   => { R.curEffect = {handler:'Ask'}; return R.Unit; }, // effectful head::Nil
  ()    => ({nil:true}),
];
R.StrPat.parseWhole(emailTable, efActions, 'a@b.co,c@d.eu')
```
Observed: the effectful transform runs, sets `curEffect`, and then the engine *still* runs the outer `head::tail` transform with `()` in place of the suspended value:
  log      = [["single-EFFECTFUL","c@d.eu"],["cons","a@b.co","()"]]
  curEffect set? true
  result   = [{"cons":["a@b.co",{}]},"a@b.co",{},"c@d.eu"]

The MLscript-level shape that triggers this is any compiled string region with an effectful transform, e.g. under `:effectHandlers`:
  `if s is ((("a"..="z") as c) => h.ask(c)) ~ "!" then ...`
where `h` is a handler instance. (`ups/regex/CompiledSemantics.mls` already exercises exactly this shape with a pure `print`, so the path is live.)

**Suggested fix.**

Either (a) hoist transform application out of the engine — have `parseRun` return the recorded call plan (action ids + argument tuples, in commit order) and apply the closures in the generated user block, where handler lowering applies; or (b) as a stopgap that turns a silent miscompilation into a diagnosable one, check `runtime.curEffect !== null` immediately after `actions.[actionId].apply(...)` in `execValueOp` and call `runtime.illegalEffect("in a string pattern transform")`. Add a `:effectHandlers` regression test with an effectful `=>` transform under `~`, with `:fixme` if (a) is deferred.

## C3. `isParametricStringSite` ignores `defn.extractionParams`, so use sites of parametric string patterns return the whole matched string instead of the extraction binding

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1218` — *miscompilation*, refuted 0/3

**What's wrong.**

`isParametricStringSite` only tests `defn.patternParams.nonEmpty && arguments.length == defn.patternParams.length`. It never looks at `defn.extractionParams`. But `matchParametersWithArguments` (line 509) deliberately treats `argumentCount === patternParameterCount` as "all extraction parameters omitted", and `compilePattern(pd)` (line 1465) then makes `unapply` return the *extraction bindings* as the output (`case sole :: Nil => makeMatchSuccess(getBinding(sole))`, `case ps => tuple of bindings`). `MixedParameters.mls` pins this semantics explicitly ("We can omit all extraction parameters completely. All extraction parameters will be placed in a tuple and returned" / "The value of y is the same in the example above and in the one below").

When `isParametricStringSite` fires, `makeMatchSplit` (line 660) bypasses `makeMatchPatternSplit`/`unapply` entirely and calls `makeStringRegionSplit`, whose output is the automaton's value = the concatenation of the consumed segments (i.e. the whole scrutinee for a transform-free region). The extraction parameter's value is never surfaced as the output: `visibleSlots` is `root.symbols`, and `root` is a `Synonym`, whose `symbols` is `Nil` (ups/Pattern.scala:78), so even the binding does not come back.

So `P(Arg)` and `P(Arg, x)` — documented to be equivalent — now disagree, and the automaton path silently wins.

**Scenario.**

```
pattern Bracket(pattern P, inner) = "[" ~ (P as inner) ~ "]"

// goes through makeMatchPatternSplit -> Bracket.unapply -> extraction binding
if "[ab]" is Bracket(Str, x) then x
//| = "ab"     (correct)

// 1 argument == 1 patternParam  =>  isParametricStringSite fires
if "[ab]" is Bracket(Str) as v then v
//| = "[ab]"   (WRONG; should be "ab")
```
With two extraction params (`pattern Bracket2(pattern P, a, b) = (P as a) ~ "-" ~ (P as b)`), `Bracket2(Str) as v` should yield the tuple `[a, b]` and instead yields the whole input string.

**Suggested fix.**

Require `defn.extractionParams.isEmpty` in `isParametricStringSite` (and correspondingly document that parametric string patterns with extraction parameters keep the `unapply` route). Alternatively, teach `makeStringRegionSplit` to project the extraction parameters out of `compiled.visibleSlots` — but that also requires `Instantiator`/`StringCompiler` to keep definition-internal `Rename`s visible through `Synonym`, which they currently do not.

## C4. `makeStringRegionSplit` emits `StrPat.matchWhole`/`parseWhole` with no `Str` class test, so non-string scrutinees match string patterns

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1250` — *miscompilation*, refuted 0/3

**What's wrong.**

Every other string-matching path in the compiler guards the scrutinee with a `Str` head test: `makeStringPrefixMatchSplit`'s `Wildcard` case emits `Branch(scrutinee, FlatPattern.ClassLike(ctx.builtins.Str, ...))` (line 1007), its `Str`/`Literal` cases go through `Str.startsWith`/`Str.length` (which throw on non-strings), and `Compiler.buildMultiMatcherBody`'s new `stringBranch` wraps the whole automaton call in `Branch(scrutinee, FlatPattern.ClassLike(strSymbol, ...))`.

`makeStringRegionSplit` does neither: it emits `runtime.StrPat.matchWhole(table, scrutinee)` (line 1250) or `runtime.StrPat.parseWhole(table, actions, scrutinee)` (line 1255) directly, then branches on the result. `Runtime.StrPat.matchWhole` starts with `let i = input.length - 1; while i >= 0 do ...`, so for a value whose `.length` is `undefined` (a number, an object) the loop never runs and the function returns `matcher.starts.charCodeAt(seedRev) === 49` — i.e. *whether the empty string matches* — and for `[]` (`length === 0`) exactly the same. `parseRun` is worse: `n = undefined` makes every character edge (`pos < n`) and every ε-edge (`viable(prog, revArr.[NaN], t)` -> `undefined`) unviable, so the search stack empties and it throws `Error("StrPat: no viable transition (this is a compiler bug)")`.

Note the branch is reachable both at inline use sites (`makeMatchSplit`'s `Concatenation` case, line 740) and inside every generated `unapply` for a non-parametric string pattern definition (line 1462 -> `makeStringRegionSplit`).

**Scenario.**

Using the pattern already in `ups/regex/EmptyString.mls`:
```
pattern Funny = "" ~ "" ~ ""

42 is Funny            //| = true    (WRONG; should be false)
[] is Funny            //| = true    (WRONG)
42 is @compile Funny   //| = false   (correct — multi-matcher has the Str head)
```
(The encoded match table in the golden is `"1,0;;1,1;10"`: `starts[seedRev=0] == '1'`, so any scrutinee with a falsy/zero `length` is reported as a match.)

And for the parsing entry point:
```
fun trimStart(str) = if str is (" " | "\t") ~ rest then trimStart(rest) else str
trimStart(42)
//| RUNTIME ERROR: Error: StrPat: no viable transition (this is a compiler bug)
```
which blames the compiler for a user type error (pre-PR this was a plain `TypeError: string.startsWith is not a function`).

**Suggested fix.**

Wrap both emitted call sites in `Branch(scrutinee(), FlatPattern.ClassLike(ctx.builtins.Str.safeRef, ctx.builtins.Str, N, false)(Tree.Dummy), ...) ~: alternative`, exactly as `Compiler.buildMultiMatcherBody` already does for the absorbed `Str` head. (Defensively, `StrPat.matchWhole`/`parseRun` should also reject non-strings rather than silently reading `.length`.)

## C5. Per-label `StringCompiler` in `multiMatcherStringBranch` duplicates transform closures that share parameter symbols, crashing `SymbolRefresherWalker`

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Compiler.scala:285` — *compiler-crash*, refuted 0/3

**What's wrong.**

`multiMatcherStringBranch` creates a fresh `StringCompiler()` for every label of the multi-matcher (line 285, with an explicit comment justifying it: "each label needs its own compiler"). Transform closures are interned *per compiler instance* — `StringCompiler.build`'s `Extract` case does `actionSources.indexWhere(_ eq term)` over that instance's own buffer, and builds `Term.Lam(PlainParamList(params), term.mkClone)` where `params` are `Param(..., correspondence(symbol), ...)`, i.e. the **shared** `VarSymbol`s stored in the `Extract` node.

All labels of one multi-matcher are instantiated by a *single* `Instantiator` (see `compilePatternImpl`), so two labels that reach the same `Instantiation` see the *same* `Extract` node object, with the same `correspondence` map. Because interning is per-label, each label emits its own `Term.Lam` binding the very same `VarSymbol` as a parameter. Both lambdas are then placed in the same `Blk` (the multi-matcher body assembled at line 331), so `SymbolRefresherWalker.refreshParamList` sees the symbol defined twice and fires `assert(... , "already defined: w")`.

The TODO in `StringCompiler.build`'s `Extract` case anticipates this but understates it: it claims the situation "only trips the refresher when a simplifier pass duplicates a subtree containing both". In `multiMatcherStringBranch` the duplication is unconditional and deterministic — two labels of one matcher body are always two regions in one block. Before this PR the situation was unreachable because `Instantiator` rejected `Concatenation` outright, so a multi-matcher never contained two string regions.

**Scenario.**

```mls
:js
open annotations

class Box(val v)

pattern T = (("a" ~ "b") as w) => [w]

pattern P2 = Box(T ~ "c") | Box(T ~ "d")

fun f2(x) = if x is @compile P2 as y then y else "no"
```

This aborts compilation of the whole definition with

```
/!!!\ Uncaught error: java.lang.AssertionError: assertion failed: already defined: w
	at: hkmc2.codegen.SymbolRefresherWalker.assertUpdate(SymbolRefresher.scala:15)
	at: hkmc2.codegen.SymbolRefresherWalker.refreshVarSymbol(SymbolRefresher.scala:24)
	at: hkmc2.codegen.SymbolRefresherWalker.refreshParamList(SymbolRefresher.scala:62)
```

and every later use of `f2` then fails with "No definition found in scope for member 'f2'" / `ReferenceError: f2 is not defined`.

Verified minimal pair (same file, all four cases run together):
- `pattern P1 = Box(T ~ "c")` + `@compile` (one label)  ->  works, `f1(Box("abc")) = Box("abc")`
- `pattern P2 = Box(T ~ "c") | Box(T ~ "d")` + `@compile` (two labels)  ->  **crash above**
- same `P2` without `@compile` (goes through `unapply`, one region per site)  ->  works
- two separate `~` regions in one `if` block without `@compile`  ->  works

So the trigger is specifically the two-labels-in-one-multi-matcher path.

**Suggested fix.**

Intern transform closures across all labels of one multi-matcher body rather than per `StringCompiler` instance: thread a shared interning table (`Buffer[Term]` keyed by `eq` on the source `Extract` term, plus the resulting `Term.Lam`) through the `StringCompiler` constructor from `multiMatcherStringBranch`, and let each label's `Compiled.actions` index into it, emitting the closures once at the top of the `Blk`. Alternatively adopt the principled fix already sketched in the `Extract` TODO (host each definition's transforms as methods on the pattern object and reference them by selection). Whichever is chosen, add a regression test with the shape above, and drop/downgrade the now-inaccurate claim in the TODO that this "only trips the refresher when a simplifier pass duplicates a subtree".

## C6. `rightInclusive` is silently dropped for string ranges: `"a" ..< "z"` matches `"z"` inside any compiled string region

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Instantiator.scala:133` — *miscompilation*, refuted 0/3

**What's wrong.**

`SP.Range(lower, upper, rightInclusive)` binds `rightInclusive` and then never uses it in either literal branch. The string branch builds `CharClass(lower.head.toInt, upper.head.toInt)`, and `Pattern.CharClass` is documented and implemented as an *inclusive* range (`StringCompiler.build`: `addChr(entry, (lo, hi) :: Nil, cont)`), so `..<` is compiled exactly like `..=`. The integer branch has the same defect (`(lower to upper)` is inclusive).

This is not a new line of code in the sense that the old expansion `(lower.head to upper.head)` was equally inclusive, but the PR makes it *reachable on the main path*: before, `SP.Concatenation` was an error in `Instantiator`, so string ranges only reached this code under the opt-in `@compile` annotation. Now every `pattern P = ... ~ ...` containing a range is instantiated here and compiled by `StringCompiler`. Meanwhile the legacy translation the PR replaces handles the flag correctly (`SplitCompiler.makeRangeTest`, line 253: `val upperOp = if rightInclusive then lteq else lt`, used from the prefix path at line 1039). So the *same* range pattern now means two different things depending on whether it sits next to a `~`, with no diagnostic.

The PR's comment ("mirroring the previous expansion") documents the bug as intended behaviour and bakes inclusivity into the new node's contract, which makes it harder to fix later.

**Scenario.**

Verified by running the diff-test suite on a scratch file:

```
:js

pattern Half = ("a" ..< "z") ~ "!"

"z!" is Half
//│ = true      // WRONG: `..<` must exclude "z"

pattern Plain = "a" ..< "z"

"z" is Plain
//│ = false     // correct, via the legacy `makeRangeTest` path
```

`"y!" is Half` is also `true`, so the class really is `a..z` inclusive rather than off in some other way. Existing goldens do not catch this because every string range in the test suite uses `..=`.

**Suggested fix.**

Thread `rightInclusive` through: emit `CharClass(lo, hi)` when inclusive and `CharClass(lo, hi - 1)` (reducing to `Never` when `hi - 1 < lo`) when exclusive, or give `CharClass` an explicit inclusivity field. Fix the `IntLit` branch the same way (`if rightInclusive then lower to upper else lower until upper`). Add regression tests with `..<` in both a compiled string region and an `@compile`d integer range.

## C7. Recursive string pattern with a transform silently returns wrong bindings when matched through `unapply` (the plain, unannotated form) — no test covers this shape

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:455` — *miscompilation*, refuted 0/3

**What's wrong.**

`parseRun` returns root-visible binding slots by reading the *global* slot store after the whole parse (`result.push(bindings.get(s))`, Runtime.mls:454-456), and the call sites destructure them positionally (`SplitCompiler.scala:1266`, `Compiler.scala:317`). That is only sound when each slot is written exactly once on the committed walk. For a *recursive* region, every activation writes the same slots, so the exported value is the value of the LAST activation, not the outermost one.

The reason this is not caught internally is that `Op.Defer`/`capturedSlots` handles exactly this hazard — but only for operations that live *inside* the automaton. Whether a definition's transform lives inside the region depends on which entry point is used:
  * `@compile P` -> `Compiler.multiMatcherStringBranch` compiles `StringCompiler.stringFragment(expandedPattern)`, i.e. the whole definition including its `Transform`, so the transform is deferred with slot capture => correct;
  * a *parametric* use site `P(A)` -> `isParametricStringSite` -> `makeStringRegionSplit` on the whole constructor, transform inside the region => correct;
  * a plain `x is P` for a *non-parametric* `P` -> `makeMatchPatternSplit` -> `P.unapply`, which is built by `makeMatchSplit(input, pd.pattern, true)`. `compilePattern` dispatches node-by-node, so only the innermost `Concatenation` becomes the automaton region; the enclosing `Transform` is applied OUTSIDE the automaton on the exported slots => the outermost activation's bindings are clobbered.

Every recursion+transform test in the PR uses one of the two *working* paths: `Separation.mls` (`Lines`/`TailLines` are parametric), `EmailAddress.mls` (`CommaSep(Email)` is parametric), `UpsBugsBacklog.mls` (`Input`, which happens to recurse only once because the greedy wildcard eats the whole string). Nothing exercises a non-parametric recursive string pattern with a transform, which is the most natural spelling and the one that is broken.

**Scenario.**

Verified by running `hkmc2DiffTests` on a scratch file:

```
:js
open annotations
pattern Digit = "0" ..= "9"
pattern R2 = (((Digit as h) ~ (R2 as t)) => h + "," + t) | ("" => "$")

if "1" is R2 as r then r else "NOPE"
//| = "1,$"            <- correct (depth 1 only)

if "12" is R2 as r then r else "NOPE"
//| = "2,2,$"          <- WRONG, should be "1,2,$"

if "123" is R2 as r then r else "NOPE"
//| = "3,2,3,$"        <- WRONG, should be "1,2,3,$"

fun viaCompile(s) = if s is @compile R2 as r then r else "NOPE"
viaCompile("123")
//| = "1,2,3,$"        <- correct

pattern P2(pattern D) = (((D as h) ~ (P2(D) as t)) => h + "," + t) | ("" => "$")
if "123" is P2(Digit) as r then r else "NOPE"
//| = "1,2,3,$"        <- correct
```

The same pattern therefore yields three different answers depending on how it is referenced, with no diagnostic. Decoding `"3,2,3,$"`: the outer transform reads `bindings.get(h)` = "3" (last digit) and `bindings.get(t)` = "2,3,$" (the value the outermost deferred frame wrote last).

**Suggested fix.**

Two parts.

(1) Fix: make `unapply` for a non-parametric definition compile the *whole* body as one region whenever `containsStringSeq(pd.pattern) && regionSupported(pd.pattern, Set.empty)` — exactly the condition already used for `unapplyStringPrefix` at `SplitCompiler.scala:1489-1493`. That puts the `Transform` inside the automaton, where `Op.Defer` capture already does the right thing. Failing that, `StringCompiler.compile` must refuse to export a visible slot that can be written more than once (i.e. a slot bound inside a recursive SCC), and `softAssert` it.

(2) Test: add to `hkmc2/shared/src/test/mlscript/ups/regex/CompiledSemantics.mls`:

```
// Bindings of the outermost activation of a recursive component must survive
// the inner activations, regardless of which entry point is used.

pattern Digit = "0" ..= "9"

pattern Listed = (((Digit as h) ~ (Listed as t)) => h + "," + t) | ("" => "$")

:expect "1,2,3,$"
if "123" is Listed as r then r else "NOPE"

:expect "1,2,3,$"
if "123" is @compile Listed as r then r else "NOPE"

pattern ListedP(pattern D) = (((D as h) ~ (ListedP(D) as t)) => h + "," + t) | ("" => "$")

:expect "1,2,3,$"
if "123" is ListedP(Digit) as r then r else "NOPE"
```

## C8. `@compile`d string patterns silently skip transforms in match-only mode, diverging from the identical inline path

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Compiler.scala:289` — *miscompilation*, refuted 0/3

**What's wrong.**

`multiMatcherStringBranch` and `SplitCompiler.makeStringRegionSplit` (SplitCompiler.scala:1240) are near-copies of one another: both compile the region, then choose between `StrPat.matchWhole` (recognition only, no value ops) and `StrPat.parseWhole` (committed forward walk that executes the ops), then destructure `[output, slots...]`. But the two copies use *different* predicates for that choice.

`makeStringRegionSplit` (SplitCompiler.scala:1247) takes the recognition-only path only when
    `compiled.pure || (!outputNeeded && compiled.visibleSlots.isEmpty && compiled.actions.isEmpty)`
and its own doc comment (SplitCompiler.scala:1232-1235) states the invariant explicitly: "Transforms, however, always force the parsing entry point — they run exactly once on the committed parse, even when the match is only used as a condition."

`multiMatcherStringBranch` (Compiler.scala:289) instead writes `if isMatchOnly then <matchWhole>` unconditionally, with no test on `compiled.actions`. `ResultMode.MatchOnly` is selected in `SplitCompiler.compilePatternImpl` (SplitCompiler.scala:1380-1385) whenever the pattern has no explicit extraction matches, no reachable definition with `extractionParams` (`carriesExtractionSlots`, SplitCompiler.scala:128), and the output is not needed — none of which is falsified by an inline transform. So a `@compile`d region containing a `=>` transform reaches `matchWhole`, the transform closures are never even passed to the runtime, and they never run.

This is precisely the class of bug the PR's own `ups/regex/CompiledSemantics.mls` was written to pin down ("Transforms run exactly once, and only on the committed parse" — and its `probe` test asserts the transform runs when the match is used only as a condition). The `@compile` route violates that pinned semantics. It is also the concrete payoff of the DRY violation: the choice predicate is the kind of logic AGENTS.md says must be centralized ("the logic for handling cases that ought to be similar should be centralized").

**Scenario.**

Verified empirically by adding this file and running `sbt "hkmc2DiffTests/testOnly hkmc2.DiffTestRunner -- -z ..."` (file removed afterwards):

    :js
    open annotations

    // Inline site: matches the existing golden in CompiledSemantics.mls
    fun probe(x) = if x is ("a" => print("ran")) ~ "b" then "yes" else "no"
    probe("ab")
    //| > ran
    //| = "yes"

    // Same pattern via @compile: transform is silently dropped
    fun probe2(x) = if x is @compile (("a" => print("ran2")) ~ "b") then "yes" else "no"
    probe2("ab")
    //| = "yes"        <-- no "ran2" is printed

    // Output demanded => Full mode => transform does run
    fun probe3(x) = if x is @compile (("a" => print("ran3")) ~ "b") as o then o else "no"
    probe3("ab")
    //| > ran3
    //| = "()b"

So an effectful transform runs, or does not run, depending purely on whether the caller happens to bind the pattern output — with no diagnostic. Adding `@compile` to a working program silently changes its observable behaviour.

**Suggested fix.**

Factor the shared decision + call-emission into one helper (e.g. on `StringCompiler.Compiled`: `def needsParsing(outputNeeded: Bool, bindingsNeeded: Bool): Bool = !pure && (outputNeeded || bindingsNeeded || actions.nonEmpty || visibleSlots.nonEmpty)`), and have both `makeStringRegionSplit` and `multiMatcherStringBranch` consult it. At minimum, change Compiler.scala:289 to `if isMatchOnly && compiled.actions.isEmpty then` and add a `softAssert` in `multiMatcherStringBranch` that the `matchWhole` path is only taken when `compiled.actions.isEmpty`. Add the `probe2` case above as a regression test in `ups/regex/CompiledSemantics.mls`.

# MAJOR (26)

## M1. The pure-subtree shortcut's `Mark`/`Slice` pairing invariant is unchecked, so any future violation is silent

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:355` — *missing-assertion*, refuted 0/3

**What's wrong.**

The shortcut at lines 355-364 emits `Op.Mark` on an entry ε-edge and `Op.Slice` on an ε-edge out of a freshly created `exit` state, and *assumes* every accepting path through `build(pattern, exit, false, Nil, scc)` reaches `exit`. That assumption is exactly the completion protocol documented above `build`, and it is false whenever the sub-tree can reach a same-SCC `Synonym`, because line 486 returns a goto state that jumps to a component entry and never comes back to `exit`.

When that happens the failure mode is entirely silent: `reduceStates` prunes the now-unreachable `exit` (it is *live* — it reaches `accept` — so `dropDeadEdges` keeps its edge; it is only removed by the reachability-from-entry pass), so the emitted automaton simply has an unmatched `Op.Mark` and a lost value. The runtime `markStack` is LIFO and is never checked for balance, so a stray mark can additionally be consumed by an unrelated later `Op.Slice`, yielding a slice with the wrong start offset.

AGENTS.md requires invariants that the code relies on to be asserted (`softAssert`/`assert`). The existing `softAssert`s in `build` (lines 368, 374, 381, 395) are all vacuous — they sit in arms that are only reachable when `!needValue && exitOps.isEmpty` already holds — while the one non-trivial structural invariant of the construction has no guard at all.

**Scenario.**

Any pattern for which `isPureDeep` returns `true` on a sub-tree containing a same-SCC tail reference. Today this is reachable via the `pureMemo` bug (see the companion finding): `pattern Y = ("a" ~ X) | (("b" ~ "c") => "T")`, `pattern X = ("d" ~ Y) | "e"`, then `if "zae" is ("z" ~ Y) as r then r` builds `Mark` → goto(X) with the matching `Slice` on a pruned state, and evaluates to `"()z"` with zero diagnostics.

**Suggested fix.**

In the shortcut, assert that the pure sub-tree cannot reach a same-SCC reference, e.g. `softAssert(scc.isEmpty || !containsSameSccReference(pattern, scc.get.sccId), "pure-subtree shortcut over a same-SCC tail call")` before taking it (and fall through to the general case if it does). Symmetrically, add a guard in the `Synonym` goto arm (line 471) asserting that no `Op.Mark` is pending — e.g. thread a `underMark: Bool` flag through `build` and `softAssert(!underMark)` there. It would also be cheap and worthwhile for `parseRun` to `throw` when `markStack` is non-empty at acceptance, which turns this whole class of compiler bug from silent-wrong-answer into a loud failure.

## M2. `correspondence(symbol)` is an unguarded map lookup: bindings inside a pattern *argument* crash the compiler with `NoSuchElementException`

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:463` — *crash*, refuted 0/3

**What's wrong.**

For `Extract(p, correspondence, term)` the action's parameter list is built as `p.symbols.map(symbol => Param(..., correspondence(symbol), ...))`. `correspondence` comes from the *definition*'s `SP.Transform` and therefore only maps the symbols bound syntactically inside the definition body. But `p.symbols` is computed on the **instantiated** pattern, so after `Instantiator` substitutes a pattern argument, `p.symbols` also contains every `VarSymbol` bound by the argument (`Pattern.symbols`: `Rename(pattern, name) => name :: pattern.symbols`, and `Concat(ps) => ps.flatMap(_.symbols)`).

For a use site such as `Wrap(("x" as w))`, `p.symbols` is `[h, w]` while `correspondence` is `{h -> h'}`, and `correspondence(w)` throws an uncaught `java.util.NoSuchElementException` out of the compiler — not a reported `COMPILATION ERROR`. This is a genuine regression of this PR for string patterns: the analogous non-string program is accepted today (see the scenario).

**Scenario.**

```
:js
pattern Wrap(pattern L) = ((L as h) ~ "!") => [h]

if "y!x!" is (Wrap("y") ~ Wrap(("x" as w))) as r then r
```
crashes the compiler:
```
/!!!\ Uncaught error: java.util.NoSuchElementException: key not found: w
	at hkmc2.semantics.ups.StringCompiler.$anonfun$2(StringCompiler.scala:463)
	at hkmc2.semantics.ups.StringCompiler.build(StringCompiler.scala:462)
```
The same construct on a non-string parametric pattern is fine on this very branch:
```
pattern W2(pattern L) = (L as h) => [h]
if 1 is W2((Int as w)) then "ok"   // = "ok"
```
(Both verified with the diff-test runner.)

**Suggested fix.**

Do not derive the action's parameters from `p.symbols`. The transform's parameters are exactly `correspondence`'s codomain for the symbols the *definition* binds, so restrict the list: `val transformSymbols = p.symbols.filter(correspondence.contains)` and use that list for both `params` and `argSlots` (they must be derived from the same list — see the companion finding). If a symbol reaching an `Extract` without a correspondence entry is believed impossible, replace the lookup with `correspondence.getOrElse(symbol, lastWords(s"no transform parameter for $symbol"))` so the invariant is stated. Note `Compiler.scala:616` has the same unguarded lookup and should be fixed with it rather than duplicated (AGENTS.md: keep it DRY).

## M3. `Extract` actions are interned by term identity but `argSlots` are recomputed per occurrence, so one closure can be called with another instantiation's argument list

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:460` — *miscompilation*, refuted 0/3

**What's wrong.**

`actionSources.indexWhere(_ eq term)` interns the closure by the identity of the transform `Term`. `Instantiator.instantiate` re-walks the *same* `SP` tree for every `Instantiation` and reuses the original `transform` term object (`Extract(instantiate(pattern), parameters.toMap, transform)`), so two distinct instantiations `D(A1)` and `D(A2)` of one parametric definition share the term and therefore share one interned action.

But the closure's `params` are computed only for the **first** occurrence (line 462-463), while `argSlots = p.symbols.map(slotOf)` (line 468) is recomputed for **every** occurrence. `p.symbols` depends on the substituted argument, so the two occurrences can produce lists of different length and different order. The generated `Op.Call(actionId, argSlots)` then pushes the wrong number of arguments — or, when the lengths happen to agree, silently passes values positionally into the wrong parameters, because the parameter list came from a different instantiation.

This is not a hypothetical future hazard; it is live today, and it is ordering-dependent (which occurrence is built first is decided by `Concat`'s `go`, which builds the last element first), so it can flip between "loud" and "silent" with a trivial source rearrangement. `Runtime.checkArgs` catches the arity case only because arity checking happens to be enabled here.

**Scenario.**

```
:js
pattern Wrap2(pattern L) = (L ~ ("!" as h)) => h

if "x!y!" is (Wrap2(("x" as w)) ~ Wrap2("y")) as r then r   // expected "!!"
```
fails at run time with
```
Error: Function expected 1 argument but got 2
    at Runtime.checkArgs (Runtime.mjs:1394:41)
    at StrPat.parseRun (Runtime.mjs:919:25)
```
because `Wrap2("y")` is built first and fixes the closure at one parameter `h`, while `Wrap2(("x" as w))` emits `Op.Call(id, [slot_w, slot_h])`. Since `p.symbols` puts the argument's symbols *before* `h` here, with arity checking off the closure would instead receive `w`'s value (`"x"`) bound to `h` — a silent wrong result. (Verified with the diff-test runner.)

**Suggested fix.**

Key the interning on something that determines the whole calling convention, not just the term: intern on `(term, p.symbols)` (identity for the term, structural for the symbol list), and store the `params`/`argSlots` pair alongside the action so the two can never diverge. Better, compute one canonical `transformSymbols` list (the symbols the definition's `correspondence` actually maps, in `correspondence` order) and derive *both* `params` and `argSlots` from it, which also fixes the companion `correspondence(symbol)` crash and makes the action independent of which instantiation reached it first. Longer term, the TODO's own suggestion — hosting each definition's transforms as methods next to `unapply` — is the right fix and would remove the shared-parameter-symbol hazard across regions as well.

## M4. `mergeIdentical` is not semantics-preserving on ε-cycles: merging two states with identical edge lists silently drops (or duplicates) value operations on the committed parse

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:630` — *miscompilation*, refuted 0/3

**What's wrong.**

The doc comment at line 576-578 justifies reduction 3 with "States with identical ordered edge lists are merged: they have identical futures, including alternation priorities." That is true of the recognized *language* and of edge priority, but it is NOT true of the committed parse, because the runtime forward walk does not have a pure "future determined by edges" semantics.

In `Runtime.mls`/`parseRun`, the per-round ε-search cuts back-edges with a visit mark keyed by NFA *state id*:

    else if visited.get(target) !== gen && viable(prog, revArr.[n - pos], target) do
      visited.set(target, gen); parentState.set(target, source); parentOps.set(target, edge.[2]); pushEdges(stack, target)

So the number of times an ε-cycle is traversed before the search falls through to a lower-priority alternative depends on the *identity* of the states on the cycle, not only on their edge lists. Consequently, identifying two states that lie on a common ε-path which carries `Op`s between them changes the set of `Op`s on the committed path — exactly the thing that determines bindings, `Op.Call` transform invocations, and `Op.Defer` frames.

`mergeIdentical`'s key `(state == accept, edges.toList)` cannot see this: it distinguishes only acceptance, and merging is applied transitively across passes of the `while changed` loop, so a merge that is locally harmless can enable a second merge that collapses an off-cycle state with an on-cycle one.

I ported all three reductions plus the final pruning to a reference implementation and differentially tested them against a reference committed-parse semantics (priority DFS with a (state, pos) visited set — which is exactly what the runtime's viability-oracle-driven commit computes) over ~1M random automata, restricted to `build`'s structural shape (every op-carrying ε-edge is the sole edge of its state — see the `addEps` call sites with non-empty ops at lines 358, 362, 484-485, 516, 522, 916; all of them are freshly created single-edge states). Results: `dropDeadEdges` 0 mismatches / 200k, `contractTrivial` 0 mismatches / 200k, `mergeIdentical` produced mismatches. Every mismatch had an ε-cycle in the input automaton; adding an "do not merge states that lie on an ε-cycle" guard eliminated all of them (0 / 300k).

I was not able to exhibit an .mls source that produces the offending state pair today — `buildReference`'s `Op.Enter`/`Op.Exit` bracketing currently keeps an outer reference to a recursive component structurally distinct from the internal gotos, and the pure path carries no ops at all. But ε-cycles themselves *are* produced by `build` (a nullable recursive body, e.g. `pattern Xss = Xs ~ (Xss | "")` with a nullable `Xs`; also left recursion under `Or`, which `checkTailPositions` accepts because `case Or(ps) => ps.foreach(check(owner, _, tail))` propagates `tail`). So the soundness of reduction 3 rests entirely on incidental properties of `build` that are neither documented nor asserted, and the file's own TODO at line 453 ("host each definition's transforms as methods ... and reference them from regions by selection") is precisely the kind of change that would start producing shared op-states across reference sites and expose this. Per AGENTS.md this is the worst-case class: silent miscompilation, and an invariant that is relied upon but not asserted.

**Scenario.**

NFA-level counterexample honouring `build`'s structural invariants (accept = 0, entry = 1; `o` is any non-empty op list, e.g. `Op.Bind(0) :: Nil`):

  0 (accept): []
  1 (entry):  [Eps(3, Nil), Eps(0, Nil)]
  2:          [Eps(4, o)]
  3:          [Eps(4, o)]
  4:          [Eps(2, Nil), Eps(0, Nil)]

All states are live, so `dropDeadEdges` is a no-op; no state is a single op-free ε-edge, so `contractTrivial` is a no-op.

`mergeIdentical` pass 1: states 2 and 3 have the same key -> rep(3) = 2, so state 1 becomes [Eps(2,Nil), Eps(0,Nil)]. Pass 2: states 1 and 4 now have the same key -> rep(4) = 1, so state 2 becomes [Eps(1, o)]. After pruning: 0: [], 1 (entry): [Eps(2,Nil), Eps(0,Nil)], 2: [Eps(1, o)].

Run `parseRun` on the empty input (n = 0), tracing the actual runtime code:

* BEFORE reduction: cur = 1, visited{1}; pop Eps(3) -> visit 3 (parentOps = -1), push its edges; pop Eps(4, o) -> visit 4 (parentOps = opsId(o)), push its edges; pop Eps(2) -> visit 2, push its edge; pop Eps(4, o) -> `visited.get(4) === gen`, skipped; pop Eps(0) -> target === accept and pos === n -> `execChain(0)` walks 0 <- 4 <- 3 <- 1 and runs `o` EXACTLY ONCE.
* AFTER reduction: cur = 1, visited{1}; pop Eps(2) -> visit 2 (parentOps = -1), push its edge; pop Eps(1, o) -> `visited.get(1) === gen`, skipped; pop Eps(0) -> accept, `execChain(0)` walks 0 <- 1 and runs NOTHING.

So `o` is executed once before the reduction and zero times after it. If `o` is `Op.Bind(slot)` the caller destructures `undefined` for that binding; if it is `Op.Call(actionId, _)` the user's `=>` transform is never invoked; if it is `Op.Slice`/`Op.Add` the value stack is left underflowed and `valStack.pop()` in `Op.Add`/`Op.Drop` returns `undefined`, producing a corrupted output string. The dual direction (an op executed once too often) also occurs — a second random counterexample, [[], [e()->3, e()->0], [e()->3, e()->0], [e()->2, e(o1)->0, c(0)->1]] with entry 3 on input "0", yields ops [] before the merge and ['o1'] after it.

**Suggested fix.**

Make reduction 3 respect ε-cycle structure. The cheapest sound rule (empirically clean over 300k random automata) is to exclude from merging every state that lies on an ε-cycle: compute the states on ε-cycles once per pass (a DFS over `Edge.Eps` back-edges) and `continue` past them when filling `representative`, leaving them as their own representatives. A tighter alternative is to refuse a merge of s1 and s2 when one is ε-reachable from the other. Either way, the doc comment at lines 576-578 must be corrected: the justification is not "identical edge lists imply identical futures" but "identical edge lists imply identical futures *provided* the identification does not change the ε-cycle structure the runtime's per-position `visited` set observes". Additionally, since the current safety of the reduction depends on `build` never emitting two distinct states with the same op-bearing edge on a common ε-path, that property should be `softAssert`ed (or the guard added unconditionally so it does not need to be).

## M5. Reverse determinization has no size bound: a fixed-length prefix in a string pattern makes the compiler build an exponentially large table with no diagnostic and no fallback

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:716` — *perf*, refuted 0/3

**What's wrong.**

`reduceStates`'s doc comment sells the three reductions as what keeps the encoded program small ("the encoded NFA section shrinks linearly and the viability matrix ... shrinks with the state count"), but the dominant term is not the NFA size — it is `revSets.size * states.size` bits for the viability matrix plus `revSets.size * classes` integers for the transition table. `reverseDeterminize` is an unbounded subset construction over the *reversed* NFA, i.e. it materialises the reachable-state DFA of the reversal of the recognised language, and there is no cap, no counter, no `fail(...)`, and no fallback to the legacy prefix-composition translation in `SplitCompiler.makeStringRegionSplit` (which only handles `compile` returning `N`, i.e. a reported error).

The reversal of a language with a fixed-length *prefix* followed by an unbounded tail is the classic exponential case (`Sigma* a Sigma^k` needs 2^(k+1) DFA states), so a pattern of the form `k` character classes, then a literal, then `Str` blows up. I modelled `reverseDeterminize` exactly (epsilon-predecessor closure + per-class predecessor sets, seeded from `close({accept})`) on that NFA shape and measured: k=8 -> 513 reverse states; k=10 -> 2049; k=12 -> 8193; k=14 -> 32769; k=16 -> 131073 reverse states, i.e. 2^(k+1)+1, with the viability section alone reaching 415,065 base64 characters at k=16 and the transition section 786,438 integers. At k=20 that is ~2.1M reverse states, ~8 MB of base64 and ~25 MB of decimal integers embedded as a single JS string literal, on top of a `LinkedHashMap[Set[Int], Int]` with 2M entries in the compiler.

For calibration, the existing `CommaSep(Email)` golden already emits a 5,253-character literal (130 NFA states, 47 reverse states, 1,019 characters of viability bits), so the quadratic term is visible even on the tests that do exist.

**Scenario.**

```
pattern C = "a"..="z"
pattern P = C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ C ~ "a" ~ Str

"abcdefghijklmnopqrstuvwxyz" is P
```
The pattern is 23 NFA states after reduction, but `reverseDeterminize` enumerates 2^21 = 2,097,153 subsets: the compiler allocates millions of `Set[Int]`s, `packBits` produces a multi-megabyte string, and the generated `.mjs` contains it as one string literal. There is no error message and no way for the user to know why compilation stopped making progress; `regionSupported` in SplitCompiler.scala accepts the pattern, so the legacy translation (which handles it in linear space) is never used.

**Suggested fix.**

Bound the construction: thread a budget through `reverseDeterminize` (e.g. cap `ids.size * states.size` bits, or simply cap `ids.size`) and, on overflow, abandon the automaton for this region. Since `compile` already has a principled "give up" path, the cleanest shape is to return `N` — but with a *warning* rather than an error, and to have `SplitCompiler.makeStringRegionSplit` fall back to `makeStringPrefixMatchSplit` in that case, the same way `regionSupported` already routes unsupported constructs to the legacy translation. At minimum, log the (revStates, states, table length) triple next to the existing `log(s"String region: ...")` line and `softTODO` the missing bound so the limitation is recorded.

## M6. Reverse determinization is unbounded: exponential subset blow-up hangs/OOMs the compiler with no guard, timeout, or fallback

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:716` — *design*, refuted 0/3

**What's wrong.**

`reverseDeterminize` is a textbook subset construction over the reversed NFA. Its state count is |DFA(L^R)|, which is 2^Theta(n) for languages of the form Sigma^k a Sigma* — precisely the shape produced by `<charclass> ~ ... ~ <charclass> ~ <literal> ~ Str`. Nothing anywhere bounds it: `compile` (line 894) has no size guard, `encode` (line 839) has no guard, and `SplitCompiler.regionSupported` decides the automaton-vs-legacy fallback purely syntactically, so there is no way to bail out to the old translation once the blow-up starts.

Three costs compound:

1. `transitions` is `revStates * classCount` Ints and the viability matrix is `revStates * stateCount` bits (line 865), both emitted verbatim as a JS string literal at *every* call site.
2. `worklist.remove(0)` on an `ArrayBuffer` (line 751) is O(n) per pop, making the construction O(revStates^2) in element moves on top of the exponential state count.
3. The JS side undoes the packing: `decodeBits` (Runtime.mls:176) expands the base64 section into a JS array with one boolean element per bit, so a 10^6-bit matrix becomes a 10^6-element array at run time. The base64 packing only saves source size, not runtime memory.

I verified the exponential claim by hand for k=1 (L = Sigma a Sigma*): the reachable reverse subsets are {q2}, {q1,q2}, {q0,q2}, {q0,q1,q2} = 4 = 2^(k+1). In general the subset after reading suffix w is {k+1} union {i in [0,k] : w[k-i] == 'a'}, giving exactly 2^(k+1) distinct subsets.

**Scenario.**

```
pattern Blow =
  ("a".."z") ~ ("a".."z") ~ ("a".."z") ~ ("a".."z") ~ ("a".."z") ~ ("a".."z") ~
  ("a".."z") ~ ("a".."z") ~ ("a".."z") ~ ("a".."z") ~ ("a".."z") ~ ("a".."z") ~
  "q" ~ Str

"abcdefghijklq" is Blow
```
This passes `containsStringSeq` and `regionSupported` (the trailing `Str` resolves to a `ClassLikeSymbol`, hitting the `case N => arguments.forall(...)` arm), so it is compiled by `StringCompiler`. With k = 12 the reverse determinization reaches 2^13 = 8192 states over ~15 NFA states and 3 classes: the viability section alone is 8192*15 = 122880 bits = 20480 base64 characters, and the `revTransitions` section is 8192*3 = 24576 comma-separated integers (~120 KB of text). The emitted JS therefore contains a ~140 KB string literal for a 14-element pattern, duplicated once per use site.

Raise k to 20 and it is 2^21 = 2.1M reverse states: `revTransitions` alone is ~64 MB of source text, the viability string ~8.4 MB, and `worklist.remove(0)` performs ~2*10^12 element moves. The compiler does not diagnose anything; it simply hangs and then OOMs. At k = 25 it is unreachable in any lifetime.

**Suggested fix.**

Add an explicit budget to `reverseDeterminize`/`encode` (e.g. cap `revStates * stateCount` and `revStates * classes`). On overflow, abandon the automaton and either report a diagnostic pinning the pattern or return `N` from `compile` so `SplitCompiler` falls back to `makeStringPrefixMatchSplit`, exactly as it already does for `regionSupported == false`. Independently: replace `worklist.remove(0)` with an index cursor into the buffer (the worklist is already processed in strictly increasing id order, so a `var head = 0` pointer is a drop-in), and represent the viability matrix on the JS side as a packed string with a `charCodeAt`-based bit test instead of unpacking into a boolean-per-bit array in `decodeBits`.

## M7. `regionSupported` admits `Negation` and conjunctive `Composition`, which `StringCompiler.build` unconditionally `fail`s on — previously-compiling patterns now produce a hard compilation error

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1199` — *design*, refuted 0/3

**What's wrong.**

`regionSupported` is documented as deciding whether "the pattern ... only uses constructs that the string automaton compiles faithfully", and it is the sole gate before `makeStringRegionSplit`. But `case Negation(pattern) => loop(pattern, bound)` (line 1199) and `case Composition(_, left, right) => loop(left, bound) && loop(right, bound)` (line 1198, which covers `and` as well as `or`) both return `true`, while `StringCompiler.build` calls `fail(...)` on `Not(_)` (StringCompiler.scala:436) and on `And(_)` (StringCompiler.scala:433). `fail` sets `failed`, reports an error through the ambient `Raise`, and `compile` returns `N`, so `makeStringRegionSplit` returns `RejectSplit`.

The old translation had no such error: `makeStringPrefixMatchSplit` returned `RejectPrefixSplit` for `Negation` (line 1001) and emitted real code for `Composition(false, ...)` (line 977). So a program that used to compile (and just never match, or actually match) is now rejected by the compiler. This is the gate and the compiler disagreeing about the supported language, which is exactly the kind of duplicated-knowledge split AGENTS.md warns against ("the logic for handling cases that ought to be similar should be centralized").

**Scenario.**

```
pattern NotA = ~("a")

if "b!" is NotA ~ "!" then 1 else 2
//| COMPILATION ERROR: Negations are not supported within string patterns yet.
// (before this PR: compiled fine, evaluated to 2)
```
and
```
pattern AB = "a" and "a"
if "ax" is AB ~ "x" then 1 else 2
//| COMPILATION ERROR: Conjunctions are not supported within string patterns yet.
```

**Suggested fix.**

Make `regionSupported` return `false` for `Negation` and for `Composition(false, _, _)` so those regions stay on the legacy translation, and add `:fixme` regression tests for both. Better still, derive the gate from `StringCompiler` itself (e.g. a `StringCompiler.supports(pat)` predicate, or run the build speculatively with a suppressed `Raise` and fall back on `failed`) so the two cannot drift apart.

## M8. `given Raise = Function.const(())` turns a rejected whole-body region into a silently always-failing `unapplyStringPrefix`

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1487` — *miscompilation*, refuted 0/3

**What's wrong.**

`compilePattern(pd)` suppresses diagnostics while generating `unapplyStringPrefix`, on the assumption that "they have been already reported in the translation of `unapply`". That assumption no longer holds: `unapply` compiles `pd.pattern` through `makeMatchSplit`, which decomposes `Composition` *before* reaching the `Concatenation` case, so each alternative is compiled as its own region (or not at all). `unapplyStringPrefix`, by contrast, feeds the **whole body** to one `StringCompiler` (line 1490-1495) because `containsStringSeq(pd.pattern) && regionSupported(pd.pattern, Set.empty)` holds for the whole body.

A construct that only appears in a non-`~` alternative therefore triggers `fail` in `makeStringPrefixAutomatonSplit` only, where the error is swallowed and the method degenerates to `failure` (line 1283). The legacy `makeStringPrefixMatchSplit` would have generated working code for that alternative. The result is a runtime behaviour change with no diagnostic at all.

**Scenario.**

```
pattern R = ("a" ~ "b") | ~("c")

// forced onto the legacy prefix protocol by the guard on the right operand
if "abz" is R ~ (rest where true) then rest else "no"
//| = "no"     (WRONG, silently: R.unapplyStringPrefix always fails)
// before this PR: R.unapplyStringPrefix("abz") = MatchSuccess(["ab", "z"]), result "z"
```
`R.unapply` still works (`"ab" is R` = true), so nothing warns the user that the prefix matcher was quietly turned into a constant failure.

**Suggested fix.**

Do not swallow errors that the new automaton path raises. Either (a) keep the ambient `Raise` for `makeStringPrefixAutomatonSplit` and de-duplicate identical diagnostics, or (b) when `StringCompiler.compile` returns `N` in prefix mode, fall back to `makeStringPrefixMatchSplit` instead of `failure`, so behaviour is never silently lost.

## M9. `regionSupported` accepts constructor patterns with no resolved symbol, crashing `Instantiator` with `lastWords("Missing symbol for constructor pattern")`

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1197` — *crash*, refuted 0/3

**What's wrong.**

`regionSupported`'s last `Constructor` arm is `case N => arguments.forall(_.forall(loop(_, bound)))`. That arm is reached not only for class/object symbols (the case the comment justifies) but also when `target.resolvedSym` is `N` entirely — i.e. for erroneous constructor patterns, which the elaborator does produce (`case OpApp(lhs, op, rhs :: Nil) => Pattern.Constructor(term(op), S(...))` with an unresolved `op`, and `case sel: (SynthSel | Sel) => Constructor(term(sel), N)`). `arguments.forall` on such a node returns `true`, so the whole region is judged supported.

`makeStringRegionSplit` then runs `new Instantiator`, whose `Constructor` case matches on `target.symbol` and ends with `case N => lastWords(s"Missing symbol for constructor pattern ...")` (Instantiator.scala:120). `lastWords` is `throw new Exception("Internal Error: ...")` (utils/package.scala:209), so the compiler aborts.

The old translation handled this gracefully: `makeStringPrefixMatchSplit`'s `Constructor` case ends in `case S(_: ModuleOrObjectSymbol) | S(_: ClassSymbol) | N => RejectPrefixSplit` (line 970). Note also that the gate uses `resolvedSym` while `Instantiator` uses `symbol`; the two are computed differently (`Term.symbol` vs `Term.resolvedSym`) and can disagree independently of this bug.

**Scenario.**

`ups/RangePatterns.mls` already documents that `0..< 256` elaborates to `Constructor(<error>, S([...]))` ("Cannot use this ‹error› as a pattern."). Putting such a node inside a sequence:
```
:pe
:e
if "x" is (0..< 256) ~ "y" then 1 else 2
//| java.lang.Exception: Internal Error: Missing symbol for constructor pattern `.<`
```
Same for an unresolved selection, e.g. `if "x" is Char.NoSuchPattern ~ "y" then 1 else 2`.

**Suggested fix.**

Split the `case N` arm: return `true` only when `symbolOption` actually resolved to a `ClassSymbol`/`ModuleOrObjectSymbol`, and `false` when `target.resolvedSym` (or `target.symbol`) is `N`. Also make `regionSupported` and `Instantiator` agree on which of `symbol`/`resolvedSym` they consult, and add an `assert`/`softAssert` in `Instantiator` documenting the precondition the gate is supposed to establish.

## M10. String range patterns lose `rightInclusive` when compiled to `CharClass`, so `"a" ..< "z"` inside a `~` sequence wrongly matches "z"

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Instantiator.scala:128` — *miscompilation*, refuted 0/3

**What's wrong.**

`SP.Range(lower, upper, rightInclusive)` carries an exclusivity flag that the elaborator faithfully preserves (`Elaborator.scala:2516`, `..<` gives `incl = false`), and that the non-compiled path honours: `makeRangeTest` picks `lt` vs `lteq` based on it (SplitCompiler.scala:253), and the legacy string-prefix path calls `makeRangeTest(stringHeadSymbol, lower, upper, rightInclusive, ...)` (SplitCompiler.scala:1039).

The new `CharClass(lower.head.toInt, upper.head.toInt)` drops `rightInclusive` entirely, and `Pattern.CharClass` is documented as "the *inclusive* range `lo` to `hi`". The comment claims it "mirrors the previous expansion `(lower.head to upper.head)`" — true of the old *`@compile`* path, but the `~` path did **not** go through `Instantiator` before this PR; it went through `makeRangeTest`, which was correct. So routing `~` sequences through `Instantiator` is a new silent regression for exclusive string ranges. No test covers `..<` with string bounds.

**Scenario.**

```
// exclusive upper bound
"z" is ("a" ..< "z")          //| = false   (correct, uses makeRangeTest)
"z!" is ("a" ..< "z") ~ "!"   //| = true    (WRONG; should be false)
```
Same divergence for a definition: `pattern Lower = "a" ..< "z"` behaves differently depending on whether it is used bare or inside a sequence.

**Suggested fix.**

Either encode exclusivity into the class (`CharClass(lower.head, upper.head - (if rightInclusive then 0 else 1))`, guarding against an empty range which should become `Never`), or add a `rightInclusive` field to `Pattern.CharClass` and honour it in `StringCompiler.build`'s `addChr`. Add regression tests for `"a" ..< "z"` both bare and inside `~`.

## M11. Polymorphic-recursive parametric string patterns now hang the compiler in `Instantiator` at ordinary (non-`@compile`) use sites

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1241` — *nontermination*, refuted 0/3

**What's wrong.**

`makeStringRegionSplit` unconditionally runs `new Instantiator` on the fully applied pattern. `Instantiator.schedule` memoizes on `Instantiation(symbol, arguments)` (structural equality on the argument `Pat`s), so a definition whose body applies itself to a *strictly larger* argument enqueues an infinite chain of distinct instantiations and `runInstantiationLoop` never terminates.

`regionSupported` does not detect this: its `visited` guard is keyed on the `PatternSymbol`, not on the instantiation, so the second occurrence of `Rep` short-circuits to `true` and the site is accepted. Before this PR the `Instantiator` was only reachable via `@compile`/`compilePatternImpl`; ordinary use sites went to `makeMatchPatternSplit` and the compiler terminated (the divergence, if any, was at run time). The PR makes the hang reachable from plain source with no annotation.

**Scenario.**

```
pattern Digit = "0" ..= "9"
pattern Rep(pattern P) = (P ~ Rep(Rep(P))) | ""

if "12" is Rep(Digit) then 1 else 2
// compiler hangs: instantiates Rep(Digit), Rep(Rep(Digit)), Rep(Rep(Rep(Digit))), ...
```

**Suggested fix.**

Bound the instantiation worklist (depth or count) in `Instantiator.runInstantiationLoop` and report a proper "pattern instantiation does not terminate / self-embedding higher-order pattern" error, as `StringCompiler.checkTailPositions` already does for the first-order case. At minimum, gate `isParametricStringSite` on a check that the definition body only applies its own parameters unchanged.

## M12. `multiMatcherStringBranch` ignores `compiled.actions` in match-only mode, so `@compile` silently changes the observable effects of a string pattern's transforms

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Compiler.scala:289` — *effect-semantics*, refuted 0/3

**What's wrong.**

At line 289 the branch takes the `strPatMatchWhole` (recognition-only) path whenever `isMatchOnly`, regardless of `compiled.actions`. The other new string entry point, `SplitCompiler.makeStringRegionSplit`, takes the opposite decision: its condition is `compiled.pure || (!outputNeeded && compiled.visibleSlots.isEmpty && compiled.actions.isEmpty)`, and its scaladoc states the intended rule explicitly — "Transforms, however, always force the parsing entry point - they run exactly once on the committed parse, even when the match is only used as a condition."

The two paths are reachable from the *same* source pattern: `x is P` goes through `makeMatchSplit` -> `makeStringRegionSplit`, while `x is @compile P` goes through `compilePatternImpl` -> `Compiler.buildMultiMatcherBody` -> `multiMatcherStringBranch`. `Split.from` calls `makeMatchSplit(..., outputNeeded = false)` for every top-level `is`, and `compilePatternImpl` then picks `ResultMode.MatchOnly` whenever `!outputNeeded` and no extraction slots are involved — which is the common case. So `@compile` flips whether a transform's side effects happen.

The PR's own `CompiledSemantics.mls` pins the run-the-transform behaviour as the intended semantics (`probe("ab") //| > ran`), so the `@compile` path violates the semantics this PR documents. (For non-`~` patterns both paths agree on dropping the transform — verified — so this divergence is newly introduced here.)

**Scenario.**

```mls
:js
open annotations

fun probe(x)  = if x is ("a" => print("ran"))  ~ "b" then "yes" else "no"
fun probeC(x) = if x is @compile (("a" => print("ranC")) ~ "b") then "yes" else "no"

probe("ab")
//| > ran
//| = "yes"

probeC("ab")
//| = "yes"     <-- "ranC" is never printed
```

The two patterns are identical up to `@compile`, which is documented as an optimization annotation, yet only the un-annotated one runs the transform. Any transform performing I/O, raising an effect, mutating state, or throwing will behave differently under `@compile`.

**Suggested fix.**

Mirror `makeStringRegionSplit`'s condition in `multiMatcherStringBranch`: use `strPatMatchWhole` only when `compiled.pure || (compiled.actions.isEmpty && compiled.visibleSlots.isEmpty)`, and otherwise emit the `strPatParseWhole` call even in `ResultMode.MatchOnly` (discarding the returned output/slots and testing only for non-null). Factor the shared "which entry point does this compiled region need" decision into one helper used by both call sites so the two paths cannot drift again, and add a `CompiledSemantics.mls` case that runs the `probe`/`probeC` pair above.

## M13. Flattening nested `Concat` re-associates `~`, producing a different output value than the sub-pattern computes on its own

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Instantiator.scala:148` — *miscompilation*, refuted 0/3

**What's wrong.**

`parts` splices an immediately-nested `Concat` into its parent, so `a ~ (b ~ c)` and `(a ~ b) ~ c` both become `Concat(a :: b :: c :: Nil)`. `StringCompiler.build` then folds the element outputs strictly left-to-right with `Op.Add`, which the runtime engine implements as JavaScript `+` (`Runtime.mls`, op 2: `let b = pop(); let a = pop(); push(a + b)`). JS `+` is *not* associative across mixed operand types, so re-association changes the produced value whenever a transform in the spine yields a non-string.

The flattening is applied *after* instantiation, so it also fires across pattern-parameter substitution: the body `"#" ~ S` with `S := (p ~ q)` becomes a three-element concat, silently discarding the grouping the user wrote. The result is that the very same sub-pattern produces one value when referenced through a named synonym and a different value when passed as a pattern argument.

The justification in the comment ("so that the string pattern compiler sees the whole `~`-spine at once") does not hold: both consumers of `Concat` already recurse through nesting — `build` (line 405ff) rebuilds the fold for a nested `Concat`, and `checkTailPositions` (line 247-251) propagates the `tail` flag through `ps.last`. Nothing needs the spine flat.

**Scenario.**

Verified by running the diff-test suite on a scratch file:

```
:js

if "ab" is ((("a" => 1) ~ ("b" => 2)) as r) then r else "no"
//│ = 3

pattern S = ("a" => 1) ~ ("b" => 2)

if "#ab" is (("#" ~ S) as r) then r else "no"
//│ = "#3"      // correct: "#" + (1 + 2)

pattern Wrap(pattern S) = "#" ~ S

if "#ab" is (Wrap(("a" => 1) ~ ("b" => 2)) as r) then r else "no"
//│ = "#12"     // WRONG: (("#" + 1) + 2)
```

The first two blocks establish that `S`'s output is the number `3` and that `"#" ~ S` is `"#3"`; substituting the *same* pattern as an argument to `Wrap` yields `"#12"`. Writing the parentheses explicitly (`"#" ~ (("a" => 1) ~ ("b" => 2))`) also yields `"#12"`.

**Suggested fix.**

Drop `parts` and build `Concat(instantiate(left) :: instantiate(right) :: Nil)`; let `StringCompiler` flatten internally only where it is provably value-neutral (e.g. when `isPureDeep` holds for the whole spine, so the output is a single slice). If flattening is kept for other reasons, restrict it to elements for which `isPureDeep` holds, and document that `~` output is a strict left fold of `+`.

## M14. `Pattern.simplify` drops bare empty string literals from `Concat`, changing the match output's value and type

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala:208` — *miscompilation*, refuted 0/3

**What's wrong.**

The comment claims empty literals "consume nothing and contribute nothing to the output", but the output of a `Concat` is the left fold of its element outputs under JS `+` (`Op.Add`), and `"" + v` is not `v` when `v` is not a string — it is `String(v)`. Dropping the `""` element therefore changes both the value and its runtime type.

The divergence is observable because `simplify` is only applied on one of the two paths that compile a string region: `Compiler.multiMatcherStringBranch` calls `StringCompiler.stringFragment(pattern).simplify` (Compiler.scala:271), whereas `SplitCompiler.makeStringRegionSplit` compiles the instantiated pattern without simplifying. So the *same* pattern definition compiles to two different outputs depending only on whether the match site carries `@compile`.

The dropping is also inconsistent by construction: `Rename(Literal(StrLit("")), x)` and `Extract(Literal(StrLit("")), _, _)` are correctly retained, so only the bare form is affected — which makes the resulting semantics depend on incidental syntax.

Secondary point: when every element is dropped, the replacement `Literal(StrLit("")) :: Nil` is a freshly allocated literal with no `Loc`, so the rebuilt `Concat` loses its source location (see also the `toLoc` finding).

**Scenario.**

Verified by running the diff-test suite on a scratch file:

```
:js

open annotations

pattern EmptyThenOne = "" ~ ("a" => 1)

if "a" is (EmptyThenOne as r) then r else "no"
//│ = "1"      // region path: "" + 1

fun f(x) = if x is (@compile EmptyThenOne) as r then r else "no"
f("a")
//│ = 1        // @compile path: the "" was dropped by `simplify`
```

One pattern, two outputs (`"1"` vs `1`), differing only by the `@compile` annotation — which is documented as a pure optimisation switch.

**Suggested fix.**

Either stop dropping bare empty literals in `Concat` (they are cheap: `build` compiles `Literal(StrLit(""))` to zero transitions), or only drop them when the surrounding concat is value-irrelevant (`isPureDeep`, or when the concat's value is not demanded). Independently, `simplify` should be applied consistently on both region-compilation paths so that `@compile` cannot change observable semantics.

## M15. Compiler crash (AssertionError) when a string region contains a rejected node whose sub-patterns come from different source blocks

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:434` — *crash*, refuted 0/3

**What's wrong.**

The new rejection paths in `StringCompiler.build` report diagnostics with `pattern.toLoc` on an *instantiated* `ups.Pattern` (lines 389, 434, 437). `ups.Pattern` extends `AutoLocated` and computes `toLoc` from `children` (Pattern.scala:51-66); for `And`/`Or`/`Concat` the children are the sub-patterns, and for `Synonym` the children are `pattern.symbol +: pattern.arguments` — i.e. the location of the referenced pattern's *definition site* (`PatternSymbol.toLoc = id.toLoc`).

`AutoLocated.mkLoc` asserts `origins.size === 1` (syntax.scala:49). In hkmc2 diff tests each block gets its own `Origin` (`DiffMaker.scala:339: Origin(file, blockLineNum + output.linesDelta, fph)`), and across files origins obviously differ. So as soon as a rejected node has two children resolving to definitions in different blocks/files, the assertion blows up instead of the intended error being reported, and the whole definition is dropped, cascading into `No definition found in scope` and a runtime `ReferenceError`.

This is reachable only because the PR introduced these `Pat.toLoc` call sites on instantiated patterns inside string regions; `Concat` also participates, since `Pattern.simplify` rebuilds `Concat` without a location (Pattern.scala:203-213) so the auto-computed span is used there too.

**Scenario.**

Verified by appending to `hkmc2/shared/src/test/mlscript/ups/regex/NonRegular.mls` (each `pattern` in its own block):

```
pattern ProbeA = "a"

pattern ProbeB = "b"

:e
pattern ProbeC = "x" ~ (ProbeA & ProbeB)

"xa" is ProbeC
```

Actual output:

```
//│ /!!!\ Uncaught error: java.lang.AssertionError: assertion failed:
//│   (List(NonRegular.mls:+86, NonRegular.mls:+88),
//│    And(List(Synonym(Instantiation(pattern:ProbeA,List())),
//│             Synonym(Instantiation(pattern:ProbeB,List())))))
//│ 	at: hkmc2.AutoLocated.mkLoc(syntax.scala:49)
//│ 	at: hkmc2.semantics.ups.Pattern.toLoc(Pattern.scala:31)
//│ 	at: hkmc2.semantics.ups.StringCompiler.build(StringCompiler.scala:434)
```

Expected: the intended `Conjunctions are not supported within string patterns yet` error. Putting `ProbeA` and `ProbeB` in the *same* block makes the crash disappear, confirming the origin mismatch is the trigger.

**Suggested fix.**

Do not rely on `AutoLocated` spans for instantiated `ups.Pattern` nodes. Either carry an explicit `Opt[Loc]` on the nodes the `Instantiator` builds (as `Instantiation` already does) and use it in these diagnostics, or make `mkLoc` degrade gracefully (return `N` instead of asserting) when children span multiple origins. Add a regression test with definitions in separate blocks.

## M16. Exclusive string ranges `..<` become inclusive inside `~` sequences — a regression introduced by routing `Concatenation` through `Instantiator`, and `..<` on strings has zero test coverage

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Instantiator.scala:133` — *miscompilation*, refuted 0/3

**What's wrong.**

`Instantiator.instantiate` for `SP.Range(lower, upper, rightInclusive)` binds `rightInclusive` and then never uses it: the string branch emits `CharClass(lower.head.toInt, upper.head.toInt)`, an *inclusive* range. Before this PR that path was reachable only under `@compile`; `Concatenation` was handled by `makeStringPrefixMatchSplit`, whose `Range(lower: StrLit, upper: StrLit, rightInclusive)` case (SplitCompiler.scala:1029-1040) forwards `rightInclusive` to `makeRangeTest`, which picks `lt` vs `lteq` correctly (SplitCompiler.scala:250-253).

This PR reroutes every `Concatenation` to `makeStringRegionSplit` -> `Instantiator`, so a correct `..<` inside a sequence now silently loses its exclusivity. `regionSupported` explicitly whitelists `Range(_, _, _)` (SplitCompiler.scala:1194), so nothing stops it.

`RangePatterns.mls` only exercises `..<` on *integers*; there is no test of `..<` on strings anywhere in `hkmc2/shared/src/test/mlscript/`, so the divergence between the two paths is invisible.

**Scenario.**

Verified by running `hkmc2DiffTests` on a scratch file:

```
:js
open annotations
pattern NotNine = ("0" ..< "9") ~ ""

"9" is NotNine
//| = true          <- WRONG: '9' is excluded by ..<

"9" is ("0" ..< "9")
//| = false         <- correct (legacy makeRangeTest path)

fun mm(s) = if s is @compile NotNine then "yes" else "no"
mm("9")
//| = "yes"         <- WRONG, multi-matcher path is equally affected
```

So `("0" ..< "9")` and `("0" ..< "9") ~ ""` disagree on the character '9'.

**Suggested fix.**

In `Instantiator.scala:130-134`, honour the flag: `CharClass(lower.head.toInt, if rightInclusive then upper.head.toInt else upper.head.toInt - 1)`, and reject / report an empty class when the resulting `lo > hi` (also worth doing for reversed bounds such as `"z" ..= "a"`). Add to `hkmc2/shared/src/test/mlscript/ups/regex/CompiledSemantics.mls`:

```
// Exclusive ranges stay exclusive inside a sequence.

pattern NotNine = ("0" ..< "9") ~ ""

:expect false
"9" is NotNine

:expect true
"8" is NotNine

:expect false
"9" is ("0" ..< "9")
```

## M17. `NonRegular.mls` blesses a rejected pattern as "never matches", but `unapply` and `@compile` disagree on it — the file's own tests are chosen so the disagreement is invisible

`hkmc2/shared/src/test/mlscript/ups/regex/NonRegular.mls:19` — *test-gap*, refuted 0/3

**What's wrong.**

The header comment (NonRegular.mls:5-7) asserts "Self-embedding patterns are rejected with an error pinning the culprit reference, and nothing is compiled: the pattern never matches." The only evidence offered is `"(())" is Parens` -> `false` (line 18-19) and `"abc" is Outer` -> `false` (line 80-81) — inputs that exercise the *rejected* alternative only.

But `Parens = ("(" ~ Parens ~ ")") | ""` also has an `""` alternative. `P.unapply` is compiled alternative-by-alternative (`compilePattern` dispatches on `Composition` before it ever sees a `Concatenation`), so only the rejected alternative is dropped and the `""` alternative still compiles normally. `@compile P`, in contrast, hands the whole expanded pattern to one `StringCompiler`, whose `checkTailPositions` failure discards the entire region (`compile` returns `N`, and the call site emits `emptyMatchResult("rejected string pattern")`). The two entry points therefore disagree, and the claim in the comment is only true of one of them.

**Scenario.**

Verified by running `hkmc2DiffTests` on a scratch file:

```
:js
open annotations

:e
pattern Parens = ("(" ~ Parens ~ ")") | ""
//| [COMPILATION ERROR] This recursive use of pattern `Parens` is not in tail position.

"" is Parens
//| = true

fun viaCompile(s) = s is @compile Parens
//| [COMPILATION ERROR] ... (the same error, re-reported at the use site)

viaCompile("")
//| = false
```

`"" is Parens` is `true` while `"" is @compile Parens` is `false`, for the same pattern and the same input.

**Suggested fix.**

Decide on one behaviour (recommended: the whole definition is poisoned, so both are `false`, or both keep the surviving alternatives) and pin it. Add to `NonRegular.mls`, right after the existing `"(())" is Parens` block:

```
// The surviving `""` alternative must behave the same through both entry points.

:expect false
"" is Parens

:expect false
"" is @compile Parens
```

and fix the header comment to describe whichever semantics is chosen.

## M18. `NonRegular.mls` golden bakes in a duplicated diagnostic: the tail-position error is re-reported once per compiled region and once per `@compile` use site

`hkmc2/shared/src/test/mlscript/ups/regex/NonRegular.mls:72` — *diagnostics*, refuted 0/3

**What's wrong.**

`StringCompiler.checkTailPositions` walks `bodies`, i.e. every instantiation reachable from the region root, not just the root's own body. For a mutually recursive group, each member's `unapply` builds a region containing the whole group, so each member re-reports the same offending reference. That is why NonRegular.mls:65-78 records the identical five-line error twice (both copies pin `Inner` inside `Outer`'s body, with byte-identical locations); the second copy carries no new information.

The same duplication is unbounded across use sites: a user who writes `@compile Parens` in ten places gets ten more copies of the definition-site error, because `makeStringRegionSplit` compiles a fresh region per site. Committing this shape as a golden makes it a specified behaviour rather than a known wart.

**Scenario.**

Existing golden `NonRegular.mls:62-78` shows the error twice for one two-line program. Additionally, verified in a scratch file: adding `fun viaCompile(s) = s is @compile Parens` after an already-erroring `pattern Parens = ("(" ~ Parens ~ ")") | ""` produces a *third* copy of the same error, located on the `pattern Parens` line rather than on the use site, so the user cannot tell which of their expressions triggered it.

**Suggested fix.**

Deduplicate: report tail-position violations once per pattern definition (e.g. memoize the check per `PatternSymbol` in the `Context`, or only check bodies whose owner is the region root), and at use sites report a short secondary message pinned to the *use* location instead of re-emitting the definition-site error. Then regenerate the `NonRegular.mls` golden so it records one error, and add a use-site block asserting that a second `@compile` reference does not multiply the diagnostics.

## M19. `Str` with arguments inside a string pattern: an error is reported but the pattern then matches anyway; `StringCompiler`'s own guard for this is dead code with no test

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:389` — *miscompilation*, refuted 0/3

**What's wrong.**

`StringCompiler.build` has a `ClassLike(sym, arguments) if sym is ctx.builtins.Str` case that calls `fail(msg"`Str` cannot have arguments in a string pattern.")` for `S(_)` arguments. That branch is unreachable: `Instantiator.keyedArguments` errors first ("Class `Str` has no parameters") and drops the arguments, so `StringCompiler` only ever sees `ClassLike(Str, N)` — the any-string wildcard. The reported error then does not stop the region from being compiled, and the pattern matches as if the argument had not been written.

Because the branch is unreachable, its message string is never tested, and the observable behaviour after the error (a *successful* match) is never tested either. The PR's `Str`-as-any-string change (CompiledSemantics.mls:39-50) makes this strictly worse than before: previously `Str` in string position consumed exactly one character, so `Str("x") ~ "b"` at least failed on most inputs.

**Scenario.**

Verified by running `hkmc2DiffTests` on a scratch file:

```
:js
open annotations
pattern StrArg = Str("x") ~ "b"
//| [COMPILATION ERROR] Class `Str` has no parameters.

"xb" is StrArg
//| = true      <- and also `"zb" is StrArg` is true: the argument is ignored
```

A user writing `Str("x")` gets an error and a pattern that matches every `<anything>b`.

**Suggested fix.**

Either make the erroneous pattern degrade to `Never` in `Instantiator` (so the match fails after the error, matching the `Or(Nil)`/`And(Nil)` convention used elsewhere), or remove the now-dead `fail` branch in `StringCompiler.scala:388-390` and note in a comment that `Instantiator` normalizes it away. Whichever is chosen, pin it in `ups/regex/NonRegular.mls`:

```
:e
pattern StrArg = Str("x") ~ "b"

:expect false
"xb" is StrArg
```

## M20. Prefix mode (`unapplyStringPrefix`) is exercised by exactly one assertion, with an empty remainder — the whole `remaining` protocol and its greediness are unpinned

`hkmc2/shared/src/test/mlscript/ups/regex/Separation.mls:33` — *test-gap*, refuted 0/3

**What's wrong.**

`makeStringPrefixAutomatonSplit` (SplitCompiler.scala:1272-1298) is a brand-new entry point: it wraps the region in a lazy `Sigma*` tail, records the split point via `Op.Rem`, and returns `MatchSuccess([consumed, remaining], null)`. The only test of it in the whole suite is `Separation.mls:33-34`, `Integer.unapplyStringPrefix("123")` -> `MatchSuccess(["123", ""], null)` — a case where `remaining` is `""`, i.e. where a whole-match would give the same answer and where `Op.Rem`/`remStart` could be entirely broken without the test noticing. Nothing tests: a non-empty remainder, failure (`MatchFailure`), greediness through a recursive component, or alternation order in prefix position (the star is lazy, so leftmost-first must win over longest).

This matters because `unapplyStringPrefix` is also what the *legacy* `Concatenation` fallback calls (`makeStringPrefixMatchSplit`), so any regression here silently corrupts the guard/chain fallback path too.

**Scenario.**

All of the following currently behave correctly (verified in a scratch difftest run) and none is pinned by a test, so any future change to `Op.Rem`, to the lazy-star construction, or to the `Mode.Prefix` branch of `StringCompiler.compile` would go unnoticed:

```
pattern Pre  = ("a" ~ "b") | ("a" ~ "b" ~ "c")
Pre.unapplyStringPrefix("abcd")   //| = MatchSuccess(["ab", "cd"], null)
pattern Pre2 = ("a" ~ "b" ~ "c") | ("a" ~ "b")
Pre2.unapplyStringPrefix("abcd")  //| = MatchSuccess(["abc", "d"], null)
pattern Star = ("a" ~ Star) | ""
Star.unapplyStringPrefix("aaab")  //| = MatchSuccess(["aaa", "b"], null)
pattern Xs = "x" ~ (Xs | "")
Xs.unapplyStringPrefix("xxy")     //| = MatchSuccess(["xx", "y"], null)
Integer.unapplyStringPrefix("abc") //| = MatchFailure(null)
```

**Suggested fix.**

Add a new file `hkmc2/shared/src/test/mlscript/ups/regex/Prefix.mls` containing exactly the blocks above (with `:expect` on each), plus a prefix case with a transform and one with a binding, so the `[output, remaining, slots...]` layout of `parseRun` is pinned. E.g.:

```
:js

pattern Digit = "0" ..= "9"
pattern Integer = Digit ~ (Integer | "")

// The remainder is the un-consumed suffix, and the prefix is committed
// leftmost-first, not longest.
Integer.unapplyStringPrefix("123abc")
//| = MatchSuccess(["123", "abc"], null)

Integer.unapplyStringPrefix("abc")
//| = MatchFailure(null)

pattern Pre = ("a" ~ "b") | ("a" ~ "b" ~ "c")
Pre.unapplyStringPrefix("abcd")
//| = MatchSuccess(["ab", "cd"], null)

// A transform in prefix position runs exactly once and supplies the output.
pattern Shout = ((Integer as n) => n + "!")
Shout.unapplyStringPrefix("12x")
```

## M21. A guard or `as`-chain anywhere in a string region silently reverts the whole region to the legacy greedy translation, changing the match result; no test and no `:fixme` records this

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1182` — *design*, refuted 0/3

**What's wrong.**

`regionSupported` returns `false` for `Guarded(_, _) | Chain(_, _)` anywhere in the region, and `compilePattern`'s `Concatenation` case then falls back to `makeStringPrefixMatchSplit` — the greedy prefix composition whose misbehaviour this PR exists to fix (see the three `:fixme`s the PR removes from `Simplification.mls`). So adding a vacuous guard to a sub-pattern changes the *matching relation*, not just the implementation. The user has no way to see which translation they got, and there is no test, `:fixme` or `:todo` recording the divergence — the PR's comment at SplitCompiler.scala:1170-1181 describes the fallback as a mere implementation detail.

**Scenario.**

Verified by running `hkmc2DiffTests` on a scratch file:

```
:js
open annotations
pattern Xs = "x" ~ (Xs | "")
pattern XsX = Xs ~ "x"

"xxxx" is XsX
//| = true                                    <- automaton

fun guardedRegion(s) = if s is (Xs where true) ~ "x" then true else false
guardedRegion("xxxx")
//| = false                                   <- legacy greedy: Xs eats all x's

fun chained(s) = if s is (Xs as Digit) ~ "x" then true else false
chained("xxxx")
//| = false
```

A guard that is always `true` flips the answer from `true` to `false`.

**Suggested fix.**

Short term: add these blocks to `ups/regex/Simplification.mls` under `:fixme` with the automaton answer as the `:expect`, so the divergence is a recorded known bug rather than silent:

```
// A guard anywhere in the region falls back to the legacy greedy translation,
// which changes the matching relation. See #<issue>.
:expect true
:fixme
if "xxxx" is (Xs where true) ~ "x" then true else false
```

Longer term: guards over already-consumed input are compatible with the two-pass scheme (evaluate them on the committed forward walk, and reject the whole match rather than backtrack) — or, if that is not acceptable, `regionSupported` should report a diagnostic rather than silently switching semantics.

## M22. Automaton table size is exponential in the pattern with no bound, no assertion and no diagnostic

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:716` — *generated-code-size*, refuted 0/3

**What's wrong.**

`reverseDeterminize` (StringCompiler.scala:716) is an unbounded subset construction: reverse states are `Set[Int]` subsets of the NFA state set, and there is no cap, no size check, no `softAssert`, and no user-facing error when the construction explodes. `encode` (StringCompiler.scala:865-877) then emits a `viability` matrix of `revStateCount * stateCount` bits, base64-packed, plus a `revTransitions` table of `revStateCount * classCount` decimal integers — both inlined verbatim as a JS string literal at the call site.

This makes generated code size `O(stateCount * 2^stateCount)` in the worst case. The classic witness is a language whose *reverse* needs exponentially many DFA states, i.e. a fixed-length prefix followed by a distinguishing character and then an unbounded tail. AGENTS.md requires asserting invariants the code relies on; the code relies on the reverse subset construction staying small (that is the entire justification of the Frisch-Cardelli scheme) and never checks it.

Compile time was still fast at the sizes I tested, so the failure mode is not a hang but a silently enormous generated module: 313 KB of string literals produced by a single 1-line pattern definition, retained forever at run time in `StrPat.programs` (see the separate decode-representation finding).

**Scenario.**

Measured empirically (file added, `sbt "hkmc2DiffTests/testOnly hkmc2.DiffTestRunner -- -z ZzBlowup"`, then removed):

    pattern AB = "a" | "b"
    pattern ABs = AB ~ (ABs | "")
    pattern Blow6  = AB ~ AB ~ AB ~ AB ~ AB ~ AB ~ "a" ~ ABs
    pattern Blow9  = AB * 9  ~ "a" ~ ABs
    pattern Blow12 = AB * 12 ~ "a" ~ ABs

Resulting table lengths (characters of JS string literal), read out of the `:soir` golden:

    Blow6 : revStates=131    matchWhole table   1,496   parsePrefix table   2,677
    Blow9 : revStates=1027   matchWhole table  13,198   parsePrefix table  21,142
    Blow12: revStates=8195   matchWhole table 120,718   parsePrefix table 192,469

Exactly 8x per +3 repetitions, i.e. 2^k. `Blow12` alone emits 313 KB of string literals into the module. `Blow20` would be ~80 MB; `Blow30` would exhaust memory during determinization with no error message. A user writing a fixed-width-field parser (`pattern Record = Digit~Digit~Digit~Digit~":"~Rest`) walks straight into this.

**Suggested fix.**

Add a configurable budget checked inside `reverseDeterminize` and again before `encode`: e.g. `if ids.size > MaxReverseStates || revStates * stateCount > MaxViabilityBits then fail(msg"This string pattern is too complex to compile to a finite matcher (...)" -> root.toLoc)` and fall back to the legacy translation instead of emitting the table (`compile` already returns `Opt[Compiled]`, and callers already handle `N` by rejecting/keeping the old path). Also add a `softAssert` documenting the assumed relationship between NFA size and reverse-DFA size, and record the trade-off in the class doc comment (which currently presents the reverse determinization as unconditionally cheap).

## M23. `StrPat.parseRun` allocates a frozen 2-element array per NFA edge examined, plus 4 frozen Maps and N closures per call

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:408` — *perf*, refuted 0/3

**What's wrong.**

This is the answer to LPTK's "crazy scheme" concern, but the cost is not where he thought. What is actually repeated per match, read off the generated `Runtime.mjs`:

1. `pushEdges` (Runtime.mls:404-409) does `stack.push([state, edges.[i]])`. An immutable tuple literal lowers to `globalThis.Object.freeze([...])` (JSBuilder.scala:255) — confirmed at Runtime.mjs:301-304. `pushEdges` is invoked once per NFA state entering the search frontier, and every state is re-expanded at every input position (the `gen` marks are per-position). So this is `O(n * E)` freshly allocated **frozen** 2-element arrays for an input of length n and an automaton with E edges. `Object.freeze` on a JSArray is a V8 runtime call that transitions the elements kind; it is on the order of 100 ns, and it also forces every later `item.at(0)`/`edge.at(2)` onto a slower elements kind. For the `CommaSep(Email)` automaton (130 states, ~250 edges) matching a 200-char input, that is up to ~50,000 `Object.freeze` calls, i.e. milliseconds per match.

2. Per `parseRun` call (Runtime.mls:284-310): one capture object, four `Object.freeze(new Map())` (`visited`, `parentState`, `parentOps`, `bindings` — Runtime.mjs:867-873), four arrays, plus three closures (`readSlot`, `execValueOp`, `runFrameOps` — Runtime.mjs:875-877).

3. Worse, `runOps` (Runtime.mls:364) was lifted into a *factory* by the lambda rewriter: `runOps = lambda$1(prog, frames, bindings, execValueOp, runFrameOps)` is re-evaluated at **every committed transition** (Runtime.mjs:918 and :940), i.e. once per consumed character. So one extra closure allocation per input character.

4. `visited` is already designed for the array idiom — it uses a monotone `gen` counter, the standard trick for reusing a scratch array — but stores into a hashed `Map` anyway. `visited`/`parentState`/`parentOps` are keyed by dense state ids `0..stateCount-1`, and `bindings` by dense slot ids `0..slotCount-1`; all four should be plain arrays (or `Int32Array`), turning hashed lookups into indexed loads.

By comparison, the `programs.has(table)` / `programs.get(table)` pair that prompted the review comment costs two hash-table probes on an already-hashed internalized string — nanoseconds. It is real waste, but it is three or four orders of magnitude below items 1-3.

**Scenario.**

`parseEmails(emails.join(","))` in `ups/regex/EmailAddress.mls` runs `parseWhole` over a ~200-character input against the 130-state automaton. Per call this executes on the order of 10^4-10^5 `Object.freeze([state, edge])` allocations (item 1), ~200 `runOps` closure allocations (item 3), 4 `Object.freeze(new Map())` (item 2), and ~10^5 hashed `Map` probes on small integer keys (item 4) — for what the algorithm claims is a linear-time scan. The same input through the recognition-only `matchWhole` path allocates nothing, so the gap between the two entry points is enormous and entirely accidental.

**Suggested fix.**

In `Runtime.mls`: (a) make the search stack two parallel `mut []` arrays of ints (`stackSource`, `stackEdgeIdx`) instead of pushing tuples, or at minimum push a `mut [...]` so no `Object.freeze` is emitted; (b) hoist `runOps`/`execChain`/`pushEdges` out of `parseRun` into module-level `fun`s taking their state explicitly, so the lambda rewriter cannot re-create them per transition; (c) replace `visited`/`parentState`/`parentOps` with three arrays sized `prog.stateCount` (the `gen` counter already makes reuse across rounds correct) and `bindings` with an array sized `prog.slotCount`; (d) reuse those scratch arrays across calls via fields on the decoded `Program`, since `parseRun` is not reentrant per program... or, if reentrancy is wanted, allocate them once per call but as plain arrays. Add a comment documenting that these are hot-loop representations chosen deliberately.

## M24. The transform-closure tuple and its lambdas are re-allocated on every match at every call site (LPTK's hoisting request)

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1256` — *perf*, refuted 0/3

**What's wrong.**

`makeStringRegionSplit` (SplitCompiler.scala:1256) and `makeStringPrefixAutomatonSplit` (SplitCompiler.scala:1286) both build `actionsTuple(compiled.actions, ...)` (TermSynthesizer.scala:103) *inside* the emitted split, i.e. inside the matching function's body. The `:soir` golden in `ups/regex/EmailAddress.mls:104-110` shows the result verbatim:

    define lambda  as fun lambda0(head, tail) { return Stack.Cons(head, tail) };
    define lambda1 as fun lambda1(head)       { return Stack.Cons(head, Stack.Nil) };
    define lambda2 as fun lambda2()           { return Stack.Nil };
    set tmp = [lambda0, lambda1, lambda2];
    set parseResult = runtime.StrPat.parseWhole("130,1,0,...", tmp, input);

All three lambdas are closed (they reference only the module-level `Stack`), yet they are declared inside `parseEmails`, so each call allocates three JSFunction objects, one array, and one `Object.freeze` on it (immutable tuple literals lower to `Object.freeze([...])`, JSBuilder.scala:255). Neither `LambdaRewriter` nor `Lifter` hoists them out, because `Lifter` only runs under `config.liftDefns` and lifts *definitions*, not the value computation that builds the tuple.

The empty case is even sillier: every `unapplyStringPrefix` emits `set tmp = []` (an `Object.freeze([])` per call) and passes it as `actions` even when `compiled.actions.isEmpty` — confirmed by the `:soir` of a plain `pattern Ident = ("a" ..= "z") ~ (Ident | "")`.

Regarding LPTK's literal complaint: the table string is **not** re-parsed per match. It is a JS string literal, hence internalized by V8 with a cached hash, and `StrPat.getProgram` (Runtime.mls:228) memoizes the decode in the module-level `programs` Map. So the decode happens once per distinct table per process. But the conclusion he draws is right for the other three reasons above, and the double `has`+`get` probe (Runtime.mls:229-230, Runtime.mjs:734-742) is a gratuitous second hash lookup that a single `get` + `undefined` test would avoid.

**Scenario.**

Any hot loop over `parseEmails` — e.g. `emails.map(parseEmails)` over 10^5 strings — performs 10^5 * (3 closure allocations + 1 array allocation + 1 `Object.freeze` + 2 `Map` probes) purely to hand the engine three constant closures and a constant table. None of these values depends on the scrutinee.

**Suggested fix.**

Hoist per LPTK's comment. Concretely, in this codebase there are two seams:

(1) For pattern *definitions*, `compilePattern(pd: PatternDef)` (SplitCompiler.scala:1454) already returns a list of members that become fields/methods of the generated pattern object (visible in the `:soir` as `define Email as pattern Email { method unapply = ...; method unapplyStringPrefix = ... }`). Add two more members alongside them: `val program = runtime.StrPat.decode("<table>")` and `val actions = [<lambdas>]`, both initialized once at module init (the decode is pure and can carry `@mayNotRaiseEffects`). `unapply`/`unapplyStringPrefix` then call `StrPat.runWhole(Email.program, Email.actions, input)`. This removes the per-call tuple, the per-call `Map` probes, and the `set tmp = []` for action-free patterns.

(2) For parametric use sites (`isParametricStringSite`) and inline `if` sites there is no owning definition. Mirror what `compilePatternImpl` already does at SplitCompiler.scala:1407-1410 for matcher `implementations`, but one scope further out: thread a `using` hoist-buffer capability (e.g. `TopLevelHoister` holding a `Buffer[(TempSymbol, Term)]` keyed by table string) from the `Elaborator` entry point that builds the file's `Blk`, and drain it into that `Blk`'s statement list. Keying by table string also deduplicates sites that compile the same region (see the code-size finding).

Obstacles to document while doing this: (a) the actions tuple is only hoistable because transform lambdas are currently closed — their parameters are the correspondence symbols (StringCompiler.scala:462-465) — but nothing enforces that `term` cannot capture an enclosing local, so the design should hoist the *decoded program* unconditionally and hoist the actions tuple only when it is closed; (b) `parseWhole` itself must stay at the call site (it invokes user actions and is deliberately not `@mayNotRaiseEffects`), only the constant operands move; (c) `SplitCompiler` is invoked deep inside term elaboration and currently has no handle on its enclosing block, which is the actual engineering cost of this change.

## M25. Automaton tables are duplicated per entry point and per use site, and recompiled from scratch each time

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1489` — *generated-code-size*, refuted 0/3

**What's wrong.**

Three separate duplications compound:

1. **Two tables per pattern definition.** `compilePattern` emits `unapply` (which goes through `makeStringRegionSplit` and embeds the whole-match table) *and* `unapplyStringPrefix` (SplitCompiler.scala:1489-1495, which embeds a full `parsePrefix` parsing table for a *different* automaton: `root ~ lazy-Sigma*`). The prefix table is the larger of the two and is emitted for every string pattern definition — even though this PR's own change makes almost every string site use the whole-match automaton instead, leaving `unapplyStringPrefix` reachable only from the legacy composition path.

2. **A full copy per parametric/inline use site.** `isParametricStringSite` sites and inline `~` sites each construct a fresh `Instantiator` + `StringCompiler` (SplitCompiler.scala:1241-1243) and inline the whole table at the site. Two sites using the same parametric pattern get two byte-identical multi-kilobyte literals, and pay the determinization cost twice at compile time.

3. **`matchTable` is a strictly redundant re-encoding of `table`.** In `encode` (StringCompiler.scala:878-884), `starts(r) = revSets(r) contains start`, and the `viability` bit at index `r * stateCount + start` is *the same predicate*. So `matchTable`'s four sections are: header (derivable), `bounds` (byte-identical to section 1 of `table`), `revTransitions` (byte-identical to section 4), and `starts` (column `start` of section 5). When one pattern is used both as a condition and as an extractor, the module carries both encodings of the same automaton and the runtime caches two decoded objects (`matchers` and `programs`) for it. The whole `Matcher` / `decodeMatcher` / `getMatcher` / `matchers` path in Runtime.mls:129-247 is a parallel implementation of a projection of `Program` — a DRY violation in the runtime library.

**Scenario.**

Measured by `:soir` on the `Email` chain from `ups/regex/EmailAddress.mls` (scratch file, since removed):

    pattern Email = UserName ~ "@" ~ Domain
      method unapply           -> matchWhole table    991 chars
      method unapplyStringPrefix -> parsePrefix table 2,079 chars   (mostly-dead method)

and for the parametric case:

    fun f(x) = if x is Rep1(Lower) then 1 else 0   -> matchWhole("3,0;97,123;1,2,1,1,1,1,1,2,1;001", x)
    fun g(x) = if x is Rep1(Lower) then 2 else 0   -> matchWhole("3,0;97,123;1,2,1,1,1,1,1,2,1;001", x)

byte-identical literals at both sites. In `EmailAddress.mls` itself, the single `CommaSep(Email)` site inlines 5,253 characters (EmailAddress.mls:111); a second use of `CommaSep(Email)` anywhere in the file would add another 5,253. Since each definition in the chain re-expands its full transitive closure, a chain of n definitions costs O(n * expansion) — quadratic in chain length. Combine with the exponential-blowup finding and a single file can easily emit megabytes.

**Suggested fix.**

(a) Only emit `unapplyStringPrefix`'s automaton when something can still call it, or better, derive prefix matching from the whole-match program at run time (the prefix automaton is `root ~ lazy-Sigma*`; the engine could take a `prefix` flag rather than a second table) so one table serves both methods. (b) Delete `matchTable`, `Matcher`, `decodeMatcher`, `getMatcher` and `matchers` entirely: implement `matchWhole` as the reverse scan over a decoded `Program`, testing `viable(prog, rev, prog.start)` instead of `starts.charCodeAt(rev) === 49`, and have call sites that only need recognition pass the same `table` string. This alone removes an entire duplicated decoder and cache, and makes the condition-vs-extractor uses of one pattern share a single cached program. (c) Deduplicate use-site tables by hoisting them (see the hoisting finding) keyed by table content, which also shares the compile-time determinization across sites.

## M26. `specialize(lit)` maps `Concat`/`CharClass` to `Never` under a *non-local* invariant with no assertion, so breaking the invariant silently miscompiles

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala:456` — *design*, refuted 1/3

**What's wrong.**

I verified the invariant the new case relies on and it does hold today, but only by an argument that lives entirely in another file:

- `Pattern.map` and `Pattern.reduce` bottom out at exactly the same set of positions (both stop at `NonCompositional`, both recurse through `And`/`Or`/`Not`/`Rename`/`Extract`), so `StringCompiler.containsStringNode` (built on `reduce`) is true iff a `Concat`/`CharClass` is visible to `specialize`'s `map`. Hence `absorbStrings` in `buildMultiMatcherBody` is exactly right.
- The only `syntax.Literal` a JS string can satisfy is `StrLit` (`Case.Lit` lowers to `===`), and the only `ClassLikeSymbol` a primitive string satisfies is `builtins.Str` (`JSBuilder` lowers it to `typeof sd === 'string'`; every other class lowers to `instanceof`, and `Object`/`Record`/`Tuple` tests are all false for a primitive string — I confirmed `"zz" is Object`, `"zzz" is { length: _ }`, and `Tuple.isArrayLike` on a string all yield `false`).

So `heads`'s filter (`case _: StrLit => false; case symbol if symbol is strSymbol => false`) really does exclude every head a string could take, and `specialize(lit)` is never reached with a `StrLit` head while a `Concat` is present.

The problem is that the code encodes this as a silent `Never` instead of asserting it. Note that the case is genuinely *live* and *correct* for non-string literal heads (e.g. labels `{"a" ~ "b", 1}` produce head `IntLit(1)`, under which a `Concat` really cannot match), so it cannot simply be deleted — which is precisely why the `StrLit` sub-case needs an explicit guard. AGENTS.md: "If you are not sure about whether some invariants you need do hold, assert them using softAssert or assert", and "The worst possible outcome would be to introduce changes that might lead to silent miscompilation." Here the failure mode of a broken invariant is exactly silent no-match, with no diagnostic.

**Scenario.**

The invariant is one very natural optimization away from being broken. LPTK's own review comment complains that the automaton table is huge and re-parsed at the call site; the obvious response is to keep cheap `StrLit` head dispatch when the string-shaped patterns of *some* labels are plain literals, e.g. relaxing the filter in `buildMultiMatcherBody` to

```scala
case lit: StrLit if !expandedPatterns.exists((_, p) => p.heads.contains(lit) && containsStringNode(p)) => true
```

With any such relaxation, a matcher over labels `{ A = "ab", B = "a" ~ "b" }` keeps head `StrLit("ab")`; for input `"ab"` the `"ab"` branch is entered first, `specialize(StrLit("ab"))` maps `B`'s `Concat` to `Never`, and the record reports `p_B = MatchFailure` even though `"a" ~ "b"` matches `"ab"`. No error, no warning — the wrong answer.

Even without any refactor, the same happens the day a class that primitive strings satisfy is added (e.g. a `Char` builtin lowered to a `typeof`/`length` test, or making `Object` match primitives): that head is not filtered, its branch precedes the appended `Str` branch, and every `Concat` label under it becomes `Never`.

**Suggested fix.**

Make the invariant explicit and loud. In `specialize(lit)` split the case:

```scala
case _: (Literal | ClassLike) => Never
case p: (Concat | CharClass) =>
  softAssert(!lit.isInstanceOf[StrLit],
    "string-shaped patterns must be absorbed into the `Str` head before literal specialization")
  Never
```

(or `lastWords` if the invariant is meant to be hard). Correspondingly, tighten `buildMultiMatcherBody`'s head filter so the property it guarantees is stated where it is established — e.g. filter on "every head a string value can satisfy" via a single named predicate shared with the assertion, rather than an inline `case _: StrLit` / `is strSymbol` match that a future builtin will silently fall through. Documenting the invariant in a scaladoc, as done now, is not sufficient under AGENTS.md when the failure mode is silent miscompilation.

# MINOR (16)

## M1. Non-recursive definitions and cross-SCC components are re-inlined at every reference with no sharing, giving exponential NFA size

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:498` — *perf*, refuted 0/3

**What's wrong.**

`buildReference` inlines `bodies(inst)` afresh at every reference (line 498), and `buildSccCopy` materializes a *complete new copy of the whole SCC* at every external reference (line 517). Nothing is memoized on `(inst, cont, needValue, exitOps)`, so the number of states built is proportional to the number of *paths* through the reference DAG, not to its size.

`reduceStates` can merge the resulting duplicates afterwards (`mergeIdentical` keys on the ordered edge list, so isomorphic bottom-up copies do collapse), but only after `build` has already allocated all of them, and `reduceStates` itself is not cheap: the `while changed` loop re-runs `dropDeadEdges`/`contractTrivial`/`mergeIdentical` over the whole `states` buffer, and `encodeOps` resolves pool entries with a linear `pool.indexOf`. So the peak cost is exponential in the nesting depth even when the reduced result is small.

This compounds with the two other size multipliers already visible in the goldens: `reverseDeterminize` is a subset construction (worst case exponential in the reduced state count), and the viability section is a dense `revStates × stateCount` bit matrix embedded as a JS string literal at every call site — `EmailAddress.mls` already emits a ~6 KB literal for a two-instantiation grammar, which is what prompted the reviewer's comment about hoisting the table into a top-level field.

**Scenario.**

```
pattern A0 = "a" | "b"
pattern A1 = A0 ~ A0
pattern A2 = A1 ~ A1
pattern A3 = A2 ~ A2
...
pattern A16 = A15 ~ A15

"aaaa" is (A16 ~ "")
```
`build` inlines `A16` → two copies of `A15` → … → 2^16 = 65536 copies of `A0`'s fragment (~2·10^5 states) before any reduction runs, for a language that needs 17 states. Each additional level doubles compile time and memory; a dozen more levels makes the compiler hang or OOM on a program the user would consider small.

**Suggested fix.**

Memoize inlining: key a cache on `(inst, cont, needValue, exitOps, sccContext)` and return the previously built entry state when a reference repeats with the same continuation and pending operations (the fragment is a pure function of exactly those inputs). The same key works for `buildSccCopy`, which would then build at most one copy of an SCC per distinct `(cont, pure)`. Independently, consider hoisting the encoded table to a top-level `val` per region (as the reviewer asked) so the size cost is paid once per program rather than once per call site, and replace `encodeOps`'s `pool.indexOf` with a `Map[Ls[Int], Int]`.

## M2. `classRepresentative(bounds, 0)` is not a member of class 0 whenever a range starts at U+0000, producing a permanently dead transition column

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:702` — *invariant*, refuted 0/3

**What's wrong.**

`computeBounds` unconditionally does `points += lo`. `AnyChar = (0, MaxUnit)` is used for the wildcard (line 383), for `Str` in string position (line 397), and for the trailing lazy star of every `Mode.Prefix` compilation (line 915). So `0 in bounds` for essentially every region that mentions `_`, `Str`, or that is compiled in prefix mode.

When `bounds(0) == 0`, the JS `classOf` (Runtime.mls:250) returns `count of bounds <= unit`, which is >= 1 for every code unit (all units are >= 0). Class 0 is therefore empty and never selected at run time. Yet `classRepresentative(bounds, 0)` returns 0, which is a member of class *1*, not class 0 — its documented contract ("A representative code unit for each class", line 700) silently does not hold.

The consequence today is waste, not miscompilation: `chrPre(0)` is populated identically to `chrPre(1)`, so column 0 of every reverse row duplicates column 1 and is never read. But there is no `assert`/`softAssert` recording the invariant, so any future use of `classRepresentative` that actually needs a member of the class (emitting a witness string, testing class emptiness, minimizing the alphabet) will be silently wrong — exactly the failure mode AGENTS.md singles out ("If you are not sure about whether some invariants you need do hold, assert them").

**Scenario.**

```
pattern Bracketed = ("[" ~ (Str as s) ~ "]") => s
if "[abc]" is Bracketed as s then s
```
`Str` contributes range (0, 65535) -> `points += 0` (and no `hi+1` since `hi == MaxUnit`); `"["` contributes 91, 92; `"]"` contributes 93, 94. So `bounds = [0, 91, 92, 93, 94]` and `classCount = 6`. At run time `classOf` never returns 0 for any input character, so 1/6 of every row of the encoded `revTransitions` section is dead payload, and `classRepresentative(bounds, 0) = 0` reports a code unit that `classOf` assigns to class 1. The same happens for every `unapplyStringPrefix` automaton, because `Mode.Prefix` always appends `addChr(star, AnyChar, star)`.

**Suggested fix.**

In `computeBounds`, only record `lo` as a boundary when it is greater than 0: `if lo > 0 then points += lo`. Class 0 then genuinely denotes `[0, bounds(0))` and contains its representative 0; the partition is unchanged (a range starting at 0 covers the whole low class anyway), and one class is saved on every `Str`/wildcard/prefix region. Additionally add `softAssert(classId == 0 || bounds(classId - 1) < bounds.lift(classId).getOrElse(MaxUnit + 1), ...)` — or simply assert `bounds.headOption.forall(_ > 0)` — so the representative-membership invariant is checked rather than assumed.

## M3. `classOf` is a linear scan over all class boundaries executed once per input character, and the alphabet partition is never minimized

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:250` — *perf*, refuted 0/3

**What's wrong.**

`classOf(prog, unit)` walks `bounds` from index 0 until `bounds[i] > unit`, i.e. O(classCount) per lookup, and each step is an `Array.prototype.at()` call in the generated JS (Runtime.mjs:762-779). It is invoked once per input character in `matchWhole`'s reverse scan (line 277) and twice per character in `parseRun` (reverse scan at line 294, plus the forward walk's `unitInRanges`). Matching an M-character string therefore costs O(M * classCount) just to classify characters — for a PR whose stated purpose is optimized compilation, this is the hot loop.

This is aggravated by `computeBounds` performing no alphabet-class *minimization*: it emits one boundary pair per distinct range endpoint, without merging classes whose transition columns are identical. Every additional literal character in a pattern widens the alphabet, and thus both the per-character scan and the width of every reverse-transition row (`revStates * classCount` integers in the encoded table).

**Scenario.**

```
pattern Hex = (("0".."9") | ("a".."f") | ("A".."F")) ~ Str
```
`computeBounds` yields `{0, 48, 58, 65, 71, 97, 103}` -> 7 classes, of which classes {[48,58), [65,71), [97,103)} are behaviourally identical (all three are "hex digit") and could be one class; class 0 is dead (see the U+0000 finding). Classifying the character 'x' (120) scans all 6 boundaries.

Scale this up to a realistic lexer-style pattern such as a keyword alternation `"if" | "then" | "else" | "while" | "fun" | "let" | ...`: each distinct letter contributes two boundaries, so classCount reaches several dozen. Matching a 1000-character string then performs ~50 000 `bounds.at(i)` calls per scan, and the `revTransitions` section is 50x wider than the number of behaviourally distinct classes requires.

**Suggested fix.**

Two independent fixes. (a) In `classOf`, replace the linear scan with a binary search over `bounds`, or — since the alphabet is only 65536 units wide and the program is decoded once and cached — build a `Uint8Array(65536)` class-lookup table in `decodeProgram` and index it directly (64 KB per program, O(1) per character). (b) In `computeBounds`, minimize the partition: after collecting the raw boundaries, group classes by the set of `Edge.Chr` ranges that contain their representative and keep one boundary per distinct group. This shrinks `classCount`, the width of `revTransitions`, and the per-character cost simultaneously.

## M4. Blank-line whitespace churn in `module Str`, unrelated to the change

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:114` — *standards*, refuted 0/3

**What's wrong.**

The PR rewrites four pre-existing blank lines in the untouched `module Str` block (Runtime.mls lines 114, 117, 123, 126) from two-space-indented blank lines to fully empty lines. Two more of the same appear in `Pattern.scala` (six whitespace-only removed lines across the PR, per `git diff | grep -c '^-  *$'`). AGENTS.md is explicit on both counts: "Never strip indentation whitespace" and "When working on a PR, make sure to check the diff of the whole PR ... to ensure that no needless empty-line changes are included. If you find any, please remove them." These lines are in a module the PR otherwise does not modify, so they are pure diff noise.

**Scenario.**

`git diff hkust-taco/hkmc2...HEAD -- hkmc2/shared/src/test/mlscript-compile/Runtime.mls | head -30` shows hunks of the form `-  ` / `+` immediately after `module Str with` and between each `@mayNotRaiseEffects` member, none of which is otherwise touched by the PR.

**Suggested fix.**

Restore the original two-space blank lines at Runtime.mls:114, 117, 123, 126 and the equivalent lines in Pattern.scala, so the diff contains only the new `module StrPat`.

## M5. Each region inlines the full automaton table as a fresh string literal and builds its own `Instantiator`/`StringCompiler`, duplicating both code and transform closures

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/SplitCompiler.scala:1240` — *design*, refuted 0/3

**What's wrong.**

This is the generalisation of the reviewer's comment on `ups/regex/EmailAddress.mls`. `makeStringRegionSplit` (line 1240) and `makeStringPrefixAutomatonSplit` (line 1278) each construct `new Instantiator` + `new StringCompiler` and then embed `str(compiled.table)` — a multi-kilobyte literal for realistic patterns — directly at the call site. Consequences:

1. Code size: N syntactic uses of the same pattern in a sequence emit N copies of the same table. The runtime `programs`/`matchers` `Map` caches the *decoded* program, so correctness is fine, but the emitted JS grows linearly and each call hashes a multi-KB key.
2. Symbol duplication: `StringCompiler`'s `Extract` case interns transform closures only *per region*, and its own TODO says "two regions in one block that reach the same definition's transform still produce two closures sharing parameter symbols", which "trips the refresher when a simplifier pass duplicates a subtree containing both". `compilePattern(pd)` guarantees this situation for every non-parametric string-pattern definition containing a transform: `unapply` builds one region (line 1462 -> `makeStringRegionSplit`) and `unapplyStringPrefix` builds a second one over the *same* body (line 1495), producing two `Term.Lam`s whose parameters are the very same `correspondence(symbol)` `VarSymbol`s, in the same generated pattern object.

**Scenario.**

`ups/UpsBugsBacklog.mls`'s `pattern Input = ((Char.Whitespace ~ (Input as inp)) => inp) | ((c ~ (Input as inp)) => [c, ..inp]) | ("" => [])` already hits case 2: two independent `StringCompiler` instances each emit `Term.Lam(PlainParamList([Param(inpParam)]), ...)` with the identical `inpParam` symbol. And for `ups/regex/EmailAddress.mls`'s `CommaSep(Email)`, adding a second use site duplicates the ~10 KB table literal verbatim in the output.

**Suggested fix.**

Hoist the table (and the action closures) into a top-level `val` of the enclosing file/module — the reviewer's suggestion — and reference it from every site, keyed by the compiled region. That fixes the code-size blowup and, by compiling each definition's transforms once next to `unapply`, also removes the shared-parameter-symbol hazard the `Extract` TODO describes.

## M6. PR strips indentation whitespace from blank lines, which AGENTS.md explicitly forbids

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala:263` — *standards*, refuted 0/3

**What's wrong.**

AGENTS.md: "Never strip indentation whitespace. Empty lines in this project are usually significant. ... When working on a PR, make sure to check the diff of the whole PR ... to ensure that no needless empty-line changes are included in the PR. If you find any, please remove them."

The diff against `hkust-taco/hkmc2` contains 7 hunks whose only content is replacing an indentation-only blank line (`"  "`) with an empty line, in files whose surrounding code is otherwise untouched.

**Scenario.**

`git diff hkust-taco/hkmc2...HEAD | grep -c '^-  $'` reports 7. Per file: `ups/Pattern.scala` 2 (around the `specialize(lit)` / `specialize(symbol)` doc comments, lines ~263 and ~276 of the new file), `ups/Compiler.scala` 1 (before `import Pattern.*`), `test/mlscript-compile/Runtime.mls` 4 (inside `module Str with`, which the PR otherwise does not modify).

**Suggested fix.**

Restore the original indentation-only blank lines in `ups/Pattern.scala`, `ups/Compiler.scala` and `Runtime.mls`; the `Runtime.mls` hunks in `module Str with` are pure churn and should be dropped from the PR entirely (they also force a regeneration diff in `Runtime.mjs`).

## M7. PR strips trailing whitespace from three pre-existing blank lines, which AGENTS.md explicitly forbids

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala:459` — *standards*, refuted 0/3

**What's wrong.**

AGENTS.md, "Editing Style": "Never strip indentation whitespace." and, under Workflow: "When working on a PR, make sure to check the diff of the whole PR (including all commits) to ensure that no needless empty-line changes are included in the PR. If you find any, please remove them."

Three hunks in this diff consist solely of turning a `"  "` line into `""`, unrelated to the change being made:
- `Pattern.scala:459` (blank line after `specialize(lit)`)
- `Pattern.scala:474` (blank line after `specialize(symbol)`)
- `Compiler.scala:263` (blank line after `multiMatcherBranch`'s closing `Blk(...)`)

**Scenario.**

`git diff hkust-taco/hkmc2...HEAD -- hkmc2/shared/src/main/scala/ | grep -n '^[-+][[:space:]]*$'` reports the removals at diff lines 138/396/412, each of the form `-  ` immediately followed by `+`. Reviewing the PR shows these as three spurious hunks that carry no semantic change and add noise to `git blame`.

**Suggested fix.**

Restore the two spaces on those three lines (`Pattern.scala:459`, `Pattern.scala:474`, `Compiler.scala:263`) so the hunks disappear from the diff. Note that the surrounding indentation-significant Scala 3 style makes such lines meaningful editing anchors in this codebase, which is why AGENTS.md calls them out.

## M8. Indentation-only lines stripped in `Pattern.scala`, contrary to AGENTS.md

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala:459` — *standards*, refuted 0/3

**What's wrong.**

AGENTS.md: "Never strip indentation whitespace" and "make sure to check the diff of the whole PR ... to ensure that no needless empty-line changes are included". The diff for `Pattern.scala` contains two hunks of the form `-  ` / `+` (the separator lines after `specialize(lit)` and after `specialize(symbol)`), which convert the project's `  `-indented blank separators into fully empty lines. Every other blank separator in the file (lines 33, 41, 49, 67, 124, 138, 180, 248, 272, 279, ...) still carries the two-space indentation, so the change is both a standards violation and gratuitous diff noise in an otherwise reviewable file.

**Scenario.**

`git diff hkust-taco/hkmc2...HEAD -- hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala | grep -nE '^[-+][[:space:]]*$'` reports `-  ` / `+` pairs at diff lines 120/121 and 136/137, corresponding to current-tree lines 459 and 474, neither of which is adjacent to any semantic change.

**Suggested fix.**

Restore the two-space indentation on the blank lines at Pattern.scala:459 and :474 so those two hunks disappear from the PR diff.

## M9. Whitespace-only churn strips indented blank lines that AGENTS.md forbids touching

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:114` — *standards*, refuted 0/3

**What's wrong.**

AGENTS.md, "Editing Style": "Never strip indentation whitespace." and "When working on a PR, make sure to check the diff of the whole PR (including all commits) to ensure that no needless empty-line changes are included in the PR. If you find any, please remove them."

The diff against `hkust-taco/hkmc2` contains exactly seven hunks that replace a pre-existing two-space-indented blank line (`-  `) with an empty line (`+`), touching nothing else. They are all pure churn and unrelated to the feature. In `Runtime.mls` they also break the local convention: the neighbouring `module Tuple with` block still uses the indented form, so `module Str` is now the odd one out.

Exact locations in the current working tree:
  - hkmc2/shared/src/test/mlscript-compile/Runtime.mls:114, 117, 123, 126  (inside `module Str with`)
  - hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala:459, 474
  - hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Compiler.scala:263

On the other AGENTS.md checklist items I found no violations: no `asInstanceOf` is introduced anywhere in the diff; no `end` markers are removed; no default arguments are added to core logic (`buildSccCopy(..., pure: Bool)` is called with a named argument, not a default); the new `var`s are all either method-local or instance fields of `StringCompiler` (`failed`, `anyOps`), not global mutable state on symbol classes; and `softAssert`/`lastWords` are used reasonably densely in the NFA builder (StringCompiler.scala:336, 368, 374, 381, 395, 424, 430, 475, 480, 495, 502-504).

**Scenario.**

`git diff hkust-taco/hkmc2...HEAD -U0 -- hkmc2/shared/src/test/mlscript-compile/Runtime.mls | grep -E '^(-[[:space:]]+|\+)$'` shows four `-  ` / `+` pairs at Runtime.mls:114/117/123/126, i.e. lines changed for no reason inside `module Str with`, a module this PR does not otherwise modify. Same command on Pattern.scala and Compiler.scala shows the remaining three.

**Suggested fix.**

Restore the two trailing spaces on those seven lines (`git checkout -p` the relevant hunks, or re-add `  ` manually at Runtime.mls:114,117,123,126; Pattern.scala:459,474; Compiler.scala:263), and verify with the grep above that the PR diff contains no remaining `^-[[:space:]]+$` lines.

## M10. `Compiled.resultPrefixSize` is dead code while the result-array layout it encodes is hardcoded at three call sites

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:126` — *design*, refuted 0/3

**What's wrong.**

`Compiled.resultPrefixSize(mode)` (StringCompiler.scala:126-128) is documented as "Elements of the array returned by the parse entry points, before the binding slots" and returns 1 for `Whole` / 2 for `Prefix`. It is never called anywhere in the codebase (`grep -rn resultPrefixSize hkmc2/shared/src/main` matches only its own definition). Instead, the layout knowledge is open-coded three times:

  - SplitCompiler.scala:1266  `callTupleGet(resultSymbol, 1 + slot, "string binding")`  (Whole)
  - SplitCompiler.scala:1290-1291  `callTupleGet(..., 0)` / `callTupleGet(..., 1)`  (Prefix)
  - Compiler.scala:301  `callTupleGet(resultSymbol, 1 + slot, "string binding")`  (Whole)

and a fourth time on the runtime side in `parseRun` (Runtime.mls:412-421), which pushes `output`, optionally `remaining`, then the slots. Five places must agree on one wire format, and the one abstraction written to centralize it is inert. This is exactly the maintainability failure AGENTS.md's DRY section targets: "the logic for handling cases that ought to be similar should be centralized".

**Scenario.**

If `parseRun` is ever extended to return one more leading element (e.g. the match end offset, a natural next step for supporting non-anchored search), the author updates Runtime.mls and, plausibly, the `Prefix` site — but the two `1 + slot` sites are textually identical to each other and easy to miss, and there is no assertion tying them to the mode. The result is that binding destructuring reads the wrong array element: `if s is ("[" ~ (Str as x) ~ "]")` binds the *output* string to `x` instead of the captured slice, with no error anywhere. Nothing in the type system or the tests would catch it, because both are `Str`.

**Suggested fix.**

Use `resultPrefixSize` at all three call sites (`callTupleGet(result, compiled.resultPrefixSize(mode) + slot, ...)`, `callTupleGet(result, 0/1, ...)` derived from it), and add a `softAssert` in `Compiled` relating `visibleSlots.size` to the array arity the engine will return. Better: give `Compiled` a small API (`def outputIndex(mode)`, `def remainingIndex`, `def slotIndex(mode, slot)`) and delete the raw integer arithmetic from both `SplitCompiler` and `Compiler`, so the shared wire format has exactly one owner on the compiler side.

## M11. `classOf` does a linear scan over class boundaries for every input character in the allocation-free hot loop

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:250` — *perf*, refuted 0/3

**What's wrong.**

`classOf` (Runtime.mls:250-255) walks `prog.bounds` linearly until it finds the first boundary greater than the code unit, and returns the index. It is called once per input character in `matchWhole` (Runtime.mls:277) and once per character in `parseRun`'s backward scan (Runtime.mls:295), i.e. it sits inside the only two loops the design advertises as linear-time and allocation-free.

`bounds` has `classCount - 1` entries, and `classCount` grows with the number of distinct character ranges in the pattern: the `CommaSep(Email)` automaton has 17 classes (header `130,1,0,3,17,47,0`, EmailAddress.mls:111). So `matchWhole` is `O(n * C)`, not `O(n)`. The generated code (Runtime.mjs:761-779) confirms there is no early exit or memoization, and every iteration goes through `bounds.at(i)` on a frozen array. A lexer-style pattern alternating over many keywords or Unicode blocks would push `C` into the dozens or hundreds, making the recognition path several times slower than the naive `String.prototype.startsWith` chain it replaces.

**Scenario.**

`"john.doe@guardian.co.uk" is Email` (a 23-character input, 17 classes) performs up to 23 * 17 = 391 comparisons plus 23 non-inlined static calls just to classify characters, on top of the 23 table lookups that are the actual work. Scale that to a pattern with 100 character classes matching a 1 KB string and classification dominates the scan by two orders of magnitude, while the doc comment on the module presents the backward scan as "a single right-to-left scan ... with no allocation", implying constant work per character.

**Suggested fix.**

Precompute a direct lookup table at decode time: for the (overwhelmingly common) case where all boundaries are below 128 or 256, build a `Uint8Array` of that size mapping code unit -> class id and fall back to binary search above it; store it on the decoded `Program`/`Matcher`. Failing that, at minimum replace the linear scan with a binary search over `bounds`. Document the chosen representation, since the decode cost is amortized by the `programs` cache and so a bigger table is essentially free.

## M12. Final pruning silently depends on the unasserted invariant that `accept` has no outgoing edges; otherwise dropped targets are renumbered to state 0

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala:664` — *design*, refuted 1/3

**What's wrong.**

`keep(accept) = true` is executed *after* the reachability worklist, deliberately keeping an accept state that is unreachable from `entry` (the never-matching region). `renumber` and `compacted` are then both built by a single increasing scan over `keep`, so `compacted(renumber(s)) == states(s)` holds and the indices are consistent — that part is correct, including when accept is unreachable.

What is *not* checked is that the kept set is closed under edges. It is closed only because (a) the reachable-from-entry set is closed by construction and (b) `accept` — the one state added outside the worklist — happens never to have outgoing edges: it is created by `val accept = newState()` in `compile` and only ever passed as a `cont`, and neither `contractTrivial` (guarded by `source != accept`) nor `mergeIdentical` (whose key includes `state == accept`) can give it any. Nothing in the code states or asserts this.

`renumber` is `new Array[Int](states.size)`, i.e. zero-initialised, and slots for dropped states are never assigned. So the moment `accept` acquires an outgoing edge and is unreachable, `retargetAll(edges)(renumber(_))` rewrites that edge's target to 0 — a perfectly well-formed automaton pointing at the wrong state. That is exactly the silent-miscompilation failure mode AGENTS.md asks to guard against with `softAssert`.

**Scenario.**

Any future change that gives the accept state an outgoing edge — e.g. reworking `Mode.Prefix` so the trailing lazy star loops on `accept` instead of on a separate `star` state, or adding an end-anchor/lookahead construct — combined with a region whose `entry` cannot reach `accept` (e.g. `pattern P = Never ~ "a"`, or any pattern whose string fragment is `And(Nil)`, which `build` compiles to an edge-less state). The pruning keeps `accept`, its out-edge targets are dropped, `renumber(target)` returns the default 0, and the emitted table contains an edge from `accept` to the state that happens to be renumbered 0 — no error, no assertion, just a wrong automaton.

**Suggested fix.**

Either (a) seed the worklist with `accept` as well (`keep(accept) = true; val worklist = Buffer(entry, accept)`), which makes the kept set closed by construction and removes the hidden dependency entirely, or (b) keep the current shape and add `softAssert(states(accept).isEmpty, "the accept state must have no outgoing edges")` immediately before `keep(accept) = true`, plus a comment recording why the kept set is edge-closed.

## M13. The engine immediately un-packs the deliberately bit-packed viability matrix into a boxed JS boolean array, and allocates per input character

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls:176` — *perf*, refuted 1/3

**What's wrong.**

`StringCompiler.packBits` goes to real trouble to store the viability matrix at 6 bits per source character (`packAlphabet`, Base64). `decodeBits` then expands it to one JS array element per bit — a `PACKED_ELEMENTS` array of `true`/`false` oddball pointers, 4-8 bytes each, i.e. a 32-64x memory expansion over the packed form, defeating the point of the packing. `viable` then indexes it with `.at()` (Runtime.mjs:786), which is measurably slower than `[]`. The matrix is O(revStates x nfaStates) and `revStates` is worst-case exponential in the NFA size, so this multiplier applies exactly where it hurts.

The forward walk is linear in |input| as advertised, but with a large constant, and it allocates per position: `pushEdges` (line 404) allocates a fresh two-element array `[state, edges.[i]]` for *every* edge of *every* state visited at *every* position, `execChain` allocates a `chain` array per commit, and — a lowering artifact worth knowing about — the generated code re-creates the `runOps` closure at each of the two `execChain` call sites, i.e. once per committed transition, even though the source binds it once outside the loop (Runtime.mjs:917 and 938: `runOps = lambda$1(prog, frames, bindings, execValueOp, runFrameOps)`).

On the reviewer's separate concern about `programs.get(table)` re-hashing a multi-kilobyte string per call: that is a non-issue at run time. The table is a JS source literal, so V8 internalises it and caches its hash in the string header; measured cost of the `Map.get` on the 5253-char EmailAddress table is 6.4 ns/call, against ~10 us for a single 13-character parse. (It would be ~131 ns/call if the table were ever built dynamically rather than being a literal.) The real cost of the inlining scheme is source size and duplication across call sites, not the lookup.

**Scenario.**

Measured against the shipped engine with the real EmailAddress `CommaSep(Email)` table (130 NFA states, 47 reverse states, 17 classes), parsing comma-separated address lists:
  k=200  len=3889  55 ns/char
  k=800  len=15889 ~1.0 us/char
  k=3200 len=66089 55 ms  => ~0.83 us/char (~1.2 M chars/s)
The viability matrix for this small automaton is 47*130 = 6110 bits, i.e. 1019 base64 characters in the source, decoded into a 6110-element JS boolean array (~48 KB resident vs. 764 bytes packed).

**Suggested fix.**

Decode the viability section into a `Uint8Array` bitset and make `viable` do `(bits[i >> 3] >> (i & 7)) & 1`; likewise store `revTrans` and the NFA section in `Int32Array`s. Replace the `[state, edge]` pairs in `pushEdges` with two parallel plain-number stacks (or push `state` and the edge object as two entries). If the lowering keeps sinking `runOps` into the loop, hoist it by making it a module-level `fun` taking its captures as parameters.

## M14. `UpsBugsBacklog.mls`: the now-passing case is un-`:expect`ed, its golden `[a b c]` is the output of a known array-printing bug, and it is only accidentally correct at recursion depth 1

`hkmc2/shared/src/test/mlscript/ups/UpsBugsBacklog.mls:17` — *test-gap*, refuted 1/3

**What's wrong.**

LPTK asked for this case to be moved out of the backlog file, which is correct, but the block as written is not a good test wherever it lands.

(a) It has no `:expect`, so the golden records whatever the implementation produced.
(b) The golden `= [a b c]` is not the rendering of `["a b c"]`. `Rendering.renderValue` sends strings through `JSON.stringify`, so an array of one string renders `["a b c"]`. `[a b c]` is the output of the known array-literal-with-spread printing bug recorded in `hkmc2/shared/src/test/mlscript/backlog/ToTriage.mls:9-14` (`[..[], "a"]` prints `[a]`). So the golden depends on an unrelated open bug and will silently churn when that bug is fixed.
(c) The value is right only because the greedy wildcard makes the recursion bottom out after one activation. Had `Input` tokenized as the author's comment implies it was meant to, the outer transform's `c`/`inp` bindings would be clobbered by the inner activations — the defect reported separately against `Runtime.mls:455`.

**Scenario.**

`if "a b c" is Input as chars then chars` currently records `//| = [a b c]`. If the `[..[], x]` printing bug in `backlog/ToTriage.mls` is fixed, this golden changes to `//| = ["a b c"]` with no change to the string-pattern compiler, and a reviewer looking at the diff has no way to tell that the semantics did not move. Conversely, if the greedy-wildcard rule is ever changed so that `c` matches one character (the pattern's evident intent), the result becomes a three-element array whose *first* element is wrong, and there is no `:expect` to catch it.

**Suggested fix.**

Move the block to `hkmc2/shared/src/test/mlscript/ups/regex/CompiledSemantics.mls`, next to the existing `LastB` wildcard-greediness block (it belongs with the documented rule it illustrates), add the `Char.mls` import there, and assert the observable value in a form that does not go through the spread-printing bug:

```
// A wildcard in string position is greedy, so this `Input` does not tokenize:
// `c` takes the whole string because `Input` accepts the empty remainder.
// (This used to overflow the stack in the backtracking translation.)

import "../../../mlscript-compile/Char.mls"

pattern Input =
  ((Char.Whitespace ~ (Input as inp)) => inp) | ((c ~ (Input as inp)) => [c, ..inp]) | ("" => [])

:expect 1
if "a b c" is Input as chars then chars.length

:expect "a b c"
if "a b c" is Input as chars then chars.[0]
```

The `:todo`s at UpsBugsBacklog.mls:27/33 and the `:fixme` at line 49 are still accurate and should stay.

## M15. Seven existing test sites were converted to `@compile` rather than duplicated, dropping coverage of the un-annotated path (which is the one that miscompiles)

`hkmc2/shared/src/test/mlscript/ups/regex/Separation.mls:15` — *test-gap*, refuted 1/3

**What's wrong.**

The PR rewrites `"hello" is Lines("hello")` -> `... is @compile Lines("hello")` (Separation.mls:15, 19, 23, 37, 41) and `_ is Email` -> `_ is @compile Email` (EmailAddress.mls:82), plus `CommaSep(Email)` -> `@compile CommaSep(Email)` (EmailAddress.mls:95). These were *conversions*, not additions, so the plain (un-annotated) route through `SplitCompiler` lost its only coverage for parametric string patterns and for `Email`.

That matters because the two routes are genuinely different code (`Compiler.multiMatcherStringBranch` vs `SplitCompiler.makeStringRegionSplit` vs `P.unapply`), and — per the critical finding against `Runtime.mls:455` — they do not agree. Converting tests onto `@compile` is exactly the direction that hides the disagreement: `@compile` is one of the two routes that is correct.

**Scenario.**

I re-ran the un-annotated forms in a scratch difftest: `"hello" is Lines("hello")` -> `true` and `"123\n456\n789" is Lines(Integer)` -> `true`, i.e. the conversions were not needed to make the file pass. Meanwhile `"123" is R2` (un-annotated, non-parametric, recursive, with a transform) is miscompiled — a bug that only the un-annotated route exhibits and that no remaining test in `ups/regex/` can catch, because every recursive-with-transform test in the directory is now either parametric or `@compile`d.

**Suggested fix.**

Restore the original lines and add the `@compile` variants alongside them, so both routes stay covered. In `Separation.mls`:

```
:expect true
"hello" is Lines("hello")

:expect true
"hello" is @compile Lines("hello")
```

and likewise for lines 19, 23, 37 and 41, and for `EmailAddress.mls:82` and `:95`. As a rule for this feature, any test of a pattern that has both a transform and recursion should appear three times: plain, `@compile`, and (where applicable) parametric.

## M16. `Identifier.mls`: the `isWord` change removes the only documentation of the unsupported-pattern fallback, leaves two comments stale, and the added `isManyDigits` block asserts nothing negative

`hkmc2/shared/src/test/mlscript/ups/regex/Identifier.mls:17` — *test-gap*, refuted 1/3

**What's wrong.**

Three separate problems in this file after the PR:

(1) Line 17 still reads "Currently, we expand range patterns into disjunction." That is now false: `Instantiator` emits `CharClass` and keeps ranges symbolic. The comment sits directly above `isBinary`, so a reader will mis-model what `@compile Binary` produces.

(2) Lines 110-111 ("The use of `Map` makes the expanded disjunction out of order. I wonder if we should use a `SeqMap` for literals.") no longer applies to `isLetter`: `Letter = Lower | Upper` now contains `CharClass` nodes, so `StringCompiler.containsStringNode` is true, `absorbStrings` fires in `Compiler.buildMultiMatcherBody`, and `isLetter` is compiled to an automaton rather than a disjunction of literal heads. `isBinary`/`isDigit` (pure `StrLit` alternations, no `CharClass`) still take the old head-specialization path. So the file's three `@compile` probes now exercise two different mechanisms, and the comments describe only the old one.

(3) The removed comment "// Unsupported patterns are equivalent to `Never`." documented a real, still-live policy (it is what `emptyMatchResult("rejected string pattern")` implements after a `checkTailPositions` failure), and nothing replaces it. The added `isManyDigits("5678") //| = true` block has no `:expect` and no negative case, so it cannot distinguish "the automaton works" from "everything matches".

**Scenario.**

A reader of `Identifier.mls` today concludes from line 17 that `@compile Binary` expands to a disjunction and from line 110 that `@compile Letter` does the same. In fact `isLetter` goes through `multiMatcherStringBranch` and `Runtime.StrPat.matchWhole` with a `CharClass`-derived table, while `isBinary` does not. If the `absorbStrings` predicate ever changes (e.g. `containsStringNode` stops reporting `CharClass`), `isLetter` silently switches back with no test noticing, because `isLetter of "a"` / `isLetter of "0"` pass either way and neither carries `:expect`.

**Suggested fix.**

Update line 17 to "Character ranges are kept symbolic as character classes; plain literal alternations are still expanded into a disjunction of heads." Update the comment at 110-111 to note that `Letter` contains a character class and is therefore absorbed into the `Str` head. Restore the `Never` policy note near a test that still demonstrates it (`ups/regex/NonRegular.mls` is the natural home). Strengthen the new block:

```
fun isManyDigits(str) = str is @compile ManyDigits

:expect true
isManyDigits("5678")

:expect false
isManyDigits("56a8")

:expect false
isManyDigits("")
```


# Raised but refuted

These were claimed by a reviewer and knocked down by at least two of the three verifiers. Recorded so they are not raised again.

## The decoder validates nothing about the encoded table, and `parseRun`'s entry viability test uses `=== false` while every other test uses `=== true`

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls` — refuted 2/3

The claimant read the code correctly but the consequence does not follow and the path is unreachable.

Verified as described: `viable` (Runtime.mls:258) is an unchecked array index; Runtime.mjs:862 compiles `is false` to `=== false` while :916/:953 compile the truthy guards to `=== true`; `header[5]` (revStateCount) is emitted by `encode` (StringCompiler.scala:865-866) and never read by `decodeProgram` (it reads header[0..4] and header[6]); `Compiled.resultPrefixSize` (StringCompiler.scala:126) has no callers repo-wide.

Why it is refuted:

(1) Out-of-range is not reachable. `decodeBits` pads bits to a multiple of 6, so length >= revSets.size * stateCount. Every revState passed to `viable` originates from `seedRev` or a `revTrans` cell, all of which are ids minted by `idOf` and therefore < revSets.size; `reverseDeterminize` pre-grows rows (`while transitions.size < (id+1)*classes do transitions += 0`) and `LinkedHashMap.keysIterator` yields subsets in id order, so no viability row can be missing or misordered. Every `state` argument is `prog.start` or an edge target, all < stateCount. `revArr` holds exactly n+1 entries and is indexed at n, at n-(pos+1) under a `pos < n` guard, and at n-pos with 0 <= pos <= n. So `viable` always returns a genuine boolean, on which `=== false` and `!== true` are extensionally identical. The claim's own scenario admits this: it requires first injecting a bug into `packBits`/`encode` (e.g. `revSets.init.iterator`). That is a hypothetical mutation of the source, not an input, and the review brief forbids findings not tied to a concrete failing scenario.

(2) The invariant IS asserted, deliberately. Runtime.mls:420 throws `Error("StrPat: no viable transition (this is a compiler bug)")` under the comment "The upfront viability check guarantees a path to acceptance, and the search only moves to viable states, so this cannot happen." That is the documented assertion AGENTS.md calls for, placed exactly where the invariant can break. The claim's scenario terminates in that throw, i.e. the guard doing its job loudly — the opposite of silent miscompilation. `softAssert`/`assert` are Scala facilities; Runtime.mls is the emitted JS engine where a throw is the equivalent.

(3) `sextet`'s bare `else 63` can only misdecode a table that this same compiler did not emit; the tables are compiler-generated string literals in the generated output. No untrusted-input path exists.

The claimed severity ("turns a clean no-match into an uncatchable runtime error after transforms have run") therefore describes behavior of a hypothetically-broken encoder, not of this PR. || The code descriptions are accurate (viable is an unchecked .at(); line 297 compiles to `=== false` per Runtime.mjs:861-863 while lines 428/444 compile to `=== true` per Runtime.mjs:915/952; decodeProgram does skip header[5]=revStateCount emitted by encode at StringCompiler.scala:868; resultPrefixSize at StringCompiler.scala:126 has no callers). However, under the reachability lens the finding fails: with the encoder as written, `viable` can never return undefined, so the `=== false` vs `=== true` asymmetry is behaviorally inert. (1) `viability` is packed as revSets.size * stateCount bits and decodeBits rounds UP to a multiple of 6, so the decoded array is never short. (2) Every reverse-state index originates from prog.seedRev stepped through revTrans, and in reverseDeterminize every value written to `transitions` comes from idOf(next), which both registers the subset in `ids` and enqueues it, so every referenced id is < revSets.size and gets its own row; the FIFO worklist.remove(0) means ids are processed in increasing order so the row-growth loop never leaves gaps. (3) classOf is bounded by bounds.length = classCount-1. (4) Forward-walk indices n-(pos+1) and n-pos are guarded by pos<n / pos<=n, so no negative index reaches JS `.at()` (which would otherwise wrap). Tables are compiler-emitted literals inlined at call sites; no user input, scrutinee value, or pattern shape can make a table internally inconsistent. The claimant's own scenario concedes reachability requires a hypothetical future edit to packBits/encode (e.g. revSets.init.iterator), i.e. an injected bug, not a path any real MLscript program takes. What is left is a defensive-hardening wish (assert the viability section length against the discarded revStateCount, make `sextet` reject unexpected characters, delete or use the dead `resultPrefixSize`) with no concrete failing scenario behind it.

## `Exit`'s `frames.pop()` sentinel test can never fire on an empty stack: `safeCall` rewrites `undefined` to `runtime.Unit`, turning a broken invariant into an undiagnosable `TypeError`

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls` — refuted 2/3

The claim's code reading is accurate — I confirmed Runtime.mls:374-378 and the generated Runtime.mjs:205-217 (`frame = runtime.safeCall(frames.pop())`) plus `safeCall` at Runtime.mjs:1410 mapping `undefined` to `runtime.Unit`, so an empty pop would indeed yield `Unit !== null` and then `TypeError: frame.at is not a function`. But the path is unreachable, which the claimant effectively concedes: their scenario was produced by hand-feeding an unbalanced program through a JS re-implementation of `StringCompiler.encode`, not by any pattern the compiler can compile.

I traced the full producer set. `Op.Enter`/`Op.Exit` are emitted only in `StringCompiler.buildReference` (StringCompiler.scala:506-522) and only as a matched pair around one freshly allocated SCC copy: `exitState --eps[Exit]--> cont` and `entry --eps[Enter(,Defer)]--> copyEntry`, where `entry` is the only external predecessor of `copyEntry` and `exitState` is the only continuation of the copy (`buildSccCopy` gives every member the same `cont`, and `checkTailPositions` forces internal references to be tail calls). None of the three reductions in `reduceStates` (StringCompiler.scala:583-644) can separate the pair: `dropDeadEdges` removes the `Enter` edge together with the copy whenever `cont` is dead; `contractTrivial` only contracts states whose single edge is `Eps(target, Nil)`, which `Enter`/`Exit` edges never are; `mergeIdentical` keys on the exact ordered edge list, so a state can only be redirected into an `Exit`-bearing state if it already carried an identical `Exit` edge to the same `cont`. Prefix mode (StringCompiler.scala:908-917) appends `boundary --eps[Rem]--> star` after the root continuation and does not cross a bracket. `encodeOps` (:767-784) interns by encoded content, so the shared `[7]` pool entry is only ever referenced by genuine `Exit` edges. `Enter`/`Exit` also cannot end up inside a deferred frame: `pending` is assembled only from Bind/Drop/Call/Mark/Slice/Add, and `capturedSlots` already `lastWords`-asserts against nested `Defer` (:336). Finally, ops run only for committed edges of a single accepted path (`execChain`), so speculative exploration cannot execute an unpaired `Exit`.

So there is no input, and no pattern, that reaches the cited failure. What remains is a defensive-coding nit (the `!== null` sentinel is not underflow-safe, and a future compiler change would surface as an opaque TypeError instead of a clean assertion) — minor at most, and not tied to a concrete failing scenario as the review bar requires. AGENTS.md:44-45 asks for assertions where invariants are *uncertain*; this one is structurally established by construction.

Separate, genuinely reachable observation the claim gestures at but does not make: the same `safeCall(undefined) === Unit` rewrite applies to `bindings.get(slot)` at Runtime.mjs:190 (frame capture) and Runtime.mjs:987 (result array), so an unbound slot surfaces as `runtime.Unit` rather than `undefined` to transforms and to the caller. That is a live path and would need its own finding. || The code reading is correct — Runtime.mjs:206 is `frame = runtime.safeCall(frames.pop())` and `safeCall` (Runtime.mjs:1410) maps `undefined` to `runtime.Unit`, so an underflowing pop would pass the `!== null` guard and die in `frame.at(0)`. But the underflow is unreachable from any MLscript program, which is what this lens tests.

`Op.Enter`/`Op.Exit` are balanced by construction and the balance is preserved by every reduction:
(1) `StringCompiler.buildReference` (lines 493-521) is the only producer. It allocates `exitState` with the single edge `Eps(cont, [Exit])`, builds the SCC copy with `cont = exitState`, then allocates `entry` with the single edge `Eps(copyEntry, Enter :: Defer?)`. All copy states are freshly allocated per reference, so the only edge into the copy from outside is the Enter edge and the only way out is exitState's Exit edge; internal `Synonym` tail calls (lines 476-486) are gotos to `entries(member)` and stay inside.
(2) Op ordering is `Op.Enter :: Defer`, so no `Defer` precedes its `Enter`; the SCC-internal `Defer` (line 485) sits on a state only reachable after `Enter`.
(3) `reduceStates` cannot separate them: `contractTrivial` only contracts states whose sole edge is `Eps(target, Nil)` (Enter/Exit edges carry ops, so they are never removed); `mergeIdentical` merges only states with identical ordered edge lists, which is bisimulation and preserves the op sequence of every path; `dropDeadEdges` removes whole dead regions (if the Enter edge dies, exitState becomes unreachable too).
(4) `frames` is declared outside the main walk loop and is cumulative, and `execChain` runs ops only along committed parent-chains, so the concatenation of all rounds is one genuine NFA path from start to accept — on which Enter/Exit are balanced.
(5) Prefix mode (lines 908-917) routes `root`'s continuation through `boundary` before the trailing lazy star, so all Exits run before `Rem`; it introduces no unbalanced path.

The claimant's evidence is a hand-forged table (`S --ε[Exit]--> Accept`) built with a hand-written JS port of `encode`, not output of the compiler, and their own stated trigger is a hypothetical future change ("any future compiler change that lets an Op.Exit edge be reached without its matching Op.Enter"). Also, `safeCall` rewriting `undefined` to `Unit` is pre-existing MLscript codegen applied to every call, not introduced by this PR, so the "defeats future `is undefined` guards" remark is not a property of this change either.

What remains is a defensive-coding/hygiene observation with no reachable failing scenario, which the review brief explicitly excludes ("Do NOT report anything you cannot tie to a concrete failing scenario"). Note the engine does already carry a comparable defensive throw for the analogous invariant ("StrPat: no viable transition (this is a compiler bug)"), so the asymmetry is worth a one-line comment at most, not a major finding.

## Unbound binding slots and value-stack underflows are silently materialised as `()` or a wrong slice instead of failing

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls` — refuted 2/3

The mechanism is described correctly (verified line by line in Runtime.mls and the generated Runtime.mjs: safeCall maps undefined to runtime.Unit at mjs:1410, and none of valStack/markStack/frames/bindings is checked), but the claimed consequence — an unbound slot or an underflow reaching user code as a wrong value — has no reachable path.

(a) The headline EmailAddress scenario is mis-stated: at that call site `compiled.visibleSlots` is EMPTY. The region root is `Synonym(CommaSep(Email))` (the `as emails` alias is peeled off before `makeStringRegionSplit`), and `Pat.symbols` for `Synonym` is `Nil`. The golden IR in EmailAddress.mls proves it — it emits only `Tuple.get(parseResult, 0)` and no `Tuple.get(parseResult, 1 + slot)`. The three `()` entries are dead payload in an array matched by `FlatPattern.Tuple(1, true)`. Both consumers (SplitCompiler.makeStringRegionSplit and Compiler.scala) read only `visibleSlots`.

(b) The only surface construct that could leave a visible slot (or a Call argSlot) unbound is an alternation binding a variable in some branches only — because `Or(patterns) => patterns.find(_ != Never).fold(Nil)(_.symbols)` takes just the first alternative's symbols. I probed this with a scratch diff test (since deleted): `if s is (("a" as x) | "b") ~ "c" then x` fails with `Name not found: x`, and the transform variant fails with `Found an inconsistent variable in disjunction patterns.` The check is the pre-existing, general `Variables.intersect`/`report` at hkmc2/shared/src/main/scala/hkmc2/semantics/Pattern.scala:100-128; inconsistent variables are removed from scope entirely. So every visible slot and every `Op.Call` arg slot is written on every accepting path. The StringCompiler comment "even if some binding branches are dead" is defensive, not evidence of a live hazard.

(c) The underflow behaviours are, by the claim's own admission, only reproducible on hand-forged tables. I also checked the Defer/capture path the claim implies as the risk vector: `capturedSlots` (StringCompiler.scala:328-338) is precisely read-before-write, and for CommaSep it captures `head` only while `tail` is written by the frame itself before its Call — so `readSlot` never sees an unwritten slot there.

What remains is a minor hardening/consistency point, not a major silent-miscompilation defect. || The mechanism is described accurately (Runtime.mls:455 pushes `bindings.get(s)` unconditionally; readSlot falls through to `bindings.get`), but the consequence does not reach generated code.

1. Only two consumers read slot entries: SplitCompiler.makeStringRegionSplit (~line 1262) and Compiler.multiMatcherStringBranch (Compiler.scala ~311). Both index `1 + slot` strictly for entries of `compiled.visibleSlots`, which StringCompiler.scala:902 pre-allocates from `root.symbols` BEFORE `build`, so visible slots occupy indices 0..k-1. Slots beyond them (transform-internal ones) are never indexed. The claim's headline scenario — `parseWhole` on the CommaSep(Email) table returning `[out, (), (), ()]` — is exactly that dead region: every `as` in CommaSep sits under a `=>` transform and `Pattern.symbols` returns Nil for `Extract` (ups/Pattern.scala:86), so `visibleSlots` is empty and the generated code (see the golden IR in EmailAddress.mls) reads only `Tuple.get(parseResult, 0)`. The `()` values are never destructured.

2. For a *visible* slot to be unbound, one disjunct would have to bind a root-level name a sibling does not. That is rejected at elaboration: semantics/Pattern.scala `Variables.intersect` records `Inconsistent` and `report` raises "Found an inconsistent variable in disjunction patterns" — a live golden error in ups/Future.mls:39 for precisely the shape `"" | (A as head) ~ Rep0[A]`. When both arms do bind the name, `Variables.allocate` gives them the same VarSymbol and therefore the same slot, so whichever arm commits writes it. `Or.symbols` picking the first non-Never arm is safe for the same reason. In the SplitCompiler path the region root is a source-level `Concatenation` (consistency-checked) or a `Constructor` -> `Synonym` (symbols = Nil); `makeStringPrefixAutomatonSplit` discards bindings entirely (`MatchSuccess([consumed, remaining], null)`) and reads no slots.

3. The Slice/Add underflow scenarios are admitted by the claim to be hand-built op programs, not compiler output. `Op.Slice` is emitted only by the pure-subtree shortcut in `build`, always on the ε-edge paired with that fragment's `Op.Mark` entry edge, and is never threaded onward as `exitOps` into another `build`, so it cannot appear inside an `Op.Defer` payload (only Add/Drop/Bind/Call/outer exitOps reach `pending`). No compiler path emitting an unbalanced Slice/Add was shown or found.

What remains is a hardening argument (no defensive checks in the engine), not a concrete failing scenario; AGENTS.md's assert guidance is about the Scala compiler code, where `softAssert`/`lastWords` are in fact used throughout `build`, and the engine does throw on "no viable transition" and on malformed ops.

Confidence is medium rather than high only because the multi-matcher path can, via `expand` inlining a definition body into an Or arm, produce a `visibleSlots` entry (a definition-internal symbol) that an arm without the inlined body does not write. But that record is either unread (compilePatternImpl marks the bindings symbol "TODO: This is useless"; FixedPointCompiler destructures only the output) or, if an enclosing transform did read it, it would fail earlier at compile time in `correspondence(symbol)`. So it is not an instance of the claimed silent `()`.

## Correctness of the never-cleared `visited`/`parentState`/`parentOps` maps rests on an undocumented, unasserted invariant whose violation is an infinite loop or an opaque `TypeError`

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls` — refuted 2/3

I re-read Runtime.mls:284-457 and the generated Runtime.mjs. The claimant's correctness trace is accurate (per-round `stack`, `visited.set(cur, gen)` guard making parent links an acyclic tree rooted at `cur`, `accept` parented immediately before `execChain` with `cur !== accept` guaranteed by the outer loop guard, `accept` never re-parented because the `pos === n` branch commits and the `pos < n` branch is a no-op, char edges carrying ranges not ops per decodeProgram line 209, `idx`-descending replay running root-side ops first). So there is no live defect. The finding is refuted on three grounds. (1) It asserts "zero comments" for the load-bearing invariant, which is false: lines 301-302 state exactly that these are "Per-round visit marks and the parent links of the current search, used to reconstruct the ε-path to the chosen transition", and the other non-obvious points are commented at 316-321, 417-419, and 436-437. (2) It asserts "zero assertions", but the module does assert its one non-obvious global invariant in the only way available to .mls runtime code: `throw Error("StrPat: no viable transition (this is a compiler bug)")` at line 420. AGENTS.md's softAssert/softTODO guidance targets the Scala compiler codebase; no such facility exists in .mls, and instrumenting this innermost loop has a real runtime cost. (3) The claimed failure mode is factually wrong: `prog.opsPool.[opsId]` compiles to `prog.opsPool.at(opsId)` (Runtime.mjs:192), and `Array.prototype.at(undefined)` coerces the index to 0 and returns `opsPool[0]` — there is no `TypeError: ops.length of undefined`. Finally the finding itself concedes it is "not currently triggerable" and its harm depends on two speculative future refactorings, which the review brief explicitly excludes ("Do NOT report anything you cannot tie to a concrete failing scenario or a concrete standard"). || Verified at hkmc2/shared/src/test/mlscript-compile/Runtime.mls:284-457. Three independent grounds for refutation:

(a) The finding's central premise — "a lot of load-bearing reasoning for zero comments" — is false at the cited location. Lines 300-302, directly above the three maps, state: "// Per-round visit marks and the parent links of the current search, used to reconstruct the ε-path to the chosen transition." That is precisely the per-round invariant the claim says is nowhere stated. Supporting documentation also exists at lines 130-144 (module header: two-pass Frisch-Cardelli scheme, pointer to StringCompiler.scala for table layout), 392 ("Execute the operations of the ε-path from the search root to `state`"), 417-419 (why the empty-stack throw is unreachable), and 436-437 (the accept / pos === n condition). AGENTS.md's "document intent behind complex logic" is met.

(b) One of the two claimed consequences is structurally impossible, not merely unreached. parentState and parentOps are always written as a pair (439/440, 446/447), so no state ever has a parent link without an ops entry. Under the hypothesised staleness, parentState.get(w) eventually returns undefined; `undefined !== cur` is permanently true, so the while at 396 never exits and runOps is never called. The claimed "TypeError: ops.length of undefined" via prog.opsPool.at(undefined) cannot happen (the code uses prog.opsPool.[opsId], not .at). Only the hang mode is even hypothetically real.

(c) Reachability (my lens): zero. The claim itself concedes "Not currently triggerable". No MLscript pattern or input can reach either mode; the claimant's own trace of facts (1)-(3) is correct, and I re-derived it: `stack` is re-created per round so every popped `source` is either `cur` or was stamped this round; `visited.set(cur, gen)` at 412 plus the `visited.get(target) !== gen` guard at 444 prevents re-parenting `cur`, so the chain always terminates at `cur`; and `prog.accept` is parented at 439 immediately before execChain(target) at 441, with `cur !== accept` guaranteed because `pos` is constant within a round (it only changes on the committing char edge at 431, which sets committed and exits the round), so if cur === accept then pos < n and the 438 guard blocks the branch entirely. The two "realistic triggers" are hypothetical future edits this PR does not make, and the second (hoisting `stack`) would require editing a line adjacent to the comment describing the per-round discipline.

(d) Secondary: the assert half of the standard does not transfer. AGENTS.md's softAssert/assert guidance targets the Scala compiler; Runtime.mls has only assertFail, and the proposed checks would sit in the innermost per-character loop of every compiled pattern, costing runtime in all generated programs to guard an invariant local to a single 45-line function call.

## `specialize`'s `Concat | CharClass => Never` cases depend on an unasserted non-local invariant whose violation is a `MatchError`

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Pattern.scala` — refuted 3/3

Both load-bearing parts of the claim fail on re-reading the code.

(a) The asserted failure mode is impossible. `Kind.Specialized <: Kind.Expanded <: Kind.Complete` (Pattern.scala:15-18) and `Pattern[+K <: Kind.Complete]` is covariant, so `SpPat = Pattern[Kind.Specialized]` is the NARROWEST of the three. `Concat`/`CharClass` (and the pre-existing `Literal`/`ClassLike`) extend `NonCompositional[Kind.Expanded]`, which is not a subtype of `Pattern[Kind.Specialized]`. `specialize` is `pattern.map[Kind.Specialized]`, so the compiler statically forces every such node to be replaced. `completePattern` (Compiler.scala:373ff) omits those cases because they are type-level impossible, not because it "relies on specialize". If a future change let a `Concat` survive specialization, the result would be a compile error in `specialize`, never a `MatchError`. This is also exactly the pre-existing arrangement for `Literal`/`ClassLike`, untouched by the PR.

(b) The asserted mechanism for breaking the invariant is wrong. `heads` (Pattern.scala:154) and `StringCompiler.containsStringNode` (StringCompiler.scala:148) are both built on the same `reduce` traversal (Pattern.scala:146), which descends through And/Or/Not/Rename/Extract and stops at every `NonCompositional` node. They therefore cannot disagree: a `Concat` nested under a `Tuple`/`Record`/`ClassLike` argument is invisible to `containsStringNode`, but every `Literal(StrLit)` in that same subtree is equally invisible to `heads`, so no `StrLit` head can coexist with it. Such a `Concat` reaches a sub-matcher via `collectSubPatterns`, where `buildMultiMatcherBody` recomputes `absorbStrings` over that sub-pattern set — the same traversal invariant, not a separate unenforced routing rule.

(c) The concrete example is self-refuting: in `x is ("a" | ("a" ~ "b"))` the `Concat` is under `Or`, which `reduce` does descend into, so `containsStringNode` is true, the `"a"` head is filtered out at Compiler.scala:158-165, and `specialize(StrLit("a"))` is never invoked on that pattern set. `"ab"` matches through the `Str` branch as intended.

Only two call sites of `specialize` exist (Compiler.scala:171 and 192), both inside `buildMultiMatcherBody` with heads drawn from the filtered list, so there is no alternate path.

No concrete failing scenario survives; the request for a `softAssert` rests on a consequence that does not follow. || The claim misreads the type discipline and the guard. (1) `Concat`/`CharClass` are `NonCompositional[Kind.Expanded]` (Pattern.scala:381,390) and `Pattern[+K]` is covariant with `Specialized <: Expanded`, so they are not `SpPat` values; `map[L](f: NonCompositional[? <: K] => Pattern[L])` (Pattern.scala:130) *requires* `specialize` to map them to some `SpPat`. The added cases are type-mandated, not optional defensive branches. (2) The asserted failure mode is impossible: `completePattern` (Compiler.scala:373-620) matches MatchedClassLike/Record/Tuple/Or/And/Not/Rename/Extract, which is exhaustive over `SpPat`; no `MatchError` can occur because no `SpPat` can be constructed containing `Literal`/`ClassLike`/`Concat`/`CharClass` (`map` only propagates `[L]` through And/Or/Not/Rename/Extract). (3) The invariant is enforced structurally, not by a distant coincidence: `Pattern.heads` (Pattern.scala:155) and `StringCompiler.containsStringNode` (StringCompiler.scala:148) are both `reduce` over the same ExPat and therefore visit exactly the same node positions. So a Concat at a head-visible position always sets `absorbStrings`, which filters every StrLit head and the Str head (Compiler.scala:161-165); and a Concat hidden under ClassLike/Record/Tuple arguments is invisible to `containsStringNode` only because `heads` is equally blind there, so no StrLit head can arise from that position either - it is routed to a sub-matcher by `collectSubPatterns`/`buildMultiMatcher`. The claim's stated escape hatch is precisely the case that is symmetric and therefore safe. (4) The concrete scenario `x is ("a" | ("a" ~ "b"))` does not reproduce: `reduce` descends through `Or`, absorbStrings is true, the `"a"` head is filtered, and both alternatives are compiled into the single `Str` branch. (5) There is exactly one call site of `specialize` in the compiler (Compiler.scala:103 via specializeSet at 171/192), both downstream of the filter - no unguarded entry point. What remains is a purely hypothetical future-refactor concern whose stated mechanism does not hold, with no reachable program today; that is below the "concrete failing scenario" bar. || Novelty lens first: the finding is NOT pre-existing. `git show hkust-taco/hkmc2:.../Pattern.scala` shows `specialize(lit)` as `case _: (Literal | ClassLike) => Never` — `Concat` and `CharClass` do not exist on the base branch at all. So novelty does not refute it. I refute it on the other allowed grounds: the claimed mechanism is wrong and the scenario is structurally impossible.

1) The claimed failure mode ("a `MatchError` one step later in `Compiler.completePattern`") does not follow. If the invariant were violated, `specialize(StrLit("a"))` maps `Concat` to `Never` = `And(Nil)`, which is a perfectly well-typed `SpPat` that `completePattern` handles via its `And` case. No `MatchError` arises. Conversely, the added cases are not optional: `Pattern.map` (Pattern.scala:130) is `f: NonCompositional[? <: K] => Pattern[L]` and must be total on `NonCompositional`; since `Concat`/`CharClass` are `NonCompositional[Kind.Expanded]` and not `Kind.Specialized`, they *cannot* be returned unchanged. Omitting the cases would `MatchError` inside `specialize` itself, not downstream.

2) The scenario's key step is false. It claims a `Concat` nested under a `Tuple`/`Record`/class argument is invisible to `containsStringNode` (true — `reduce` treats `NonCompositional` as leaves) and that this could let a `Concat` reach `specialize` alongside a live `StrLit` head. But `map` and `reduce` perform the *same* traversal: both stop at `NonCompositional` and only recurse through `And`/`Or`/`Not`/`Rename`/`Extract`. `specialize`'s `case ClassLike(...)`/`case Record|Tuple` replace or return the whole node without visiting its arguments (see `ClassLike(sym, arguments) => MatchedClassLike(symbol, arguments)`, arguments verbatim). So a `Concat` invisible to `containsStringNode` is equally invisible to `specialize` and can never reach the `Concat => Never` case. Any `Concat` that *can* reach it is in compositional position, which is exactly where `containsStringNode` sees it, which forces `absorbStrings = true`, which filters every `StrLit`/`Str` head. The invariant is structurally enforced by traversal alignment, not by luck.

3) The "guard lives 300 lines away in another file" framing is inaccurate: the head filter (Compiler.scala:161-166) and the only two `specialize` call sites (Compiler.scala:171, 192) are ~10 and ~30 lines apart inside the same function `buildMultiMatcherBody`; only the *definition* of `specialize` lives in Pattern.scala. `grep` confirms `specialize`/`specializeSet` has no other callers anywhere in `ups/`, so there is no bypass path.

4) The residual, non-string cases the code does reach are sound: e.g. `x is (1 | "a" ~ "b")` keeps head `IntLit(1)` (only `StrLit`/`Str` are filtered) and correctly specializes the `Concat` to `Never` under it.

What is left is at most "add a `softAssert` restating an invariant that the type/traversal structure already guarantees" — not a defect tied to a concrete failing scenario, and not what the reviewer's thumbs-down can be shown to mean. The claim as written misstates the consequence and its concrete scenario is impossible, so it is refuted.

## Dead `lower.nonEmpty && upper.nonEmpty` guard makes an impossible case fall into a misleading error message

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/Instantiator.scala` — refuted 3/3

Verified the code directly. The mechanical half of the claim is right: `Elaborator.isInvalidStringBounds` (Elaborator.scala:2361-2368) requires `value.length == 1` exactly and is applied at the only StrLit `Pattern.Range` construction site (Elaborator.scala:2515-2517); `Pattern.Range` is built nowhere else (only 2517/2518/2519). So `lower.nonEmpty && upper.nonEmpty` at Instantiator.scala:128 is indeed unreachable-as-false, and `.head` was already safe (the pre-PR code used `.head` with no guard at all).

However the finding's concrete consequence is factually wrong, and it is the only thing that made it a "finding" rather than a style nit. The guard tests `nonEmpty`, not `length == 1`. Under the claim's own headline scenario — relaxing `isInvalidStringBounds` to allow surrogate pairs — `"😀"` has length 2, so `nonEmpty` is true, the guard passes, and the `case _ => error("Range patterns are not supported in pattern compilation.")` arm is NEVER reached. What actually happens is worse and different from what was claimed: `CharClass(lower.head.toInt, upper.head.toInt)` computes `CharClass(0xD83D, 0xD83D)` for `"😀" ..= "🙏"` (both heads are the same high surrogate), a silently degenerate class. So the "misleading error message" consequence does not follow on the stated input, and the guard would not even be the thing that widens the error arm.

The only StrLit input that can reach the `case _` arm is an empty bound (`"" ..= "z"`), which requires relaxing the elaborator check to accept length 0 — not a plausible future change, and the reported message would then be a one-line fix in the same arm.

Refuting on two of the listed criteria: the failing path is unreachable today, and the consequence does not follow from the code as written. What survives is a pure hygiene note with no failing scenario, recorded in `correction`. || The claim's reading of the code is accurate, but under the reachability lens it collapses: the bad path cannot be reached by any MLscript program at the PR's HEAD, and the claim itself concedes this ("the guard is dead").

Verified facts:
- `Instantiator.scala:126-138` does contain `case (StrLit(lower), StrLit(upper)) if lower.nonEmpty && upper.nonEmpty => CharClass(lower.head.toInt, upper.head.toInt)`, with a fall-through `case _ => error(msg"Range patterns are not supported in pattern compilation.")`.
- `Pattern.Range` is constructed in exactly three places in the whole of `hkmc2/shared/src/main/scala` (grep for `Range(` excluding match arms yields only these): `Elaborator.scala:2517` (StrLit), `:2518` (IntLit), `:2519` (DecLit). The only other `Range(` hit in main is `ups/Pattern.scala:164`, which is `scala.collection.immutable.Range(0, n)`, unrelated.
- The StrLit construction at 2517 is guarded: `if isInvalidStringBounds(lower, upper) then Pattern.Wildcard() else Pattern.Range(...)`, and `isInvalidStringBounds` (`:2361-2368`) requires `value.length == 1` on both bounds, raising a precise error otherwise.

So a `Pattern.Range` with a `StrLit` bound of length != 1 is unconstructible, and `lower.nonEmpty && upper.nonEmpty` can never be false when both bounds are `StrLit`. Writing `"" ..= "z"` yields the accurate diagnostic "The lower bound of character ranges must be a single character." at elaboration time and never reaches the Instantiator. The claim's own scenario is explicitly counterfactual ("if `isInvalidStringBounds` is relaxed"), i.e. it depends on a source change that has not happened.

The `case _ =>` arm is reachable today only via `DecLit` ranges (e.g. `1.0 ..= 2.0`, elaborated at `:2519`), for which "Range patterns are not supported in pattern compilation." is a truthful message. Mixed-type literal ranges are already diverted to `Wildcard` at `:2521-2523`. So there is no input that produces the misleading diagnostic the finding describes.

Two further points against reporting this:
- The redundancy is not a silent-miscompilation or crash risk: if the invariant were ever weakened, the result is a *diagnostic-quality* regression on a construct that is currently a compile error anyway, not wrong runtime semantics.
- The AGENTS.md "assert invariants" hook is a fair stylistic preference, but the surrounding arm is a defensive `error(...)` fall-through that already existed pre-PR (the base had the same `case _ => error(msg"Range patterns are not supported...")`); the PR only added the guard and the `CharClass` encoding. Turning a dead guard into an assertion is a suggestion, not a defect tied to a concrete failing scenario, which the review brief explicitly excludes.

(Incidental, and NOT this finding: the same arm drops `rightInclusive` — `CharClass(lower.head, upper.head)` ignores exclusivity, as did the base's `(lower.head to upper.head)`. That is a real semantic gap but it is pre-existing behavior, a different defect, and outside the claim under review.) || Code reads as claimed and the blame is partly right: the `lower.nonEmpty && upper.nonEmpty` guard at Instantiator.scala:128 is genuinely added by this PR (base branch had `case (StrLit(lower), StrLit(upper)) => Or((lower.head to upper.head)...)` with no guard). And the claim's factual premises hold: `Elaborator.isInvalidStringBounds` (2361-2368) rejects any StrLit bound whose length != 1, and Elaborator:2516 is the sole site building `Pattern.Range` from StrLits (grep shows Range is only constructed at Elaborator 2517/2518/2519), so the guard is dead and `.head` was already safe.

It is refuted anyway, on three grounds:

(1) Unreachable path. The claim itself proves the fall-through is unreachable for StrLit ranges. Neither `"" ..= "z"` nor `"\u{1F600}" ..= "\u{1F64F}"` reaches Instantiator: both are caught upstream and get the precise message `The lower bound/upper bound of character ranges must be a single character.`, and the pattern is replaced by `Pattern.Wildcard()`. There is no input to today's compiler that produces the "misleading" message via a string range.

(2) The reachable half is pre-existing and untouched. The only currently-reachable way into `case _ => error(msg"Range patterns are not supported in pattern compilation.")` is a DecLit range (`1.0 ..= 2.0`, Elaborator:2519). That arm and its wording are verbatim diff context - identical on `hkust-taco/hkmc2`. So the "misleading error message" defect, to the extent it exists at all, is pre-existing and unchanged by this PR.

(3) The consequence inverts under the claim's own counterfactual. If `isInvalidStringBounds` were later relaxed to admit `""`, the base branch would throw `NoSuchElementException` on `"".head` (a hard crash inside the instantiator); the PR's guard turns that into a poorly-worded but non-crashing error. On the surrogate-pair variant, base would silently take `lower.head` = the high surrogate and build a nonsense literal disjunction (silent miscompilation), whereas the PR takes the same head into a CharClass - neither is worse than the other, and the guard is not implicated since a surrogate pair has length 2 and is rejected upstream identically in both versions. So the PR does not introduce or worsen any behavior here.

Residual point worth keeping, but far below defect level: per AGENTS.md ("assert invariants with softAssert/assert") the new dead guard would be better expressed as an assertion than as a silent widening of the error arm. That is a style observation on unreachable code with no failing scenario, not a reportable defect.

## The ~6 KB automaton table committed as a `:soir` golden in `EmailAddress.mls` is unreviewable and will churn on any compiler change

`hkmc2/shared/src/test/mlscript/ups/regex/EmailAddress.mls` — refuted 2/3

I read EmailAddress.mls, the encoder in StringCompiler.scala, and the decoder in Runtime.mls. The location is real (a `:soir` block was added at EmailAddress.mls:93-132 with one very long table literal on line 111), but nearly every substantive assertion the finding rests on is wrong.

1. Size is overstated. Line 111 is 5,326 chars; the string literal itself is 5,253 (sections: 17/48/2238/85/1841/1019). Not "6,100". Minor, but indicative.

2. "It has no diagnostic value" is false. This `:soir` block is the *only* place in the entire test suite that pins the `parseWhole` integration shape — `grep -rl parseWhole hkmc2/shared/src/test/mlscript/` returns EmailAddress.mls alone. It pins the `match input Str⁰ =>` guard, the three synthesized transform lambdas, their packing into `tmp`, and the `MatchSuccess`/`MatchFailure` plumbing. EmptyString.mls:12/36 only covers `matchWhole` (recognition-only, no actions, tiny reviewable table). Deleting `:soir` as the finding proposes would delete real coverage: a silent regression to the old greedy prefix-composition path, or a mis-built action array, would show up here and nowhere else. The behavioural block at 134-143 alone does not distinguish "compiled via the automaton" from "fell back".

3. "the only place the format is documented is the `encode` scaladoc" is false. Runtime.mls documents the same layout independently: the `Program` and `Matcher` data-class field lists (lines 147-155), the `decodeProgram` section indexing (193-226), and `sextet`/`decodeBits` (165-191) describing the Base64 six-bit packing that mirrors `packAlphabet`/`packBits`.

4. "no test decodes a table to check the two are in sync" is false. `Runtime.StrPat.decodeProgram` runs on encoder output in every behavioural string-pattern test added by this PR (EmailAddress.mls:134-143, plus the new CompiledSemantics.mls and NonRegular.mls). Encoder/decoder disagreement on any section boundary would fail those immediately. The round-trip is exactly what is tested.

5. The failure scenario is structurally impossible in the code as written, so it is not a concrete scenario. `reduceStates.mergeIdentical` (StringCompiler.scala:630-645) keys the representative map on `(state == accept, edges.toList)`; the boolean component means the accept state can never share a class with a non-accepting state, which is precisely the corruption the scenario posits. The claim frames it as a hypothetical future regression, but that is a counterfactual about code that does not exist, not a defect in this PR.

I also checked the thing that *would* have made this a real finding — golden flakiness from nondeterministic encoding — and it is not present: `reverseDeterminize` uses `LinkedHashMap` for subset ids (line 741) so `ids.keysIterator.toList` is in id order, `encodeOps` interns via a `Buffer` with `indexOf`, and all state iteration is index-ordered. The table is deterministic.

What remains is the subjective observation that a 5 KB opaque literal is unpleasant to review — which is (a) the same line LPTK already commented on, with a fix already requested (hoist to a top-level field), and (b) not tied to any AGENTS.md standard; AGENTS.md contains no rule on golden size or opacity and in fact mandates committing regenerated golden outputs. The review brief explicitly excludes findings not tied to a concrete failing scenario or a concrete standard. || I read the cited location and the surrounding logic. The mechanical description is roughly right (a `:soir` block was added at EmailAddress.mls:93 and line 111 embeds the table), but the argument that makes it a finding does not survive.

1. The central premise is false. The claim says the golden "cannot detect a *wrong* table — only a *different* one" and that "nothing in the file signals that anything changed semantically." The same file, 20 lines later, runs `parseEmails(emails.join(","))` on the seven-element list and pins the full result (EmailAddress.mls:134-143). That call goes through `@compile`, so it hits `runtime.StrPat.parseWhole`, which at runtime *decodes the very table string in the golden* (`decodeProgram`/`parseRun` in hkmc2/shared/src/test/mlscript-compile/Runtime.mls:193, :284) and re-executes it. A table that miscompiles changes that behavioural golden. The `:soir` block is not the correctness evidence and was never claimed to be.

2. The claim's final paragraph — "no test decodes a table to check the two are in sync" — is simply wrong. Every `@compile` behavioural test is an end-to-end encode→decode→execute round-trip: `StringCompiler.encode` produces the string, `Runtime.mls` `decodeInts`/`decodeBits`/`decodeProgram` consume it, and the printed output is goldened. An encoder/decoder mismatch cannot be silent.

3. The proposed scenario is not concrete. "`mergeIdentical` merges the accept state with a non-accepting one, breaking `Op.Exit` for one nesting depth" while `parseEmails(emails.join(","))` "might still pass" — the behavioural test exercises `CommaSep` recursion at depths 1 through 7 and pins seven distinct output strings. A broken `Exit` at any depth changes that output. The claimant offers no depth at which the break would be invisible.

4. No standard is violated. AGENTS.md (which I read in full) says nothing about golden size, opacity, or churn; its "silent miscompilation" clause is about reasoning over code correctness, not test verbosity. Large opaque goldens are pre-existing, accepted practice in this repo: at the base ref, hkmc2/shared/src/test/mlscript/nofib/awards.mls:5 is a single 32,655-character golden output line, and mandel.mls (7,467) and eliza.mls (5,814) are comparable. The added line is 5,334 chars including the `//│ ` prefix — smaller than goldens already in the tree.

5. Two factual slips: the string is ~5.2 KB, not "6,100 characters"; and it is not "a single opaque integer/base64 string" but a five-section `;`-delimited encoding (header / bounds / NFA / revTrans / bit-packed viability), documented in `encode`'s scaladoc and mirrored by `decodeProgram`.

6. The only residual kernel — the table should not be inlined at the call site — is verbatim LPTK's existing comment #3, so it is already handled. Note also that `Runtime.mls:157-160` already memoizes decoded programs in `programs`/`matchers` Maps keyed by the table string, so the decode does not in fact happen "on every match"; what remains is the literal's placement, which is his point, not a new one.

Under my reachability lens the golden is trivially reachable (it is committed and runs in CI), but reachability is not what fails here — the consequence does not follow, the supporting facts are wrong, and the non-duplicative part is a style preference the repo does not share.

## `CompiledSemantics.mls` states "Transforms run exactly once" as a global rule, but the non-sequence path disagrees and no test contrasts them

`hkmc2/shared/src/test/mlscript/ups/regex/CompiledSemantics.mls` — refuted 3/3

The finding's central claim and its concrete scenario do not hold up.

(a) The scenario is factually wrong. It asserts `if "0" is ZeroLogged then "y" else "n"` (named pattern, no `~`, no `@compile`) "prints nothing". It prints. `SplitCompiler.compilePattern(pd: PatternDef)` (~line 1462) builds the `unapply` method with `makeMatchSplit(inputSymbol.toScrut, pd.pattern, true)` — outputNeeded is hardcoded `true` — and `makeMatchSplit`'s `Constructor` case routes a non-parametric PatternSymbol to `makeMatchPatternSplit` (line 560), which emits a call to that `unapply`. So the transform runs for both `ZeroLogged` and `ZeroLoggedSeq`; adding `~ ""` changes nothing observable. The claimed minimal pair does not exist.

(b) The transform elision the claim relies on (`case Transform(...) => if !outputNeeded then makeMatchSplit(scrutinee, pattern, false)`, line 800) is reachable only for inline patterns and, via `compilePatternImpl`, under `@compile` (line 851 is the only caller of the "efficient" `compilePattern`). It is therefore not "any pattern with no `~`" but "the inlined/specialized path".

(c) The cited contrasting evidence is pre-existing and untouched. `SimpleLiterals.mls:31-42` (`print of Some("0") is Some(@compile ZeroLogged)`) is not in the diff; `git diff hkust-taco/hkmc2...HEAD` for that file touches only lines 48-57.

(d) The underlying eager/lazy divergence also predates the PR on the `~` side: the legacy `makeStringPrefixMatchSplit`'s `case Transform(...)` (line 1082) takes no `outputNeeded` and always emits the transform call, so `("a" => print("ran")) ~ "b"` used purely as a condition already ran the transform before this PR. The PR narrows it from "possibly several times, including abandoned parses" to "exactly once on the committed parse" — an improvement, not a newly introduced contradiction.

(e) The doc file is explicitly scoped ("This file pins down the semantics of compiled string patterns") and the sentence's stated contrast target is the old backtracking translation running transforms on abandoned parses, not a language-wide claim about eagerness.

Refuted on the grounds "the code does not do what is claimed" and "pre-existing and untouched by this PR". || Refuted on three independent grounds.

**1. The scenario as written is not reachable — it omits `@compile`, and without it both sides run the transform.**

The claim's repro is:
```
if "0" is ZeroLogged then "y" else "n"     // claimed: prints nothing
```
A bare reference to a pattern symbol does not go through the `outputNeeded` machinery at all. `SplitCompiler.makeMatchSplit`'s `Constructor` case (SplitCompiler.scala:657-666) dispatches to `makeMatchPatternSplit`, which (lines 580-590) emits a *call to the pattern's precompiled `unapply`* and destructures `MatchSuccess(output, bindings)`. `unapply` is compiled ahead of time with no knowledge of the use site, so it always computes the output — i.e. always runs `observeZero`. The elision the claim relies on only exists on the *inlining* path: `Annotated(pattern, @compile)` → `compilePattern` (SplitCompiler.scala:835-854) → `makeMatchSplit(..., outputNeeded)` → `Transform` case at SplitCompiler.scala:800-801, `if !outputNeeded then makeMatchSplit(scrutinee, pattern, false)`. That is exactly why the cited golden `print of Some("0") is Some(@compile ZeroLogged)` carries `@compile`. Drop the annotation and the contrast disappears.

**2. Even with `@compile` added, the asymmetry is entirely pre-existing and untouched by this PR.**

- The lazy side: the `!outputNeeded` short-circuit at SplitCompiler.scala:800-801 is not in the diff (`git diff hkust-taco/hkmc2...HEAD` on SplitCompiler.scala touches `outputNeeded` only inside the `Concatenation` case).
- The eager side: before this PR, `(... => f(x)) ~ "..."` went through the legacy `Concatenation` case → `makeStringPrefixMatchSplit(scrutinee, left)`, whose `Transform` case (SplitCompiler.scala:1082-1104, unchanged by the PR) takes **no** `outputNeeded` parameter and unconditionally builds and applies the transform lambda. So `~` was already eager and non-`~` already lazy on the base branch. The PR changes *which* parses transforms run on (exactly once, on the committed parse, instead of also on abandoned ones) — not *whether* they run when output is unused.

**3. The doc comment is explicitly scoped; the "global rule" reading is a misreading.**

`CompiledSemantics.mls:3` opens with "This file pins down the semantics of **compiled string patterns**", and the whole preamble is about sequences ("Recognition is relational: **a sequence** matches when *some* split of the scrutinee matches..."). The sentence at :10 and the expanded note at :53-56 sit inside that scope, and :55-56 makes the intended contrast explicit — "(The backtracking translation used to run transforms on parses it later abandoned.)" — i.e. it is contrasting with abandoned-parse re-execution, not asserting anything about output-demand elision. Within the automaton path the rule is in fact accurate: `makeStringRegionSplit` takes the recognition-only fast path only when `compiled.pure || (!outputNeeded && visibleSlots.isEmpty && actions.isEmpty)`, and a transform makes `actions` non-empty (`pure = !anyOps && slots.isEmpty && actions.isEmpty`, StringCompiler.scala:927), so the parse path is always taken.

**4. The secondary sub-claim about `SimpleLiterals.mls:51` is factually wrong.**

The claim says there is "no added positive assertion that `@compile ManyZero` now accepts `"000"` or `""`". `hkmc2/shared/src/test/mlscript/ups/regex/TailRepetition.mls` (exists in base, unchanged, still green) contains `pattern ManyZeros = "0" ~ (ManyZeros | "")` with `:expect true` on `"0"` and `"000"` and `:expect false` on `""`, `"1"`, `"0001"`, `"1000"`, plus a parametric `Rep(pattern S)` case. The `@compile`-on-`~` path specifically is positively asserted in the PR's new `ups/regex/EmptyString.mls` (`"" is @compile Oops` → `= true`, with `:soir` IR showing the `Runtime.StrPat.matchWhole` call). So the behavior is pinned; at most one could ask for an extra positive line in SimpleLiterals.mls, which is a nit below the reporting bar.

What is left after all this is at most an editorial suggestion that the preamble could say "in a compiled sequence" — not tied to any concrete failing scenario or to any AGENTS.md standard, and not a defect introduced by this PR. || Traced the actual behavioural asymmetry the finding rests on, and it is pre-existing on `hkust-taco/hkmc2`, untouched by this PR.

1. The "lazy" arm is unchanged. `git show hkust-taco/hkmc2:.../ups/SplitCompiler.scala` line 782 already reads `case Transform(pattern, parameters, transform) => if !outputNeeded then makeMatchSplit(scrutinee, pattern, false)` — the transform is skipped when the output is not demanded. The PR does not touch this case, and the golden file proves it: `git show hkust-taco/hkmc2:.../ups/specialization/SimpleLiterals.mls` lines 35-41 are byte-identical to HEAD (`print of Some("0") is Some(@compile ZeroLogged)` → `> true` with no `zero 0`, then the binding block → `> zero 0`). The claim's own evidence for one half of the "inconsistency" is verbatim base-branch behaviour.

2. The "eager" arm is also unchanged in the only respect the scenario tests. The base `makeStringPrefixMatchSplit` (base line 914) takes **no `outputNeeded` parameter at all**, and its `Transform` case (base line 1064) unconditionally emits `Split.Let(lambdaSymbol, Lam(...), tail = make((_output, remains, bindings) => ... app(lambdaSymbol.safeRef, ...) ...))`. Base `makeMatchSplit`'s `Concatenation` case routes the left operand through that prefix path regardless of `outputNeeded`. So on the base branch, `if x is ("a" => print("ran")) ~ "b" then "yes" else "no"` already ran the transform. Adding `~ ""` already changed whether a `print` was observed, before this PR.

3. If anything the PR *improves* this arm: it makes the transform run exactly once on the committed parse instead of also on abandoned backtracking alternatives (the parenthetical at CompiledSemantics.mls:55-56). The eager/lazy split is not widened either — `makeStringRegionSplit` is only entered from the `Concatenation` case or from `isParametricStringSite`, which itself requires `containsStringSeq`, i.e. exactly the `~`-containing regions that were already eager.

4. The documentation half of the claim misreads the file's scope. CompiledSemantics.mls:3 opens with "This file pins down the semantics of **compiled string patterns**", and line 10 ends a paragraph that is explicitly about "a sequence matches when *some* split of the scrutinee matches" / "the committed parse". The sentence at :53 is scoped to the automaton path by both its file header and its immediate context; it is not asserted as a rule over the whole pattern language, so it is not false.

5. The residual sub-point — SimpleLiterals.mls:51 losing `:e`/`:todo` while keeping `res = false`, so the block now passes for a different reason with no added positive assertion — is real but is a trivial test-hygiene nit, and the capability it would assert is positively asserted twice elsewhere in the same PR: `ups/regex/Identifier.mls` adds `isWord of "pattern" //│ = true` and `isManyDigits("5678") //│ = true` (recursive `~` under `@compile`), and `ups/regex/EmptyString.mls` adds `"" is @compile Oops //│ = true` (nullable recursion). That does not sustain the finding as stated.

Pre-existing and unchanged on the base branch ⇒ refuted under the novelty/blame lens.

## `StringCompiler` is single-use by construction but this is neither documented on the class nor enforced

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala` — refuted 2/3

I re-read StringCompiler.scala (class decl at 151, mutable fields at 159/193-194/270/293/307/313/316/318-319, compile at 894, encode at 839, reduceStates at 585) and every call site.

What the claim gets RIGHT: the instance state is real, `compile` is the only entry point, it appends to all of it and resets nothing, `reduceStates` does not compact the `states` buffer (it only filters/retargets edges), `computeSccs` uses a *local* `nextScc` starting at 0 while `recursiveSccs` is instance-level, and the class itself carries no scaladoc stating single-use and no assert. So the mechanical description of the state is mostly accurate.

Why I refute it anyway:

1. The path is unreachable. All three construction sites make a fresh instance per region: SplitCompiler.scala:1243 and :1281 (`new StringCompiler(using context)`, each with a `context` from a freshly-constructed `Instantiator` — so reuse there isn't even expressible without also reusing the Instantiator), and Compiler.scala:285 (`StringCompiler()` inside the per-label fold). `compile` is never called twice on one instance anywhere in the repo, and nothing in the PR moves toward that.

2. The headline concrete consequence is factually wrong. The claim says `slotCount` in the header being inflated makes the caller's `1 + slot` "read the wrong array element and bind the wrong string". It does not. `slotOf` = `slots.getOrElseUpdate(symbol, slots.size)`, so a second run's symbols get indices continuing after the first run's; `visible` records those same absolute indices; the header records the total `slots.size`; and Runtime.mls:453-457 pushes `bindings.get(s)` for `s` in `0 until prog.slotCount` after `result.push(output)`. So `result[1 + slot]` still lands on exactly the slot the compiler assigned — the array is merely oversized with unused leading entries. Same for `actions`: `Compiled.actions` is `actions.toList` (the whole buffer) and `Op.Call(actionId, …)` indexes into that same list, so the indices stay consistent. Both are size waste, not misbinding. The two consequences that would be genuine (`recursiveSccs` id collision across runs corrupting Enter/Exit bracketing, and sticky `failed`/`anyOps`) are the ones the claim treats as secondary, and they are still only reachable under the hypothetical refactor.

3. The gap is already documented at the only place where reuse is even tempting. In Compiler.scala the `Context` is a class-level given shared by all labels, and that is precisely where the author wrote "each label needs its own compiler: a compiler instance accumulates the automaton states (and failure flag) of a single region" (Compiler.scala:281-283). The SplitCompiler sites each mint their own Context, so the "cache compilers keyed by Context" refactor the scenario posits has no natural pull there. `Compiled`'s scaladoc also already says "The result of compiling one string region", and `compile`'s says "Compile a string region rooted at `root`".

What survives is a documentation/robustness nit, not a major defect: there is no input, no test, and no existing call path that produces wrong code, and the specific miscompilation the claim describes cannot occur. || The code description is accurate (the class does carry per-region accumulating mutable state and `compile` at StringCompiler.scala:894 is the sole entry point that never resets it), but the finding is unreachable and therefore not a defect.

All three and only three call sites construct a fresh instance immediately before their single `compile` call, and never retain the instance:
- SplitCompiler.scala:1243-1244 — `val compiler = new StringCompiler(using context)` then `compiler.compile(instantiated, Mode.Whole)`; `compiler` is a local val that dies with the expression.
- SplitCompiler.scala:1281-1282 — same shape with `Mode.Prefix`.
- Compiler.scala:285 — `StringCompiler().compile(fragment, Mode.Whole)` is constructed *inline inside* the `patterns.iterator.foldLeft`, so a fresh compiler is created per label; there is no shared instance to poison.

Additionally, reuse is not merely avoided but structurally implausible at two of the three sites: the compiler takes `using context: Context` produced by a fresh `new Instantiator` for that specific region (SplitCompiler.scala:1241-1243, 1279-1281), so a compiler is tied by its constructor to exactly one instantiation context. Sharing one across regions would require sharing a `Context` too.

There is also no re-entrancy: `compile` is defined once and never called recursively — recursive pattern references are handled internally by `buildReference`/SCC machinery within the same run, which is precisely what the accumulating state is for.

So no MLscript program, however written, can cause a second `compile` on a live instance; the claimed consequences (stale `recursiveSccs` ids, inflated `slotCount` shifting the caller's `1 + slot` destructuring at SplitCompiler.scala:1266, `anyOps`/`failed` carryover) all require a hypothetical future refactor that does not exist in this PR. The claim itself frames the scenario that way ("Any future refactor that reuses a `StringCompiler`").

The AGENTS.md assert argument does not rescue it either: that guidance covers invariants "you are not sure ... hold". Here the invariant holds by construction at every call site, and the author already documented the hazard at the one site where it is non-obvious (the per-label loop, Compiler.scala:281-283). Adding a `used` flag + assert would be a reasonable defensive nicety, but it is a suggestion with no concrete failing scenario, which the review brief explicitly excludes.

## The decoded viability matrix is materialized as a JS boolean array, retained forever in an unbounded global cache

`hkmc2/shared/src/test/mlscript-compile/Runtime.mls` — refuted 2/3

Verified the cited code directly. TRUE: `decodeBits` (Runtime.mls:176-191) does build a JS array with one boolean element per bit, and `viable` (:247-248) indexes it; that array is retained inside the `Program` stored in the module-level `programs` Map (:159).

But the two load-bearing consequences are wrong:

(1) `matchers` does NOT hold a second such array. `decodeMatcher` (:236-240) stores `sections.[3]` raw and `matchWhole` (:279) reads it as a plain character string (`starts.charCodeAt(rev) === 49`, i.e. '1'). The encoder confirms this: StringCompiler.scala:878 emits `starts` as '1'/'0' chars, not through `packBits`. `decodeBits` has exactly one call site, in `decodeProgram`, for `viability` only. Moreover `matchTable` and `table` are chosen mutually exclusively per call site (SplitCompiler.scala:1250 vs :1255), so the "same automaton decoded twice" path in the scenario does not exist.

(2) The caches are not unbounded. Tables are emitted as source string literals (`fld(str(compiled.table))` at SplitCompiler.scala:1251/1256/1287 and Compiler.scala:290/304), so the key space is fixed at compile time by the number of distinct pattern tables in the program, and identical literals are internalized so re-evaluation adds no entries. This is a lazily-initialized static table bounded by program size, not a leak — and its lifetime is identical to the top-level-field caching LPTK's own review comment #3 requests.

(3) The AGENTS.md hook does not apply: the "no new global mutable state" rule (AGENTS.md:55-59) targets non-local mutation in the Scala compiler ("things like the Symbol classes") and permits it when documented in code, which the author did at Runtime.mls:157-158. Runtime.mls already has module-level state elsewhere.

(4) Measured the actual email table from the golden file: stateCount=130, viability section 1019 base64 chars = 6114 bits, revStateCount=47 — so ~49 KB, matching the modest case. But the same `Program` also eagerly decodes `revTrans` (799 ints) and a `states` structure from 2238 chars into hundreds of nested arrays, of the same order of magnitude; the boolean array is not the dominant cost. The 3 MB Blow12 figure derives entirely from a separate, unverified state-explosion finding, not from `decodeBits`.

Residual: a constant-factor memory inefficiency with no correctness consequence and no concrete failing scenario, below the stated reporting bar. || The construct is trivially reachable (any parseWhole call site decodes the viability section), so the finding is not refuted on reachability grounds per se. It is refuted because the claimed consequence does not follow and two load-bearing parts of the scenario are factually wrong about the code.

(a) The `matchers` cache does NOT materialize a boolean array. `decodeMatcher` (Runtime.mls:235-239) constructs `Matcher(header[0], header[1], decodeInts(sections[1]), decodeInts(sections[2]), sections[3])` — `starts` is kept as the raw string section and read with `matcher.starts.charCodeAt(rev) === 49` (Runtime.mls:279). `decodeBits` is called only from `decodeProgram`. So the scenario's "a second such structure if the same automaton is also used in recognition-only position via matchTable" is false.

(b) The cache is not unbounded. Table strings are only ever emitted as JS string literals by the compiler (`str(compiled.table)` at SplitCompiler.scala:1251, `str(compiled.matchTable)` at Compiler.scala:288). The key set is therefore exactly the set of table literals statically present in the compiled module — finite and fixed at compile time. No running program can grow it. That makes `StrPat.programs` a per-call-site memo, i.e. functionally the same lifetime as the top-level static field LPTK explicitly asked for in review comment 3. "Retained forever in an unbounded global cache" describes the reviewer-endorsed design, not a leak.

(c) The numbers are inflated. I measured the actual EmailAddress table: header `130,1,0,3,17,47,0` → stateCount=130, revStateCount=47 → 6110 viability bits, 1019 base64 chars, and the *entire table literal is 5253 chars* and is retained by the module regardless (it is the cache key). With V8 pointer compression (default in Node) a PACKED_ELEMENTS boolean array costs ~4 bytes/slot → ~24 KB, not ~49 KB — roughly 5x the already-retained source literal, not the claimed 64x. The Blow12 amplifier is also self-limiting: if revStateCount reached 8195 the emitted base64 section alone would be ~63,000 chars of generated JS source, a compile-time-visible codegen-size problem that dwarfs and subsumes the runtime array.

(d) The AGENTS.md citation is misapplied: the rule (AGENTS.md:57) says "refrain from adding new global mutable state to things like the Symbol classes" — it targets compiler symbol classes, and Runtime.mls already contains module-level mutable state (`mut val curEffect`, `resumeValue`, `stackLimit`, `stackDepth`, `stackHandler`, `Debug.enabled`).

What remains after stripping the false parts is a bare constant-factor space nit in one decoder helper, with no concrete failing scenario and no standard violated — below the reporting bar set for this review.

## `StringCompiler` uses none of the `trace` debug facilities the rest of the `ups` package relies on

`hkmc2/shared/src/main/scala/hkmc2/semantics/ups/StringCompiler.scala` — refuted 3/3

I re-read the cited code and the sibling files.

Facts the claim gets right: `StringCompiler.scala:894` is `def compile(root: Pat, mode: Mode): Opt[Compiled] = scoped("ucs:string-compiler"):`, and the file contains exactly three `log` calls (921, 924, 925) and zero `trace` calls across 927 lines. `build`, `buildReference`, `buildSccCopy`, `reduceStates`, `reverseDeterminize` are indeed silent.

But the load-bearing premise — "Every other compiler in `semantics/ups` instruments its recursive workhorses with `tl.trace`... and the various `FixedPointCompiler` entry points" — is false, and I verified it directly. `FixedPointCompiler.scala` (770 lines, the closest structural sibling: a recursive, non-trivial machine-construction compiler) contains **zero** `trace` calls and exactly **three** `log` calls (lines 376, 379, 578). Its only instrumentation is `scoped("ucs:fixpoint")` wrapped around its entry points (lines 162, 168, 190, 208) — precisely the pattern `StringCompiler` follows with `scoped("ucs:string-compiler")` around `compile`. So instrumentation density in `StringCompiler` (927 lines / 3 logs / scoped entry point) is identical to the sibling the claim cites as evidence of the norm. There is no package-wide `trace` convention being violated; `trace` is used in `Compiler.scala` (146, 204, 378) and `SplitCompiler.scala` (1455, 1526), not in `FixedPointCompiler` or `Instantiator` (which uses `scoped` only).

No standard is violated either: I grepped AGENTS.md for trace/log/debug/scoped and it says nothing about instrumentation. The task brief explicitly requires findings tied to a concrete failing scenario or a concrete standard; this claim's scenario is openly counterfactual ("Suppose the transform-dropping bug had *instead* manifested as a wrong binding..."), i.e. it describes no actual defect in this PR.

I also checked the debug plumbing is not dead: `TraceLogger.scoped` (utils/TraceLogger.scala:42) sets `scope`, and `MLsDiffMaker.scala:263` makes `etl.doTrace` true when the topic is in `showUCS`, and `StringCompiler` is constructed from `SplitCompiler`/`Compiler` with that logger — so `ucs:string-compiler` is a live, working topic. The topic-name shape point (hyphen vs. colon) is a naming nit, explicitly out of scope, and is not even uniformly violated (`ucs:pattern:resolution`, `ucs:ups:compilation` show the existing names are already heterogeneous).

Adding traces would be a reasonable reviewer *suggestion*, but as a reported defect it misstates the code norm it rests on and has no failure attached. || The claim's central premise — that "every other compiler in `semantics/ups` instruments its recursive workhorses with `tl.trace`", specifically naming "the various `FixedPointCompiler` entry points" — is factually false. Actual counts across the package:

- Compiler.scala: 3 `trace`, 9 `log`, 793 lines
- SplitCompiler.scala: 2 `trace`, 5 `log`, 1552 lines
- FixedPointCompiler.scala: **0 `trace`**, 3 `log`, 770 lines
- Instantiator.scala: **0 `trace`**, 3 `log`, 187 lines
- Pattern.scala / Context.scala: 0 `trace`, 0 `log`
- StringCompiler.scala: 0 `trace`, 3 `log`, 927 lines

So `trace` is used by exactly two of the seven files. StringCompiler's instrumentation (one `scoped` topic plus three `log` calls dumping state/slot/action counts and both encoded tables) is at parity with FixedPointCompiler — a 770-line file the claim cites as a positive example while it in fact contains zero traces. The claimed package norm does not exist.

Second, there is no standard to anchor this to. I grepped AGENTS.md for trace/log/debug/scoped/topic: the only hits are unrelated lines about default arguments, DRY, and comments. AGENTS.md mandates `softAssert`/`assert`/`softTODO` for invariants — which is about correctness, not observability — and says nothing about `tl.trace` coverage.

Third, the reachability lens kills the consequence. This is not a code path a user program can reach at all: `scoped`/`log` output is inert unless a difftest enables the topic, and no `.mls` test in the repo enables `ucs:string-compiler`, `ucs:fixpoint`, or `ucs:instantiation` (grep over hkmc2/shared/src/test/mlscript returns nothing). There is no input, valid or invalid, that produces different compiled output or different runtime behavior because of this. The "worst outcome is silent miscompilation" framing is borrowed rhetoric: missing trace calls cannot cause miscompilation, only make one marginally slower to diagnose.

Fourth, the scenario is explicitly counterfactual ("Suppose the transform-dropping bug ... had instead manifested as a wrong binding"). It hypothesizes a different bug than the one actually found and then complains that debugging it would be inconvenient. That is not a concrete failing scenario; the review brief forbids reporting findings not tied to one.

On the sub-point about the topic name: topic shapes in the codebase are already heterogeneous — `ucs:cp`, `ucs:ups:tree`, `ucs:pattern:resolution`, `ucs:normalized` vs `ucs:normalize` (two near-duplicates already coexist). `ucs:string-compiler` is no more surprising than what is already there, and it is a naming nit, which the brief says to ignore absent an explicit AGENTS.md rule.

The only residual truth is a subjective preference: the largest file in the package could benefit from per-construct tracing in `build`/`buildReference`/`buildSccCopy`/`reverseDeterminize`. That is a reasonable suggestion to leave as a passing remark on the PR, but it is a style/ergonomics preference with no defect, no standard, and no reachable consequence behind it. || The finding's load-bearing premise — that "every other compiler in `semantics/ups` instruments its recursive workhorses with `tl.trace`", so StringCompiler deviates from an established convention — is factually false, and the PR worsens nothing.

Measured counts of `trace(` / `log(` across `hkmc2/shared/src/main/scala/hkmc2/semantics/ups/` at HEAD:
- Compiler.scala (793 L): 3 trace, 9 log
- SplitCompiler.scala (1552 L): 2 trace, 5 log
- FixedPointCompiler.scala (770 L): **0 trace**, 3 log
- Instantiator.scala (187 L): **0 trace**, 3 log
- Pattern.scala (483 L): 0 / 0
- Context.scala (26 L): 0 / 0
- StringCompiler.scala (927 L, new): 0 trace, 3 log, 1 `scoped` topic

So 4 of the 6 pre-existing files carry no `trace` at all. The claim explicitly names "the various `FixedPointCompiler` entry points" as trace-instrumented; `git show hkust-taco/hkmc2:.../FixedPointCompiler.scala | grep -c "trace("` returns 0 on the base branch and 0 at HEAD. FixedPointCompiler is the closest structural analogue (770-line fixpoint/automaton compiler) and has exactly the same instrumentation shape as the new StringCompiler: a `scoped(...)` topic plus three `log` calls. StringCompiler is therefore at the package norm, not below it. The claim's supporting assertion that it is "the largest single file in the package" is also wrong — SplitCompiler.scala is 1552 lines.

Novelty/blame lens specifically: trace counts on the base branch are identical to HEAD for the two files that do use trace (Compiler 3→3, SplitCompiler 2→2), and 0→0 for FixedPointCompiler and Instantiator. The PR removes no instrumentation and degrades no existing debugging path. The only sense in which this is "introduced" is that a new file exists which, like the majority of its siblings, does not use `trace` — that is not a defect introduced or worsened by the PR.

No standard is violated either: AGENTS.md contains no requirement about `trace`/`log`/debug instrumentation (grep for trace|log|debug|scoped in AGENTS.md yields only unrelated lines about default arguments, centralizing similar logic, and comments explaining intent). The review brief requires findings tied to "a concrete failing scenario or a concrete standard"; this is tied to neither — the scenario is a hypothetical future debugging inconvenience for a bug reported separately, not a defect in this code.

The trailing point about `scoped("ucs:string-compiler")` being hyphenated where sibling topics are not is a pure naming nit (existing topics include `ucs:pattern:resolution`, `ucs:ups:compilation`, `ucs:fixpoint`), and the brief instructs ignoring naming nits absent an AGENTS.md rule, of which there is none.
