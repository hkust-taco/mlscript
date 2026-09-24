# New-resolution suite migration

## Scope and current progress

The first pass tried all 372 active `.mls` files in `basics`, `codegen`, `ucs`,
`ups`, and `apps` with new resolution and strict resolution, retaining 185 ports.
After dynamic shapes and non-strict suite defaults became available, all 187
deferred worksheets were retried, bringing the count to 239. After declared
interfaces, generic flow, tuple projections, and Array inheritance were implemented,
all 133 remaining worksheets (plus the two deferred WASM worksheets) were retried.
This pass migrates another 13, bringing the count to 252 of 372 (68%). The 51 files under
`ucs/staging` are excluded by the test runner and remain unchanged. Counts below exclude shared `.mls`
configuration files and new-resolution regression tests.

| Suite | Migrated | Retained on existing configuration | Active files |
| --- | ---: | ---: | ---: |
| basics | 60 | 30 | 90 |
| codegen | 86 | 39 | 125 |
| ucs | 52 | 18 | 70 |
| ups | 49 | 22 | 71 |
| apps | 5 | 11 | 16 |
| Total | 252 | 120 | 372 |

Migrated files start with `:.`. Each suite's `.mls` loads the common language
configuration and uses its non-strict default; nested directories inherit through
`:..`. The redundant `#lang(strictResolution: false)` settings have been removed
from the six general suites, including WASM. `newres` retains strict resolution;
`newres/loose` still needs an explicit override of that strict parent. Non-strict
resolution permits multiple selection/call targets, but still rejects missing
targets and known invalid operations. The common language configuration disables
JS execution, so each file retains its original execution flags. A parser-only test must not acquire runtime execution
merely because its resolution configuration changes.

The previous batch comprised one basics test (`ObjectExtensions`), 16 codegen
tests, two UCS compiled-pattern tests, and 35 UPS tests. They include JavaScript
imports, spread calls, qualified constructors, and recursive, parametric, and
fixed-point patterns. Five new UPS directory configurations connect these tests
to the common language configuration.

In that batch, forty-nine files needed only the configuration header and refreshed goldens.
`BadThis`, `BasicTerms`, `Spreads`, and `ImportMLs` additionally expect static
errors for invalid operations already present in their negative cases; no existing
error expectations were removed. `Throw` uses `new Error(...)`, preserving its
throw/catch results. Tests of foreign callable classes remain deferred rather
than being rewritten to avoid the capability under test.

The latest ports are:

- basics: `DynamicSelection`, `ExplicitLabels`, `LiteralSelection`, `MutArr`.
- codegen: `Arrays`, `BlockPrinter`, `CurriedClassInheritance`, `Inliner`, `Misc`,
  `NestedScoped`, `PlainClasses`, `TraceLog`.
- UPS: `regex/EmailAddress`.

Nine need only the configuration header and refreshed goldens. `ExplicitLabels`,
`CurriedClassInheritance`, `PlainClasses`, and `Arrays` additionally expect compilation errors
for existing negative cases now rejected statically: a shadowed label's missing
`break`, invalid constructor overapplication/member selections, and an empty call
on a plain class, and known out-of-bounds tuple reads. Their existing runtime-error
expectations remain in place.

The two remaining WASM worksheets were also retried; both remain deferred.
WASM therefore remains at 19 migrated worksheets out of 21, outside the table
above.

Blocked files retain their complete original sources and golden outputs. No new
per-file `:todo`, `:fixme`, `:ignore`, or resolution-mode exception hides a migration
failure. Existing expected failures remain visible. The inventory below records
trial observations, not newly accepted failures.

The five migrated application worksheets still import compilation fixtures in
their existing mode. This is caller-side migration, not a claim that all imported
application implementations use new resolution. The 20 application compilation
fixtures and four `mlscript-compile/ups` fixtures need a subsequent dependency-ordered
migration. Their shared consumers make a blanket flag change inappropriate for
this worksheet migration.

The annotated-receiver capture assertion in WASM `Basics` is fixed; a later
unannotated `this.x` initializer still blocks that worksheet (see task 3).
Method calls across REPL blocks remain assigned to the other branch.
The constructor-pattern context-mixing regression now passes; the remaining
pattern-transfer gaps are listed below.

## Straightforward fixes applied

1. Named record/tuple fields elaborate their values with the enclosing
   interpretation. `value: expression` inside a term tuple is not a type
   annotation. Existing `basics/NamedArgs.mls` exercises this distinction.
2. Compiler-generated `runtime.assertFail` calls use a synthetic selection, like
   other runtime helpers. This is not a fallback for unresolved source selections.
   `basics/Assert.mls` and `DisruptiveComments.mls` retain runtime assertion tests.
3. Free-variable collection recognizes the new direct reference forms. Pattern
   guards no longer produce spurious unused-binding warnings; see
   `ucs/patterns/GuardedPatternBindings.mls`.
4. Type applications propagate the underlying shape, preserving the requested
   interpretation and capture handling. Class validation and lowering look
   through erased type arguments. `newres/TypeApplications.mls` checks generic
   construction, inheritance, and function-result member lookup. Generic substitution
   and constraint flow are now implemented as described in task 3; type-argument
   validation is still incomplete (`basics/GenericClasses.mls`).
5. Pattern compilation annotations forward binding-shape propagation to the
   annotated pattern. Remaining pattern forms and matcher synthesis are separate
   work, described below.
6. Argument matching retains the original parameter and argument counts for
   diagnostics. A two-argument call with one supplied argument no longer reports
   the counts of the unmatched tails.
7. The assertion test explicitly constructs `new Error(...)`. An invalid
   selection from a declared class now expects its compilation error in
   `basics/Declare.mls`.

One intended semantic change is visible in `codegen/ImportConflicts.mls`: an
explicitly bound `Some5` wins over a wildcard open, yielding `"555"` rather than
`5`. That follows the already-agreed wildcard-open rule.

## Design questions and proposed decisions

### 1. Structural members and opaque values

Record fields now have their own `BlockMemberSymbol`s. Member lookup follows
record overwrites and spreads in source order and retains the selected value's
shape and captures. Tuples retain precise zero-based element projections and expose
the builtin Array class as their parent. This supports inherited members, Array
patterns, and inference of Array element type arguments. The parent uses the union
of element shapes, preserving both annotations and call-context marks.

The prelude now declares Array's common instance methods and their result
interfaces, and identifies `Array.prototype` as an Array value. Callback parameter flow supports rest parameters receiving the
remaining arguments; Array callbacks receive the element, index, and array.
Imported legacy signatures preserve substituted parameters across the member's
lexical boundary. Mutable arrays discard their initial element shapes and length,
because methods such as `push` and `reverse` can change both. Unknown layouts still
permit indexed access with an unknown result, without authorizing arbitrary members.

Generic methods use the same marked parameter flow as generic free functions,
including explicit arguments, callback-result inference, and curried signatures.
`Array.map[U]` returns `Array[U]`. Declared callable shapes retain their type
parameters. `NewResolverState` owns the inference graph and caches. Listeners have
type `TermShape => NewResolverState ?=> Unit`, so imported callbacks resolve hosts
through the consuming state. Importing touches only the accessed hosts: their
candidates and listeners are copied lazily, and caches consult individual source
entries on demand. Type-parameter references retain their originating host, so
exporter-private inference on third-party parameters survives re-exporting without
copying or enumerating whole resolver maps. Legacy annotation interpretations
also stay local instead of attaching consumer callbacks to shared prelude syntax.
Completion seals each file or diff-test block's recorded decisions and the original
host data read by erasure/lowering. Symbol flow and elimination listeners remain
active against private host data; they cannot change completed reference targets,
even between blocks sharing the same elaborator state.

`newres/GenericMethods.mls` now covers exported mapped arrays and imported generic
functions and methods with inferred results. Compiler-cache tests check independent
consumers and unchanged source candidates, listeners, and legacy annotations.
Publisher tests cover cycles, reentrant replay, transitive private inference, and
bounded copying in the presence of unrelated exporter hosts.
The external-identity case in `newres/NestedModules.mls` also passes. A remaining
`:fixme` records a capture assertion when a map callback reads a constructor field
in a module initializer, before importing comes into play.

Array declarations remain incomplete: `concat` returns `Array[Any]` because its
rest arguments currently have no declared element constraint. This does not infer
result precision from an opaque annotation.

**Accepted policy:** JavaScript imports (including package imports), `globalThis`,
and explicit dynamic selection/instantiation introduce `DynShape`. Ordinary
selections and calls on these values are checked at runtime and yield dynamic
values. `foo() as dyn` explicitly gives a result this behavior; `fun bar(x: dyn)`
provides it to a parameter independently of call-site inference. Type aliases may
also denote `dyn`. These rules apply in both strict and non-strict resolution.
Dynamic instantiation uses the existing `new!` syntax.

Before sealing a file or diff-test block, `InterfaceExposure` checks the values
reachable through its exposed interface. It seeds unannotated parameters and
unconstrained generic parameters with `UnknownValueShape`, then follows returned
functions, record/tuple contents, and public instance members. Local examples do
not close an exposed interface: both `fun foo(x) = x.a` and
`fun foo[A](x: A) = x.a` are rejected even if this unit calls `foo({a: 1})`.
Private helpers can retain local inference unless their function values escape.
Parameter annotations provide their declared shapes; callable result annotations
constrain returned implementations through their declared domains.

Discovery uses a queue and temporary observers of shape publishers. Each reached
shape is processed once, with listeners discovering subsequent candidates; there
is no repeated whole-graph scan. Observers are detached before the unit is sealed
and are never copied into consumer states. New-resolution imports have already had
their interfaces checked; the importer does not recursively recheck definitions
from other compilation units.
An unknown reaching a previously sealed elimination can still report an error,
without changing its recorded target.

Unknown values and unresolved spreads carry shared, lazy provenance. Messages,
locations, and diagnostic chains are materialized only on an error; provenance is
excluded from shape equality. Diagnostics can identify a generic parameter or
ordinary parameter and then show the record/tuple storage and return steps that
expose it. `newres/InterfaceExposure.mls` covers these paths, recursive discovery,
private helpers, returned typed closures, overloaded class exports, and later
exposure of a private definition from an earlier block. Constructor patterns
narrow unknown inputs to declared class interfaces, retaining unknown type
arguments and provenance for unannotated fields. They cannot discard the external
alternative and specialize those fields from local calls alone.

Flooding also reveals existing limits of capture precision. Forwarding through
captured functions or constructor aliases, rebuilding an instance of the same
class, and exposing partially applied constructors can lose the originating
activation. These cases conservatively report unknown-value errors and remain
explicit `:fixme` regressions in `CtxSens`, `ValCtxSens`, `Projections`,
`RecursiveEnvironment`, and `SpreadCalls`; they need a more precise representation
of captured activations. Unknowns are not converted to dynamic values to bypass
these failures. Unsupported inference forms can still have no candidates at all;
completion of such empty flows remains separate from rejecting an unknown target.

An additional gap is recorded in `InterfaceExposure.mls`: a private class returned
through a nominal result annotation can expose callable methods without those
implementations being flooded. Fixing this requires following the declared member
interface back to its implementations, while still keeping unannotated fields and
results opaque; traversing every initializer would incorrectly expose values the
annotation hides.

Dynamic selections have no fabricated nominal definition. Lowering retains their
runtime receiver and property name. Dynamic values propagate through record and
tuple spreads and unique wildcard opens. Competing wildcard-open receivers still
require disambiguation: choosing one would change which runtime object is read.
Class projections, constructor patterns, and type references also retain their
requirements for a known, unambiguous identity.

`DynShape` is distinct from `UnknownValueShape`: recursive widening, mutable
record reads, and other losses of inference precision do not automatically
license dynamic member lookup or calls. A known missing member in another receiver
candidate still reports an error even if a dynamic candidate is also present.
The same rule applies to values recovered from constructor patterns.

Regression coverage is in `newres/Dynamic.mls`, `newres/Records.mls`,
`newres/SpreadCalls.mls`, `newres/Arrays.mls`, and `newres/loose/Targets.mls`.

### 2. Pattern transfer and synthesized references

Evidence: new shape propagation lacks record, negation, string
concatenation, and transformation cases. Examples include
`ucs/general/BooleanPatterns.mls`, `patterns/String.mls`, and
`normalization/RecordImpliedByClass.mls`. Tuple bindings currently publish no
shapes. `CompiledQualifiedConstructors.mls` and `CompiledClassPatterns.mls` now
pass and are migrated, as are most UPS fixed-point, recursive, and parametric
cases. Remaining failures include unsupported pattern forms, patterns used as
terms (for example `.unapply`), and synthesized selections entering new resolution
in `ucs/examples/EitherOrBoth.mls`.

**Question:** what resolution state should synthesized matcher references share
with source references, and what precision should recursive/transformed pattern
bindings promise?

**Proposal:** retain the source reference's completed target and receiver path
when lowering synthesizes matcher code; use the existing `Lowering` capability
to obtain that result. Do not clone listener hosts with empty candidate sets or
re-run name lookup from the generated tree. Add explicit pattern transfer rules
that distinguish matched input shapes, bound-field shapes, and transformed
output shapes. Compose alternatives by union and conjunctions by successive
filtering; negation must not invent positive bindings. Reuse a dependency graph
with cycle-aware subscriptions for recursive patterns. Establish convergence
before trying to fix recursive cases by adding recursion limits.

Acceptance cases: bound members after tuple/record extraction, nested constructors,
aliases, guards, transformed results, repeated references, qualified imported
constructors, and recursive UPS matchers. Compare results and generated matcher
structure with the existing tests. `ups/examples/HindleyMilner.mls` now finishes
its new-resolution trial, but retains unsupported member and pattern cases
(see the recheck below).

### 3. Declared interfaces versus inferred values

Evidence: the prior WASM `Basics` failure mixes a nominal annotated receiver with
an untyped constructor field carrying a different capture context.
`codegen/CurriedClassInheritance.mls` now migrates after updating its existing
negative expectations; `ParamClasses.mls` still exposes constructor-value member
lookup rather than a remaining annotation-opacity decision.

**Implemented:** annotations are opaque shapes. `b: Base` exposes Base's declared
members and preserves virtual dispatch; an implementation or observed argument
cannot add subclass members. Parameters, result annotations, separate signatures,
and constructor fields use the same declared interfaces, even without observed
calls. Reading an unannotated member through such an interface yields an unknown
shape instead of following its initializer or method body.

Type interpretations retain arrows, type arguments, and lexical captures. Generic
aliases and inherited declared interfaces substitute their type arguments. Explicit
and inferred function/constructor type arguments flow through the corresponding
type-parameter symbols with entry/exit marks; explicit arguments prevent further
refinement from value arguments. Inference also connects parameters through nested
nominal arguments, as in `Foo[A]` containing a `Box[A]`. Declared member selections
carry those type-argument contexts without reading implementation value flow.

`newres/DeclaredTypes.mls` covers unused annotated functions, unannotated fields,
subclass overrides, inherited fields, curried constructors, nested captures,
generic aliases, separate signatures, and distinct generic instantiations. Its
function/tuple-constraint example now passes: callback parameter types flow into
implementation parameters, callback results constrain inferred type arguments,
and calls through declared signatures contribute argument constraints. Tuple
types retain their element interfaces, and zero-based projections preserve
capture marks through tuple values, declared types, and spreads. Mutable tuple
reads do not reuse initializer shapes. Distinct callback instantiations and
opaque annotated tuple elements have regression coverage.

WASM tuple reads and writes pass, using indexed lowering. The complete callback
example and calls through tuple elements remain explicit WASM `:fixme` cases:
that backend still lacks the required first-class function representation and
anonymous-function lowering. REPL method cases remain assigned to the other branch.

The original annotated-receiver cases from WASM `Basics` now pass and are covered
by `newres/wasm/DeclaredTypes.mls`. A fresh trial reaches a later capture assertion
in the unannotated initializer `class Foo(val x) with val y = this.x`.
`CurriedClassInheritance` now expects the earlier compilation errors as well as
its existing runtime errors. `ParamClasses` still reaches unimplemented
constructor-value member lookup (`Foo.class`); it and WASM `Basics` remain deferred.

### 4. Dynamic construction and foreign callable classes

`codegen/ImportJSClass.mls` now passes with dynamic construction and is migrated.
`basics/DynamicInstantiation.mls` remains blocked by unimplemented member lookup
in `DefnShape.getMemberImpl` for `new! C.class(1, 2)`; its previous class-lowering
failure is no longer the first observed blocker.
`PredefUsage.mls` calls JavaScript's `String` as a function, while its current
declaration supplies only a module interpretation. Bare MLscript classes also
reject old empty-call syntax, as intended by the earlier migration.

**Question:** how should foreign declarations expose both call and constructor
capabilities, without making every module or bare class implicitly callable?

**Proposal:** give foreign declarations explicit callable/constructible
capabilities using the existing overload interpretation mechanism. Explicitly
dynamic construction already lowers to dynamic IR; keep static `new` on the
listener-resolved class path.
Change test syntax only where that preserves the test's intent; tests explicitly
about callable JS constructors must not be rewritten to avoid that feature.

Acceptance cases: imported JS classes, callable-and-constructible externals,
plain MLscript classes, companion values, dynamic constructor expressions, and
errors when a selected interpretation lacks the required capability.

## Remaining implementation work, not new semantic decisions

### Rechecked generator and Hindley–Milner failures

On the merged tree, `codegen/Generators.mls` finishes its new-resolution trial
in about 1.3 seconds. Its earlier timeout was not reproduced. The primary
failure is unresolved `.next`: `NewResolver.appShape` follows a generator's body
as if the call returned its ordinary result, whereas lowering produces a
JavaScript generator object. The small `:fixme` regression
[`newres/GeneratorResults.mls`](../hkmc2/shared/src/test/mlscript/newres/GeneratorResults.mls)
shows this without `yield`: a generator returning `1` makes resolution reject
`.next` as a member of an integer literal. Generator calls need their own result
shape and iterator-member behavior; annotation recognition already works.

`ups/examples/HindleyMilner.mls` now finishes a new-resolution trial with JavaScript
disabled in about 1.4 seconds. It still reports unsupported member-variable shapes
and pattern/member errors, so the original worksheet retains its existing mode.
The recursive environment regression
[`newres/RecursiveEnvironment.mls`](../hkmc2/shared/src/test/mlscript/newres/RecursiveEnvironment.mls)
now resolves and executes, including actual recursive calls, explicit `new`,
nested class captures, wildcard opens, and partial construction.

The unbounded marks came from a missing lexical boundary: a method's reference to
an outer constructor captured the method scope but skipped its enclosing instance.
Class bodies now introduce captures, and a class and its constructor share one
resolution boundary. Consuming a reconstructed instance cancels the old instance
exit against its capture, retaining the fresh constructor exit. Explicit `new`
uses the same constructor context, including for arguments and later parameter
lists. Context fragments compose from the definition to its consumer; argument
flow traverses that composition in reverse. Optional debugging assertions detect
repeated boundaries in either direction; the private `checkMarkPaths` flag disables
them by default because scanning each new mark's tail makes chain construction
quadratic in its depth. There is no truncation or depth limit.
These changes also fix the sibling-subclass field-extraction regression in
`newres/ConstructorFieldRecovery.mls`, whose independent results are now checked.

### What the latest trials now reach

- `basics/MiscArrayTests`: `reverse` and the correctly shaped `map` callbacks work.
  Its unary callback now fails statically, as well as at runtime; the later `map`
  function still needs parameter flow from a subsequent REPL block.
- `codegen/FirstClassFunctionTransform`: tuple-held calls work, making three old
  error expectations obsolete, but later closure cases still report an unfinished
  `foo` definition. The worksheet is not migrated by merely removing expectations.
- `codegen/SetStmt`: the first `concat` resolves; update-assignment argument flow
  and reassigned aggregate shapes remain incomplete.
- `codegen/ObjectMethodDebinding`: `id(Test).foo` still has no resolved target.
  Adding an expected error would not establish the intended debinding diagnostic.
- Imported application results still lack the required interfaces: CSV's nested
  tuple selection, Iter's `reverse`, and parser collections' `sort`/`join` remain
  unresolved. Adding Array members cannot manufacture missing receiver shapes.

### Other implementation work

- Audit assignments to member symbols and definition initializers. The trial
  reaches unimplemented direct member-reference shape cases and missing
  assignment lowering in several mutation tests.
- Add transfer rules for result-bearing control flow, handlers, and quotation
  where the resolver currently has no shape rule. Preserve the established
  capture model and the boundary between elaboration and lowering.
- Review module-forwarding compatibility in `basics/CyclicModuleForwarders.mls`.
  The latest trial no longer overflows the stack; it rejects forwarding between
  the distinct nominal module types `M1` and `M2`. Do not discard its old expected
  outcomes without deciding the intended module compatibility rule.
- Preserve source origins in synthesized references and diagnostics. Some
  migrated error cases now report a definition rather than a use site, or lose
  a location. In particular, `ups/UpsBugsBacklog.mls` and
  `ups/syntax/MixedParameters.mls` retain their expected undefined-binding errors
  but lose the use-site location. These need attention without changing the
  chosen symbol.

## Execution order and completion gates

1. **Retain this measured batch.** Run compilation fixtures, main difftests,
   application difftests, and the aggregate suite. Review output changes; keep
   nonmigrated files intact. WASM `Basics` retains its previous configuration
   pending its remaining unannotated-initializer capture fix.
2. **Model generator results.** Recursive constructor contexts now normalize
   through lexical captures. Use `GeneratorResults` to specify iterator results rather
   than propagating the generator body's return shape. The earlier generator
   timeout was not reproduced.
3. **Complete structural targets and external signatures.** Dynamic JS values and
   record fields, tuple projections, and inherited Array members are supported;
   finish mutation flow, primitive members, and foreign declarations in small batches. Re-run affected negative tests as
   well as successful programs.
4. **Complete pattern transfers and reference preservation.** Start with UCS
   conjunction/record/tuple cases, then the remaining recursive and transforming
   UPS cases. Keep fixed-point behavior tested independently from matcher code
   generation. Preserve the now-passing constructor-field context regressions.
5. **Complete type/interface and call validation.** Preserve opaque annotations
   and marked generic flow; finish generic validation, rest-parameter signatures,
   module checks, and the WASM migration. Keep cross-block method work coordinated externally.
6. **Migrate shared compilation fixtures from leaves upward.** Begin with the
   four UPS fixtures; then application parsing data types, lexer, parser helpers,
   and entry points. Rebuild `.mjs` dependencies before each worksheet batch.
   Verify cache/import behavior across old and new consumers during transition.
7. **Remove the remaining legacy suite configurations.** Require no new failure
   suppressions, no lost negative diagnostics, reviewed goldens, and a successful
   `hkmc2AllTests/test`. Commit code and golden outputs together under the agent's
   identity once that gate is met.

## Validation

- `ctest`: all 47 selected compilation tests pass.
- `catest`: all 20 application compilation fixtures pass in their existing mode.
- `cwtest`: the WASM compilation fixture passes.
- `hkmc2AllTests/test`: all 951 tests pass, including 708 main tests, 18 application
  tests, and 22 WASM tests. The main count includes directory configurations and
  new-resolution regressions; it is not a count of migrated worksheets.
- All retained ports have reviewed goldens. Deferred worksheets retain their
  original source and output; no trial-generated application report changes remain.

## Deferred-file inventory

The following are the first observed trial failures, which may be symptoms rather
than root causes. Each path is relative to `hkmc2/shared/src/test/mlscript/`.
The files themselves retain the pre-trial configuration and output.

### basics

- `basics/BadAssignments.mls`: Unexpected exception; scala.NotImplementedError: SelfRef(globalThis:globalThis) (of class SelfRef)
- `basics/BadModuleUses.mls`: Unexpected lack of compilation or type error after `module Example with`
- `basics/BadOverloading.mls`: Unexpected lack of compilation or type error after `class Foo`
- `basics/BadTypeClasses.mls`: Unexpected lack of compilation or type error after `M.f`
- `basics/Classes.mls`: Unexpected compilation error; This selection of member 'id' has no resolved target
- `basics/CompanionModules_Classes.mls`: Unexpected compilation error; Resolution error in application; Module 'C' cannot be called like a function.
- `basics/CompanionModules_Functions.mls`: Unexpected compilation error; Resolution error in application; Module 'foo' cannot be called like a function.
- `basics/CyclicModuleForwarders.mls`: Unexpected compilation error; Cannot use a value of type 'module M1' at an unrelated type 'module M2'
- `basics/DynamicFields.mls`: Unexpected compilation error; Resolution error in selection; Instance of class constructor 'DynCtor' does not contain member 'dynField'
- `basics/DynamicInstantiation.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.DefnShape.getMemberImpl`)
- `basics/FunDefs.mls`: Unexpected compilation error; Resolution error in application; Value of type 'Int' cannot receive more argument lists.
- `basics/GenericClasses.mls`: Unexpected lack of compilation or type error after `class Foo[A](x: Foo[A, A])`
- `basics/Inheritance.mls`: Unexpected lack of error to fix after `[Bar.x, Bar.foo]`
- `basics/MiscArrayTests.mls`: Unexpected compilation error; Resolution error in function type; Callback parameter list does not match its declared function type.
- `basics/ModuleMethods.mls`: Unexpected lack of compilation or type error after `fun f(m: M)`
- `basics/MultiParamListClasses.mls`: Unexpected compilation error; Resolution error in application; Instance of class constructor 'Foo' cannot receive more argument lists.
- `basics/MutRcd.mls`: Unexpected compilation error; Resolution error in selection; Record literal does not contain member 'foo'
- `basics/MutVal.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `basics/New.mls`: Unexpected lack of warnings after `new`
- `basics/NewMut.mls`: Unexpected compilation error; Resolution error in selection; Instance of class 'Foo' does not contain member 'y'
- `basics/NewlineOps.mls`: Unexpected compilation error; This selection of member 'length' has no resolved target
- `basics/NewlineSels.mls`: Unexpected compilation error; This selection of member 'c' has no resolved target
- `basics/OpenIn.mls`: Unexpected compilation error; Builtin '~' is not a binary operator
- `basics/Overloading.mls`: Unexpected compilation error; Resolution error in application; Module 'Foo' cannot be called like a function.
- `basics/PrefixOps.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'Bin'
- `basics/Puns.mls`: Unexpected exception; scala.NotImplementedError: Record(List((Ident(a),Alias(Wildcard(),Ident(x))))) (of class Record)
- `basics/Records.mls`: Unexpected compilation error; Resolution error in selection; String literal does not contain member 'repeat'
- `basics/StrTest.mls`: Unexpected lack of compilation or type error after `(~)("a")`
- `basics/Underscores.mls`: Unexpected compilation error; This selection of member 'f' has no resolved target
- `basics/ValMemberSymbols.mls`: Unexpected compilation error; This selection of member 'x' has no resolved target

### codegen

- `codegen/AuxiliaryConstructors.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `codegen/BadOpen.mls`: Unexpected compilation error; Resolution error in selection; Module 'Foo' does not contain member 'y'
- `codegen/ClassMatching.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.DefnShape.getMemberImpl`)
- `codegen/ConfigDirective.mls`: Unexpected compilation error; This selection of member 'call' has no resolved target
- `codegen/ConsoleLog.mls`: Unexpected compilation error; This selection of member 'log' has no resolved target
- `codegen/CurriedClasses.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.DefnShape.getMemberImpl`)
- `codegen/ErasedTypes.mls`: Unexpected compilation error; Resolution error in application; Value of type 'Function' cannot be called like a function.
- `codegen/FirstClassFunctionTransform.mls`: Unexpected lack of compilation error after `bar([foo].0)`
- `codegen/Generators.mls`: Unexpected compilation error; This selection of member 'next' has no resolved target
- `codegen/Getters.mls`: Unexpected compilation error; This selection of member 'oops' has no resolved target
- `codegen/Hygiene.mls`: Unexpected compilation error; Resolution error in selection; String literal does not contain member 'foo'
- `codegen/ImportExample.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `codegen/ImportedOps.mls`: Unexpected compilation error; Builtin '~' is not a binary operator
- `codegen/ModuleMethods.mls`: Unexpected lack of compilation or type error after `Example |>. s(123)`
- `codegen/Modules.mls`: Unexpected compilation error; Resolution error in application; Module 'None' cannot be called like a function.
- `codegen/NestedClasses.mls`: Unexpected compilation error; This selection of member 'x' has no resolved target
- `codegen/NoFreeze.mls`: Unexpected compilation error; This selection of member 'x' has no resolved target
- `codegen/NoModuleCheck.mls`: Unexpected lack of compilation or type error after `M."foo"(1)`
- `codegen/ObjectMethodDebinding.mls`: Unexpected compilation error; This selection of member 'foo' has no resolved target
- `codegen/Open.mls`: Unexpected compilation error; Resolution error in selection; String literal does not contain member 'length'
- `codegen/OpenWildcard.mls`: Unexpected compilation error; Wildcard-open reference 'None' is ambiguous; candidate: object 'None' defined here
- `codegen/ParamClasses.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.DefnShape.getMemberImpl`)
- `codegen/PartialApps.mls`: Unexpected compilation error; Resolution error in application; Tuple literal cannot receive more argument lists.
- `codegen/PredefUsage.mls`: Unexpected compilation error; Resolution error in application; Module 'String' cannot be called like a function.
- `codegen/PrivateMembers.mls`: Unexpected compilation error; This selection of member 'y' has no resolved target
- `codegen/Pwd.mls`: Unexpected compilation error; This selection of member 'pop' has no resolved target
- `codegen/Quasiquotes.mls`: Unexpected compilation error; Unsupported quasiquote type member reference
- `codegen/RandomStuff.mls`: Unexpected exception; java.lang.StackOverflowError
- `codegen/ReboundLet.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `codegen/RuntimeUsage.mls`: Unexpected compilation error; Resolution error in selection; Class value does not contain member 'leaveOut'
- `codegen/SanityChecks.mls`: Unexpected compilation error; Resolution error in application; Function literal expected 2 arguments, but got 1
- `codegen/ScopedBlocks.mls`: Unexpected compilation error; Resolution error in application; Module 'Foo' cannot receive more argument lists.
- `codegen/ScopedBlocksAndHandlers.mls`: Unexpected exception; shape propagation for handler expressions is unimplemented.
- `codegen/Scoping.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `codegen/SelfReferences.mls`: Unexpected lack of compilation or type error after `module Foo with`
- `codegen/SetStmt.mls`: Unexpected compilation error; This selection of member 'concat' has no resolved target
- `codegen/ThisCallVariations.mls`: Unexpected compilation error; This selection of member 'call' has no resolved target
- `codegen/ThisCalls.mls`: Unexpected lack of compilation or type error after `Example |>. g(123)`
- `codegen/While.mls`: Unexpected compilation error; Resolution error in application; Integer literal cannot be called like a function.

### ucs

- `ucs/examples/BinarySearchTree.mls`: Unexpected compilation error; Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/examples/EitherOrBoth.mls`: Unexpected exception; java.lang.Exception: Internal Error: Synthetic selections must not enter new resolution
- `ucs/examples/LeftistTree.mls`: Unexpected compilation error; Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/examples/ListFold.mls`: Unexpected compilation error; Builtin '~' is not a binary operator
- `ucs/examples/ULC.mls`: Unexpected compilation error; Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/general/BooleanPatterns.mls`: Unexpected exception; scala.NotImplementedError: Composition(false,Negation(Literal(IntLit(2))),Negation(Literal(IntLit(3)))) (of class Composition)
- `ucs/hygiene/HygienicBindings.mls`: Unexpected compilation error; Resolution error in application; Class value cannot receive more argument lists.
- `ucs/normalization/Deduplication.mls`: Unexpected compilation error; This selection of member 'length' has no resolved target
- `ucs/normalization/InheritanceNormalization.mls`: Unexpected exception; scala.NotImplementedError: Composition(false,Constructor(MemberRef(member:A),None),Constructor(MemberRef(member:B),None)) (of class Composition)
- `ucs/normalization/OverlapOfPrimitives.mls`: Unexpected compilation error; Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/normalization/RecordImpliedByClass.mls`: Unexpected exception; scala.NotImplementedError: Record(List((Ident(a),Alias(Wildcard(),Ident(av))), (Ident(b),Alias(Wildcard(),Ident(bv))))) (of class Record)
- `ucs/patterns/BooleansOps.mls`: Unexpected exception; scala.NotImplementedError: Composition(false,Alias(Wildcard(),Ident(a)),Alias(Wildcard(),Ident(b))) (of class Composition)
- `ucs/patterns/ConjunctionPattern.mls`: Unexpected exception; scala.NotImplementedError: Composition(false,Composition(false,Constructor(MemberRef(member:A),None),Constructor(MemberRef(member:A),None)),Constructor(MemberRef(member:B),None)) (of class Composition)
- `ucs/patterns/RecordPattern.mls`: Unexpected exception; scala.NotImplementedError: Record(List((Ident(x),Alias(Wildcard(),Ident(a))), (Ident(y),Alias(Wildcard(),Ident(b))))) (of class Record)
- `ucs/patterns/String.mls`: Unexpected exception; scala.NotImplementedError: Concatenation(Literal(StrLit(0x)),Alias(Wildcard(),Ident(body))) (of class Concatenation)
- `ucs/patterns/where.mls`: Unexpected compilation error; This selection of member 'get' has no resolved target
- `ucs/syntax/Else.mls`: Unexpected compilation error; Resolution error in selection; Instance of class 'Set' does not contain member 'has'
- `ucs/syntax/SimpleUCS.mls`: Unexpected compilation error; This selection of member 'get' has no resolved target

### ups

- `ups/EmptyJunctions.mls`: Unexpected exception; scala.NotImplementedError: Range(IntLit(5),IntLit(3),true) (of class Range)
- `ups/Future.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'Test'
- `ups/LocalPatterns.mls`: Unexpected compilation error; Resolution error in selection; Expected a term; got pattern 'Zero'
- `ups/MatchResult.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'Cross'
- `ups/RecursiveTransformations.mls`: Unexpected exception; scala.NotImplementedError: Negation(Constructor(Capture(MemberRef(member:Bin),term:f),None)) (of class Negation)
- `ups/SimpleTransform.mls`: Unexpected compilation error; Resolution error in application; Function 'area' expected 1 argument, but got 2
- `ups/examples/BasicSeqStackParse.mls`: Unexpected compilation error; This selection of member 'at' has no resolved target
- `ups/examples/Computation.mls`: Unexpected compilation error; This selection of member 'padStart' has no resolved target
- `ups/examples/DoubleTripleList.mls`: Unexpected compilation error; This selection of member 'head' has no resolved target
- `ups/examples/EvaluationContext.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `ups/examples/EvaluationContext2.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `ups/examples/HindleyMilner.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `ups/examples/ListPredicates.mls`: Unexpected compilation error; This selection of member 'length' has no resolved target
- `ups/examples/Negation.mls`: Unexpected compilation error; Resolution error in application; Function 'flatten' expected 1 argument, but got 3
- `ups/examples/PrecedenceClimbStackParse.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'ParseStep'
- `ups/examples/Record.mls`: Unexpected compilation error; Resolution error in application; Function 'bmi' expected 1 argument, but got 2
- `ups/fixpoint/ListFusion.mls`: Unexpected compilation error; This selection of member 'toString' has no resolved target
- `ups/regex/Identifier.mls`: Unexpected compilation error; This selection of member 'forEach' has no resolved target
- `ups/regex/Separation.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'Integer'
- `ups/regex/TailRepetition.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'Zero'
- `ups/syntax/InterestingPatterns.mls`: Unexpected compilation error; Resolution error in member reference; Expected a term; got pattern 'TreeDepth'
- `ups/syntax/PatternBody.mls`: Unexpected compilation error; This selection of member 'toString' has no resolved target

### apps

- `apps/AccountingTest.mls`: Unexpected exception; scala.NotImplementedError: an implementation is missing (`semantics.NewResolver.listen`)
- `apps/CSVTest.mls`: Unexpected compilation error; This selection of member '1' has no resolved target
- `apps/IterTest.mls`: Unexpected compilation error; This selection of member 'reverse' has no resolved target
- `apps/parsing-web-demo/ExamplesTest.mls`: Unexpected compilation error; This selection of member 'sort' has no resolved target
- `apps/parsing/DirectiveTest.mls`: Unexpected compilation error; This selection of member 'display' has no resolved target
- `apps/parsing/LeftRecursion.mls`: Unexpected compilation error; This selection of member 'display' has no resolved target
- `apps/parsing/LexerTest.mls`: Unexpected compilation error; This selection of member 'join' has no resolved target
- `apps/parsing/ParseRuleVisualizerTest.mls`: Unexpected compilation error; Resolution error in application; Class value cannot receive more argument lists.
- `apps/parsing/PrattParsingTest.mls`: Unexpected compilation error; This selection of member 'toString' has no resolved target
- `apps/parsing/RecursiveDescentTest.mls`: Unexpected compilation error; This selection of member 'toString' has no resolved target
- `apps/parsing/RulesTest.mls`: Unexpected exception; java.lang.Exception: Internal Error: Synthetic selections must not enter new resolution

### wasm

- `wasm/Basics.mls`: Unexpected exception; java.lang.AssertionError: assertion failed: Entry and exit cross different lexical resolution scopes
- `wasm/Binaryen.mls`: Unexpected compilation error; Resolution error in selection; Instance of class 'Instance' does not contain member 'exports'
