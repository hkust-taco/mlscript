# New-resolution suite migration

## Scope and retained milestone

The first pass tried all 372 active `.mls` files in `basics`, `codegen`, `ucs`,
`ups`, and `apps` with new resolution and strict resolution. The 51 files under
`ucs/staging` are excluded by the test runner and remain unchanged. Counts below
exclude the new shared `.mls` configuration files and new regression tests.

| Suite | Migrated | Retained on existing configuration | Active files |
| --- | ---: | ---: | ---: |
| basics | 55 | 35 | 90 |
| codegen | 61 | 64 | 125 |
| ucs | 50 | 20 | 70 |
| ups | 13 | 58 | 71 |
| apps | 5 | 11 | 16 |
| Total | 184 | 188 | 372 |

Migrated files start with `:.`. Each suite's `.mls` loads the common language
configuration and enables strict resolution; nested directories inherit through
`:..`. The suite defaults disable JS execution so each file retains its original
execution flags. A parser-only test must not acquire runtime execution merely
because its resolution configuration changes.

Blocked files retain their complete original sources and golden outputs. No new
`:todo`, `:fixme`, `:ignore`, or loose-resolution exception hides a migration
failure. Existing expected failures remain visible. The inventory below records
trial observations, not newly accepted failures.

The five migrated application worksheets still import compilation fixtures in
their existing mode. This is caller-side migration, not a claim that all imported
application implementations use new resolution. The 20 application compilation
fixtures and four `mlscript-compile/ups` fixtures need a subsequent dependency-ordered
migration. Their shared consumers make a blanket flag change inappropriate for
this first milestone.

The unfinished WASM/type-erasure changes predate this migration and are retained.
In particular, the typed-constructor-field capture assertion is still outstanding.
Method calls across REPL blocks remain assigned to the other branch.

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
   construction, inheritance, and function-result member lookup. This does not
   implement generic substitution or missing type-argument validation.
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

Evidence: `basics/LiteralSelection.mls` fails on `arr.1` and `obj.a` because
tuple and record member lookup remains unimplemented in `TupleShape` and
`IntroShape`. The current `MemberInfo` requires a `BlockMemberSymbol`, which a
structural field need not have. `codegen/ImportJSModule.mls`, `Pwd.mls`, and many
app worksheets instead have opaque external results with no member shapes at all.

**Question:** should ordinary member selection on an opaque external value be
accepted dynamically, or require a declaration/explicit dynamic selection?
This is different from a known record's structural member.

**Proposal:** preserve strict resolution for ordinary source selections. Add a
member-target representation distinguishing nominal definitions from structural
fields, and an explicit opaque/dynamic category where the language authorizes
it. Structural targets carry their field/index path and value-shape publisher;
they must not invent nominal symbols or discard the selected value's provenance.
Resolve record overwrites and spreads in source order, independently of listener
arrival order. Lowering consumes those targets without doing lookup. Publish
external signatures through the same shape infrastructure; keep explicitly
dynamic operations on a dedicated path.

Acceptance cases: duplicate record fields, spreads arriving late, tuple indices,
field values used as receivers, field assignment, missing fields, and JS imports.
Decide whether wildcard opens accept structural records as part of this work;
do not silently treat an unsupported structural open as an empty module.

### 2. Annotations that affect elaboration

Evidence: `codegen/NoInline.mls` warns that `@noInline` has no effect and then
inlines `bar`. `Elaborator.annot` still uses eager `trm.symbol`. The trial of
`codegen/Generators.mls` exceeded the 25-second test limit; lost generator
recognition is a concrete suspect, not yet a proven explanation of that timeout.

**Question:** may elaboration-affecting annotations be obtained through forward
aliases and wildcard opens, just like other symbolic references?

**Proposal:** yes. Resolve annotation identity through completed symbolic
candidates and schedule dependent elaboration after that prerequisite is known.
Separate annotations needed to elaborate a body (`generator`, `async`) from
metadata only consumed later (`noInline`, `tailrec`). Diagnose ambiguity or a
dependency cycle explicitly. Do not recognize annotations by spelling, inspect
incomplete definitions, or call `resolvedSym` during elaboration.

Acceptance cases: direct, qualified, explicit-open, wildcard-open, shadowed,
forward, ambiguous, and cyclic annotation references. Check emitted function
kind and optimization behavior, not only final values. This should be addressed
first because it can change valid program behavior without an ordinary error.

### 3. Pattern transfer and synthesized references

Evidence: new shape propagation lacks record, conjunction, negation, string
concatenation, and transformation cases. Examples include
`ucs/general/BooleanPatterns.mls`, `patterns/String.mls`, and
`normalization/RecordImpliedByClass.mls`. Tuple bindings currently publish no
shapes. `CompiledQualifiedConstructors.mls` reaches `Term.mkClone` with a
`NewSel`; `CompiledClassPatterns.mls` reaches it with a `MemberRef`. Many UPS
failures combine these gaps with synthesized matcher selections.

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
structure with the existing tests. `ups/examples/HindleyMilner.mls` also timed
out during the trial and needs an isolated reproducer before assigning its cause.

### 4. Declared interfaces versus inferred values

Evidence: the prior WASM `Basics` failure mixes a nominal annotated receiver with
an untyped constructor field carrying a different capture context.
`codegen/CurriedClassInheritance.mls` and `ParamClasses.mls` also expose capture
or receiver-shape problems; they are not all necessarily the same bug.

**Question:** does `b: Base` restrict member lookup to Base's declared interface,
or may concrete call arguments expose subclass-only members? This remains the
unanswered question from the preceding phase.

**Proposal:** use the declared interface for member availability, preserving
virtual dispatch. Keep value-flow provenance separate from that interface so
reading a field cannot feed constructor entry marks into an unrelated function
exit. Publish declared parameter, result, and field types consistently, including
functions with no observed calls. Never fix the assertion by dropping marks.

Acceptance cases: an unused annotated function, an unannotated constructor field,
subclass overrides, inherited fields, curried constructors, nested captures, and
generic aliases. Coordinate REPL method cases with the other branch.

### 5. Dynamic construction and foreign callable classes

Evidence: `basics/DynamicInstantiation.mls` and `codegen/ImportJSClass.mls` reach
static class-lowering assumptions for explicitly dynamic constructions.
`PredefUsage.mls` calls JavaScript's `String` as a function, while its current
declaration supplies only a module interpretation. Bare MLscript classes also
reject old empty-call syntax, as intended by the earlier migration.

**Question:** how should foreign declarations expose both call and constructor
capabilities, without making every module or bare class implicitly callable?

**Proposal:** give foreign declarations explicit callable/constructible
capabilities using the existing overload interpretation mechanism. Lower
explicitly dynamic construction directly as dynamic IR, distinct from static
class construction. Keep static `new` on the listener-resolved class path.
Change test syntax only where that preserves the test's intent; tests explicitly
about callable JS constructors must not be rewritten to avoid that feature.

Acceptance cases: imported JS classes, callable-and-constructible externals,
plain MLscript classes, companion values, dynamic constructor expressions, and
errors when a selected interpretation lacks the required capability.

## Remaining implementation work, not new semantic decisions

- Argument-spread distribution now uses `TupleShape` candidates with selected
  subshapes for each spread. Tuple producers listen for all combinations; `zipArgs`
  checks their expanded counts and preserves capture marks for fixed arguments and
  residual rest tuples. Marks accumulate on each segment and are applied when a
  consumer accesses its fields, as with member selection.
  `newres/SpreadCalls.mls` covers nested and delayed spreads, multiple alternatives,
  fixed arguments after spreads, rest forwarding, captures, curried calls and
  constructors, and recursive forwarding. Repeated producers in the same spread
  context widen that spread to an explicit unknown-length tuple shape, preserving
  known surrounding fields; `basics/LazySpreads.mls` covers recursive lazy tuples.
  Unknown lengths get a distinct diagnostic instead of a fabricated arity mismatch.
  Functions can consume a known prefix and forward an unknown-length remainder to
  a rest parameter. The broader call-site correlation limitation remains tracked
  in `newres/CallSiteShapes.mls`, including a rest-forwarding case. Further
  constructor/returned-function fixes should be driven by specific failures,
  rather than replacing existing deferral.
- Audit assignments to member symbols and definition initializers. The trial
  reaches unimplemented direct member-reference shape cases and missing
  assignment lowering in several mutation tests.
- Add transfer rules for result-bearing control flow, handlers, and quotation
  where the resolver currently has no shape rule. Preserve the established
  capture model and the boundary between elaboration and lowering.
- Diagnose cyclic wildcard/module forwarding without recursive listener
  registration overflowing the stack; `basics/CyclicModuleForwarders.mls` is
  a small existing reproducer.
- Preserve source origins in synthesized references and diagnostics. Some
  migrated error cases now report a definition rather than a use site, or lose
  a location. These need attention without changing the chosen symbol.

## Execution order and completion gates

1. **Retain this measured batch.** Run compilation fixtures, main difftests,
   application difftests, and the aggregate suite. Review output changes; keep
   nonmigrated files intact. WASM `Basics` retains its previous configuration
   pending the capture fix, keeping this partial migration green.
2. **Fix annotation prerequisites and cycle handling.** Minimize both timeout
   cases. Re-enable generator/annotation tests only after checking emitted IR/JS.
3. **Implement structural targets and external signatures.** Agree on opaque
   selection policy, then migrate records, tuples, mutation, and JS interop in
   small batches. Re-run affected negative tests as well as successful programs.
4. **Complete pattern transfers and reference preservation.** Start with UCS
   conjunction/record/tuple cases, then compiled class patterns, then recursive
   and transforming UPS cases. Keep fixed-point behavior tested independently
   from matcher code generation.
5. **Complete type/interface and call validation.** Resolve the pending interface
   question, finish declared result/field shapes, port module/generic checks, and
   finish the WASM migration. Keep cross-block method work coordinated externally.
6. **Migrate shared compilation fixtures from leaves upward.** Begin with the
   four UPS fixtures; then application parsing data types, lexer, parser helpers,
   and entry points. Rebuild `.mjs` dependencies before each worksheet batch.
   Verify cache/import behavior across old and new consumers during transition.
7. **Remove the remaining legacy suite configurations.** Require no new failure
   suppressions, no lost negative diagnostics, reviewed goldens, and a successful
   `hkmc2AllTests/test`. Commit code and golden outputs together under the agent's
   identity once that gate is met.

## Validation

- `ctest`: 45 compilation tests pass.
- `catest`: 20 application compilation tests pass in their existing mode.
- Main `dtest` after retaining the migrated batch: 681 tests pass.
- `adtest` after restoring deferred files: all 18 tests pass (16 worksheets and
  two shared configuration files).
- The added `newres/TypeApplications.mls` regression passes separately.
- `hkmc2AllTests/test` passes after restoring WASM `Basics.mls` to its previous
  configuration. All 22 WASM tests pass; the final main test run passes 685 tests.
  The capture assertion remains a migration blocker, not an accepted test failure.
- This checkpoint includes the latest golden outputs and records the outstanding
  migration blocker. No trial-generated application report changes remain.

## Deferred-file inventory

The following are the first observed trial failures, which may be symptoms rather
than root causes. Each path is relative to `hkmc2/shared/src/test/mlscript/`.
The files themselves retain the pre-trial configuration and output.

### basics

- `basics/BadAssignments.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: SelfRef(globalThis:globalThis) (of class SelfRef)
- `basics/BadModuleUses.mls`: Unexpected lack of compilation or type error; [COMPILATION ERROR] This selection of member 'mtd' has no resolved target
- `basics/BadOverloading.mls`: Unexpected lack of compilation or type error; [COMPILATION ERROR] Not yet supported: overloading of function 'Foo'
- `basics/BadTypeClasses.mls`: Unexpected lack of compilation or type error; [COMPILATION ERROR] Resolution error in member reference; Value symbol 'someInt' cannot be used as a type
- `basics/Classes.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'id' has no resolved target
- `basics/CompanionModules_Classes.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'C' cannot be called like a function.
- `basics/CompanionModules_Functions.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'foo' cannot be called like a function.
- `basics/CyclicModuleForwarders.mls`: Unexpected exception; /!!!\ Uncaught error: java.lang.StackOverflowError
- `basics/DynamicFields.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Instance of class constructor 'DynCtor' does not contain member 'dynField'
- `basics/DynamicInstantiation.mls`: Unexpected internal error; [INTERNAL ERROR] Compiler reached an unexpected state at 'Lowering.scala:453': Unexpected class term shape
- `basics/DynamicSelection.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/ExplicitLabels.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Integer literal does not contain member 'break'
- `basics/FunDefs.mls`: Unexpected exception; /!!!\ Uncaught error: java.lang.StackOverflowError
- `basics/GenericClasses.mls`: Unexpected lack of compilation or type error; 
- `basics/Inheritance.mls`: Unexpected lack of error to fix; [COMPILATION ERROR] This selection of member 'x' has no resolved target
- `basics/LiteralSelection.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/MiscArrayTests.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/ModuleMethods.mls`: Unexpected lack of compilation or type error; [COMPILATION ERROR] Cannot use a value of type 'Int' at an unrelated type 'module M'
- `basics/MultiParamListClasses.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Instance of class constructor 'Foo' cannot receive more argument lists.
- `basics/MutArr.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/MutRcd.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/MutVal.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/New.mls`: Unexpected lack of warnings; [COMPILATION ERROR] Resolution error in application; Class 'Foo' cannot receive more argument lists.
- `basics/NewMut.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Instance of class 'Foo' does not contain member 'y'
- `basics/NewlineOps.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'length' has no resolved target
- `basics/NewlineSels.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/ObjectExtensions.mls`: Unexpected internal error; [INTERNAL ERROR] Compiler reached an unexpected state at 'Lowering.scala:453': Unexpected class term shape
- `basics/OpenIn.mls`: Unexpected compilation error; [COMPILATION ERROR] Builtin '~' is not a binary operator
- `basics/Overloading.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'Foo' cannot be called like a function.
- `basics/PrefixOps.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in member reference; 
- `basics/Puns.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Record(List((Ident(a),Alias(Wildcard(),Ident(x))))) (of class Record)
- `basics/Records.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `basics/StrTest.mls`: Unexpected lack of compilation or type error; [COMPILATION ERROR] Unexpected term form in expression position (negation type)
- `basics/Underscores.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'f' has no resolved target
- `basics/ValMemberSymbols.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Integer literal cannot receive more argument lists.

### codegen

- `codegen/Arrays.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/AuxiliaryConstructors.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/BadGenerators.mls`: Unexpected warning; [WARNING] This annotation has no effect.
- `codegen/BadNew.mls`: Unexpected internal error; [INTERNAL ERROR] Compiler reached an unexpected state at 'Lowering.scala:453': Unexpected class term shape
- `codegen/BadOpen.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Module 'Foo' does not contain member 'y'
- `codegen/BadThis.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'clearInterval' has no resolved target
- `codegen/BasicTerms.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Integer literal cannot be called like a function.
- `codegen/BlockPrinter.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/ClassMatching.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/ConfigDirective.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'call' has no resolved target
- `codegen/ConsoleLog.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'log' has no resolved target
- `codegen/CurriedClassInheritance.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Instance of class constructor 'Bar' cannot receive more argument lists.
- `codegen/CurriedClasses.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in object instantiation; Class 'A' expected 1 argument, but got 1
- `codegen/Do.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'hello' has no resolved target
- `codegen/ErasedTypes.mls`: Unexpected warning; [WARNING] This annotation has no effect.
- `codegen/FirstClassFunctionTransform.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/Generators.mls`: New-resolution trial exceeded the 25-second runner timeout.
- `codegen/Getters.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'whoops' has no resolved target
- `codegen/Hygiene.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; String literal does not contain member 'foo'
- `codegen/ImportAlias.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'inc' has no resolved target
- `codegen/ImportExample.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/ImportJSClass.mls`: Unexpected internal error; [INTERNAL ERROR] Compiler reached an unexpected state at 'Lowering.scala:453': Unexpected class term shape
- `codegen/ImportJSModule.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'greet' has no resolved target
- `codegen/ImportMLs.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Module 'Option' does not contain member 'oops'
- `codegen/ImportMLsJS.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'isDefined' has no resolved target
- `codegen/ImportedOps.mls`: Unexpected compilation error; [COMPILATION ERROR] Builtin '~' is not a binary operator
- `codegen/Inliner.mls`: Unexpected warning; [WARNING] This annotation has no effect.
- `codegen/InterleavedRecords.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/Misc.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/ModuleMethods.mls`: Unexpected lack of compilation or type error; 
- `codegen/Modules.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'None' cannot be called like a function.
- `codegen/NestedClasses.mls`: Unexpected internal error; [INTERNAL ERROR] Compiler reached an unexpected state at 'Lowering.scala:453': Unexpected class term shape
- `codegen/NestedScoped.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/NoFreeze.mls`: Unexpected compilation error; [COMPILATION ERROR] Assignment requires an unambiguous term member
- `codegen/NoInline.mls`: Unexpected warning; [WARNING] This annotation has no effect.
- `codegen/NoModuleCheck.mls`: Unexpected lack of compilation or type error; [COMPILATION ERROR] Resolution error in object instantiation; 
- `codegen/ObjectMethodDebinding.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'foo' has no resolved target
- `codegen/Open.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; String literal does not contain member 'length'
- `codegen/OpenWildcard.mls`: Unexpected compilation error; [COMPILATION ERROR] Wildcard-open reference 'None' is ambiguous
- `codegen/ParamClasses.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/PartialApps.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Tuple literal cannot receive more argument lists.
- `codegen/PlainClasses.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Class 'Foo' cannot receive more argument lists.
- `codegen/PredefUsage.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'String' cannot be called like a function.
- `codegen/PrivateMembers.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'y' has no resolved target
- `codegen/Pwd.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'pop' has no resolved target
- `codegen/QQImport.mls`: Unexpected runtime error; [RUNTIME ERROR] ReferenceError: Term is not defined
- `codegen/Quasiquotes.mls`: Unexpected runtime error; [RUNTIME ERROR] ReferenceError: Term is not defined
- `codegen/RandomStuff.mls`: Unexpected exception; /!!!\ Uncaught error: java.lang.StackOverflowError
- `codegen/ReboundLet.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/RuntimeUsage.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Class 'Str' does not contain member 'leave'
- `codegen/SanityChecks.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Function literal expected 1 argument, but got 0
- `codegen/ScopedBlocks.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'Foo' cannot receive more argument lists.
- `codegen/ScopedBlocksAndHandlers.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Handle(h,Capture(MemberRef(member:Effect),term:f),List(),class:Handler$h$,List(HandlerTermDefinition(k,TermDefinition(Fun,member:perform,term:Handler$h$/perform,List(...
- `codegen/Scoping.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/SelfReferences.mls`: Unexpected lack of compilation or type error; 
- `codegen/SetStmt.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `codegen/Spreads.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Function 'foo' expected 4 arguments, but got 1
- `codegen/This.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'a' has no resolved target
- `codegen/ThisCallVariations.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'call' has no resolved target
- `codegen/ThisCalls.mls`: Unexpected lack of compilation or type error; 
- `codegen/Throw.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Class 'Error' cannot receive more argument lists.
- `codegen/TraceLog.mls`: Unexpected exception; /!!!\ Uncaught error: java.lang.StackOverflowError
- `codegen/UnitValue.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'log' has no resolved target
- `codegen/While.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Integer literal cannot be called like a function.

### ucs

- `ucs/examples/BinarySearchTree.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/examples/EitherOrBoth.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection of type None; Object 'None' cannot be used as a type
- `ucs/examples/LeftistTree.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/examples/ListFold.mls`: Unexpected compilation error; [COMPILATION ERROR] Builtin '~' is not a binary operator
- `ucs/examples/ULC.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/general/BooleanPatterns.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Composition(false,Negation(Literal(IntLit(2))),Negation(Literal(IntLit(3)))) (of class Composition)
- `ucs/hygiene/HygienicBindings.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Class 'Error' cannot receive more argument lists.
- `ucs/normalization/Deduplication.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'length' has no resolved target
- `ucs/normalization/InheritanceNormalization.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Composition(false,Constructor(MemberRef(member:A),None),Constructor(MemberRef(member:B),None)) (of class Composition)
- `ucs/normalization/OverlapOfPrimitives.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Module 'String' cannot receive more argument lists.
- `ucs/normalization/RecordImpliedByClass.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Record(List((Ident(a),Alias(Wildcard(),Ident(av))), (Ident(b),Alias(Wildcard(),Ident(bv))))) (of class Record)
- `ucs/patterns/BooleansOps.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Composition(false,Alias(Wildcard(),Ident(a)),Alias(Wildcard(),Ident(b))) (of class Composition)
- `ucs/patterns/CompiledClassPatterns.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Add) (of class hkmc2.semantics.Term$MemberRef)
- `ucs/patterns/CompiledQualifiedConstructors.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: NewSel(SimpleRef(Inner),Ident(Wrapped),None) (of class hkmc2.semantics.Term$NewSel)
- `ucs/patterns/ConjunctionPattern.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Composition(false,Composition(false,Constructor(MemberRef(member:A),None),Constructor(MemberRef(member:A),None)),Constructor(MemberRef(member:B),None)) (of class Comp...
- `ucs/patterns/RecordPattern.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Record(List((Ident(x),Alias(Wildcard(),Ident(a))), (Ident(y),Alias(Wildcard(),Ident(b))))) (of class Record)
- `ucs/patterns/String.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Concatenation(Literal(StrLit(0x)),Alias(Wildcard(),Ident(body))) (of class Concatenation)
- `ucs/patterns/where.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ucs/syntax/Else.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; Instance of class 'Set' does not contain member 'has'
- `ucs/syntax/SimpleUCS.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'get' has no resolved target

### ups

- `ups/BasicStackPatterns.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: UnresolvedRef(List(MemberRef(member:Stack)),Ident(x)) (of class hkmc2.semantics.Term$UnresolvedRef)
- `ups/EmptyJunctions.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: Range(IntLit(5),IntLit(3),true) (of class Range)
- `ups/Future.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in member reference; Pattern symbol 'Test' cannot be used as a type
- `ups/LocalPatterns.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in selection; 
- `ups/MatchResult.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in member reference; 
- `ups/RecursiveTransformations.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(b) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/SimpleConjunction.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:observeLeft) (of class hkmc2.semantics.Term$MemberRef)
- `ups/SimpleTransform.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(a) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/TransformFree.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/UpsBugsBacklog.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(c) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/examples/BasicSeqStackParse.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `ups/examples/BasicStackParse.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: UnresolvedRef(List(MemberRef(member:Stack)),Ident(::)) (of class hkmc2.semantics.Term$UnresolvedRef)
- `ups/examples/Computation.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(f) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/examples/DnfCnf.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Or) (of class hkmc2.semantics.Term$MemberRef)
- `ups/examples/DoubleOrSum.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:addWithPrint) (of class hkmc2.semantics.Term$MemberRef)
- `ups/examples/DoubleTripleList.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: UnresolvedRef(List(MemberRef(member:Stack), MemberRef(member:annotations)),Ident(Nil)) (of class hkmc2.semantics.Term$UnresolvedRef)
- `ups/examples/EvaluationContext.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `ups/examples/EvaluationContext2.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `ups/examples/Extraction.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: NewSel(MemberRef(member:Option),Ident(Some),None) (of class hkmc2.semantics.Term$NewSel)
- `ups/examples/Flatten.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: UnresolvedRef(List(MemberRef(member:Stack), MemberRef(member:annotations)),Ident(::)) (of class hkmc2.semantics.Term$UnresolvedRef)
- `ups/examples/HindleyMilner.mls`: New-resolution trial exceeded the 25-second runner timeout.
- `ups/examples/ListPredicates.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(list) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/examples/Negation.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/examples/PrecedenceClimbStackParse.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: UnresolvedRef(List(MemberRef(member:Stack)),Ident(::)) (of class hkmc2.semantics.Term$UnresolvedRef)
- `ups/examples/Record.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(weight) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/examples/TupleSpread.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/Diagnostics.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/FixedPointPatterns.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/IndirectRecursion.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/ListFusion.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'toString' has no resolved target
- `ups/fixpoint/MoreAlternatives.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/NonCatchAll.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/RecursionAlternatives.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/SimpleExample.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(a) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/fixpoint/UnsupportedShapes.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/nondeterminism/BitArithmetic.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:And) (of class hkmc2.semantics.Term$MemberRef)
- `ups/nondeterminism/EvenOddTree.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:B) (of class hkmc2.semantics.Term$MemberRef)
- `ups/nondeterminism/LaRbTree.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:A) (of class hkmc2.semantics.Term$MemberRef)
- `ups/parametric/EtaConversion.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Zero) (of class hkmc2.semantics.Term$MemberRef)
- `ups/parametric/HigherOrderPattern.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Int) (of class hkmc2.semantics.Term$MemberRef)
- `ups/parametric/ListLike.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/parametric/Nullable.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/recursion/BitSeq.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Pair) (of class hkmc2.semantics.Term$MemberRef)
- `ups/recursion/BitTree.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Pair) (of class hkmc2.semantics.Term$MemberRef)
- `ups/recursion/LeafEvenOddTree.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:B) (of class hkmc2.semantics.Term$MemberRef)
- `ups/recursion/NatBox.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Box) (of class hkmc2.semantics.Term$MemberRef)
- `ups/recursion/NullTree.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Pair) (of class hkmc2.semantics.Term$MemberRef)
- `ups/recursion/SignBox.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Box) (of class hkmc2.semantics.Term$MemberRef)
- `ups/regex/EmailAddress.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:UserNameLetter) (of class hkmc2.semantics.Term$MemberRef)
- `ups/regex/Identifier.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'forEach' has no resolved target
- `ups/regex/Separation.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(t) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/regex/TailRepetition.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in member reference; 
- `ups/specialization/SimpleList.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Box) (of class hkmc2.semantics.Term$MemberRef)
- `ups/specialization/SimpleLiterals.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:observeZero) (of class hkmc2.semantics.Term$MemberRef)
- `ups/syntax/InterestingPatterns.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)
- `ups/syntax/MixedParameters.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: MemberRef(member:Bit) (of class hkmc2.semantics.Term$MemberRef)
- `ups/syntax/PatternBody.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: UnresolvedRef(List(MemberRef(member:Stack)),Ident(::)) (of class hkmc2.semantics.Term$UnresolvedRef)
- `ups/transformation/BindingLess.mls`: Unexpected exception; /!!!\ Uncaught error: scala.MatchError: SimpleRef(x) (of class hkmc2.semantics.Term$SimpleRef)

### apps

- `apps/AccountingTest.mls`: Unexpected exception; /!!!\ Uncaught error: scala.NotImplementedError: an implementation is missing
- `apps/CSVTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member '1' has no resolved target
- `apps/IterTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'reverse' has no resolved target
- `apps/parsing-web-demo/ExamplesTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'sort' has no resolved target
- `apps/parsing/DirectiveTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'display' has no resolved target
- `apps/parsing/LeftRecursion.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'display' has no resolved target
- `apps/parsing/LexerTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'join' has no resolved target
- `apps/parsing/ParseRuleVisualizerTest.mls`: Unexpected compilation error; [COMPILATION ERROR] Resolution error in application; Class 'Error' cannot receive more argument lists.
- `apps/parsing/PrattParsingTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'toString' has no resolved target
- `apps/parsing/RecursiveDescentTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'toString' has no resolved target
- `apps/parsing/RulesTest.mls`: Unexpected compilation error; [COMPILATION ERROR] This selection of member 'display' has no resolved target
