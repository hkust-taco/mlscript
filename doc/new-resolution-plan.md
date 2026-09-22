# New resolution: overloads and deferred opens

**Status: all five planned stages complete.** The final review and regression
coverage are recorded below.

Resolution owns member discovery and definition selection. Lowering consumes those
decisions; it must not recover missing decisions by inspecting overload sets or
partially elaborated definitions. A member overload set, its selected definition,
and the shape of its value are separate pieces of information.

## Intended wildcard-open semantics

For `newResolution`, lookup first searches the complete chain of ordinary `Ctx`
environments. Explicit bindings, including member definitions and selective opens,
always take precedence over wildcard opens, including wildcard opens in an inner
scope. Only a name with no explicit binding is looked up through wildcard opens.

`Ctx` carries the currently wildcard-opened members. Such a lookup creates an
`UnresolvedRef` and registers listeners on those opened members. As their shapes
arrive, matching members are propagated into the reference's `resolvedMembers`.
A pending shape is not evidence that a member is absent. Candidates retain their
receiver and capture context; module completion must not change lexical priority.

## Stages

1. **Record the contracts and update the language reference.**
   Document explicit-binding precedence and deferred wildcard lookup. Keep this
   plan current with implementation progress and validation results.
2. **Make term selection a resolver responsibility.**
   Centralize selection after symbol completion and record the selected definition
   separately from propagated value shapes. Register assignment term resolution,
   including synthesized assignments, and remove assignment lowering's member
   fallback. Preserve receiver evaluation order and avoid reading the assigned
   value to determine its target.
3. **Implement deferred opens.**
   Add wildcard-open context entries and `UnresolvedRef`. Search explicit bindings
   before wildcard sources. Use normal shape resolution for selective opens too;
   remove `moduleMembers` and eager syntax/definition-table lookup in new mode.
   Preserve receivers and marks through captures, nesting, imports, and forward
   references. Resolve competing distinct members without choosing by callback
   arrival order. Lowering can report ambiguity from the accumulated candidates;
   reporting ambiguity does not entail performing name resolution in lowering.
4. **Enforce the phase boundary for all uses.**
   Ensure ordinary value uses request term resolution, while class and pattern
   uses request their appropriate interpretation. Replace eager bare-pattern name
   classification so opened constructors are recognized without syntax lookup.
   Remove definition-selection
   fallbacks from `MemberRef`/`NewSel` lowering and audit `SelElem` shape seeding.
   Distinguish unresolved work from diagnosed errors and successful selections;
   assert internal invariants instead of silently guessing. Audit backend class
   storage against resolved identities and live IR definitions.
5. **Validate and commit.**
   Cover forward definitions, both module-body forms, explicit-vs-wildcard
   precedence across scopes and declaration orders, competing opens, captures,
   imports, overloaded class/term uses, and ordinary/synthesized assignments.
   Run `ctest` before focused tests, then `hkmc2AllTests/test`. Review diagnostics
   and golden changes for semantic correctness and commit the resulting outputs
   with the implementation under the agent's identity.

## Progress

- Stage 1 complete: plan recorded and wildcard lookup rules added to the language
  reference. These are the intended rules; stage 3 implements them.
- Stage 2 implemented: `listenTerm` records the definition selected after symbol
  completion, independently of its value shapes. Source and synthesized
  assignments request term resolution. Assignment lowering no longer selects
  from `resolvedMembers`. Declared values publish no implementation shape but
  still supply a selected definition.
- Stage 2 regressions cover a forward module definition, overloaded field writes,
  backtracking restoration, declared fields, receiver/RHS evaluation order, and
  rejection of a class-only assignment target.
- Stage 2 validation: `ctest` passed (45 tests); `dtest newres/` passed (24 files);
  `hkmc2AllTests/test` passed. Regression outputs reviewed for the stage checkpoint.
- Capture follow-up: module/object references no longer introduce their own exit
  marks. Enclosing function and receiver-context marks remain intact. This fixes
  the nested-module assertion in `newres/Assignments.mls`; its `:fixme` is removed.
  `newres/ModuleCaptures.mls` covers nested and escaping modules, objects, getters,
  methods, and separation of captures from distinct calls. Validation passed:
  `ctest` (45 tests), `dtest newres/` (25 files), and `hkmc2AllTests/test`.
- Stage 3 implemented: contexts retain wildcard sources and search the full
  explicit environment chain first. `UnresolvedRef` listens to the sources and
  retains each candidate's receiver; lowering reports missing or ambiguous
  candidates without doing resolution. Selective opens now use selection
  listeners, and `moduleMembers` is removed. Import aliases propagate shapes.
- Primitive operators retain their existing implicit binding priority, ahead of
  wildcard sources. The initial stage-3 post-elaboration traversal has been
  replaced by the contextual elaboration described below.
- Stage 3 regressions cover forward and indented modules, both open forms,
  declaration and open orders, outer explicit bindings, parameters, repeated and
  competing sources, distinct receivers sharing one member symbol, chained opens,
  imports, nested captures, class/value and class/function overloads, applied
  constructor patterns, and temporary assignment restoration.
- Deferred uses exposed duplicate shape-listener registration and an unfinished
  constructor-shape cache branch. Listeners are now registered once; cached
  constructors are reused with assertions checking their definition and base.
  An existing applied-pattern test now passes without its `:todo` marker.
- At the stage-3 checkpoint, bare constructor names still used eager classification;
  `Opens.mls` recorded this with a `:fixme` regression for both open forms. The
  final stage-4 work below removes that limitation and the marker.

- Stage 3 validation: `ctest` passed (45 tests), `dtest newres/` passed
  (26 files), and `hkmc2AllTests/test` passed with the final regression outputs.
  Golden changes remove duplicate debug callbacks and replace the fixed
  applied-pattern exception with its expected result.

- Contextual interpretation is now threaded through `term` and `subterm`:
  ordinary term uses request resolution during elaboration; class and pattern
  targets retain their specialized interpretation, and type positions do not
  request runtime values. `resolveOpenUses` and its second tree walk are removed.
- `term` requires an explicit interpretation; only `subterm` defaults to `Trm`.
  This is a deliberate exception to the usual rule against defaults: ordinary
  recursive operands stay concise, while symbolic positions and transparent
  wrappers explicitly specify or forward the interpretation. The enum cases are
  imported as `Trm`, `Clss`, `Ptrn`, and `Tpe`. Other helpers require it explicitly.
  An implicit context was avoided because a target's interpretation must not leak
  into its value arguments or selection prefixes.
- The resolver records direct definition references without demanding their value
  shapes; overload sets still resolve through listeners. Failed term selection
  marks the reference erroneous, avoiding repeated and secondary diagnostics.
- `Interpretations.mls` covers forward value uses, parenthesized and locally opened
  class targets, constructor arguments, pattern guards, and type-only references
  in signatures, aliases, type arguments, and ascriptions. Bare-pattern lookup and
  lowering/lexical shortcuts were handled in the subsequent stage-4 checkpoints.
- Contextual-interpretation validation: `ctest` passed (45 tests),
  `dtest newres/` passed (27 files), and the final `hkmc2AllTests/test` passed.
  Existing runtime outputs are unchanged; reviewed golden updates record the
  additional resolution requests made during elaboration.

- Stage 4, receiver and lowering checkpoint: lexical `SelElem` references now
  register ordinary selection listeners, just like selective opens. `SelfRef`
  obtains its base shape through definition-completion listeners, handling both
  pending and already available definitions and retaining inherited shapes.
  The resolver caches these base shapes; no new mutable symbol state is needed.
- `MemberRef` and `NewSel` lowering now consume `resolvedTargets` exclusively.
  Diagnosed references produce the error result; missing targets produce an
  unresolved-target diagnostic; strict ambiguous selections report all selected
  definitions. Existing non-strict dynamic selection behavior is preserved.
- `ReceiverResolution.mls` covers forward lexical members, overloaded class/value
  names, nested receiver capture, later selective opens, and inherited selection.
  Ambiguity diagnostics retain owner context and now point at selected definition
  names rather than the entire overload declaration.
- Reviewed the existing independent class storage: name reservation records live
  IR class symbols, and class and term slots remain separate. No storage change
  is needed for this checkpoint.
- The receiver/lowering checkpoint left constructor-pattern resolution for a
  separate regression review. That work is discharged below. The agreed alias
  rule for new resolution uses capitalization, replacing lookup-dependent binding.
- Receiver/lowering validation: `ctest` passed (45 tests), the focused receiver
  regression passed, and final `hkmc2AllTests/test` passed (including 659 diff
  tests). Reviewed the four changed ambiguity snapshots and the new regression's
  runtime outputs.

## Final stage-4 review

- Bare, applied, selected, and infix constructor patterns now use one resolver
  entry point. It waits for member completion, selects the pattern/class/object
  interpretation independently of term overloads, and accumulates candidates.
  Full and string-prefix pattern lowering share candidate validation. Lowering
  diagnoses multiple targets and distinct wildcard receivers, including
  receivers exposing the same member symbol. Missing targets and already reported
  errors are handled separately; no candidate is chosen by callback order.
- Bare uppercase names use ordinary contextual lookup. As agreed, `p as name`
  binds a lowercase name and `p as Name` matches an uppercase constructor; an
  unknown uppercase name is an error. The language reference documents this rule
  and applies wildcard precedence to pattern interpretations too.
- Constructor shape propagation handles aliases, chains, and nominal inheritance,
  so bindings receive matching scrutinee shapes. Guards and literal tests may
  conservatively retain shapes. This does not attempt to implement all unfinished
  shape inference for other pattern forms, such as tuple bindings or conjunction
  outputs. Constructor calls and explicit `new` now share inherited member lookup,
  preserving inherited capture marks; this also discharges three existing
  inheritance `:fixme` cases.
- Reentrant member-completion callbacks now see the completed state immediately,
  rather than appending to the listener buffer currently being traversed.
- Symbol queries consume recorded new-resolution targets, including captures.
  Synthesized runtime constructors carry explicit resolved class symbols, which
  lowering now accepts directly. Ambiguous `new` targets produce diagnostics.
- The `selfShapes` cache is keyed only by inner symbol, with assertions that
  repeated notifications agree on the definition and extension.
- Backend review: class storage continues to use live IR identities and separate
  slots for class/term overloads. The new pattern path retains the selected class
  identity through lowering; imported overload patterns exercise the exported
  class slots. No backend storage workaround was added.

| Planned contract | Regression coverage |
| --- | --- |
| Explicit bindings beat wildcard opens across scopes and declaration orders | `Opens.mls` |
| Deferred forward definitions, both module-body forms, captures and imports | `Opens.mls`, `ModuleCaptures.mls`, `ReceiverResolution.mls`, `OverloadedClassImports.mls` |
| Class/function and class/value overloads, storage and live class identities | `OverloadedClasses.mls`, `OverloadedClassValues.mls`, `OverloadedClassImports.mls` |
| Ordinary and synthesized assignments, evaluation order and restoration | `Assignments.mls`, `Opens.mls` |
| Contextual term/class/pattern/type interpretation | `Interpretations.mls`, `ConstructorResolution.mls` |
| Bare/applied/selected/infix patterns, objects, aliases, named patterns and pattern parameters | `ConstructorResolution.mls`, `Opens.mls`, `PatMat.mls` |
| Ambiguity independent of open order, repeated sources and distinct receivers | `ConstructorResolution.mls`, `Opens.mls` |

## Final validation

- `ctest`: 45 tests passed.
- `dtest newres/`: 29 tests passed; the final added pattern-parameter regression
  also passed its focused run.
- Final `hkmc2AllTests/test`: all suites passed, including 660 diff tests.
- Reviewed the golden changes: bare opens and constructor aliases now succeed;
  inherited member regressions now return their expected values; ambiguity and
  invalid-pattern cases produce diagnostics. Two JS snapshots omit `safeCall`
  now that symbol queries expose the already recorded function targets.
- Legacy-resolution diagnostic spans are unchanged. Implementation, language
  reference, regression inputs, and final golden outputs are committed together.
