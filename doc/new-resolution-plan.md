# New resolution: overloads and deferred opens

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
- Ordinary wildcard references request term interpretation after elaboration;
  constructor targets retain their symbolic interpretation. This traversal will
  be generalized in stage 4. Primitive operators retain their existing implicit
  binding priority, ahead of wildcard sources.
- Stage 3 regressions cover forward and indented modules, both open forms,
  declaration and open orders, outer explicit bindings, parameters, repeated and
  competing sources, distinct receivers sharing one member symbol, chained opens,
  imports, nested captures, class/value and class/function overloads, applied
  constructor patterns, and temporary assignment restoration.
- Deferred uses exposed duplicate shape-listener registration and an unfinished
  constructor-shape cache branch. Listeners are now registered once; cached
  constructors are reused with assertions checking their definition and base.
  An existing applied-pattern test now passes without its `:todo` marker.
- Stage 4 remains pending: the lexical `SelElem` shape shortcut and read-side
  lowering fallbacks still exist. Bare constructor names in patterns still use
  eager classification; `Opens.mls` records this limitation with a `:fixme`
  regression for both open forms. Applied constructor patterns already pass.

- Stage 3 validation: `ctest` passed (45 tests), `dtest newres/` passed
  (26 files), and `hkmc2AllTests/test` passed with the final regression outputs.
  Golden changes remove duplicate debug callbacks and replace the fixed
  applied-pattern exception with its expected result.
