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
   uses request their appropriate interpretation. Remove definition-selection
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
  rejection of a class-only assignment target. A nested-module parameter capture
  assertion also occurs without the new assignment listener; it is recorded as
  a `:fixme` in `newres/Assignments.mls` for the capture work in stage 3.
- Stage 2 validation: `ctest` passed (45 tests); `dtest newres/` passed (24 files);
  `hkmc2AllTests/test` passed. Regression outputs reviewed for the stage checkpoint.
- Stages 3 and 4 remain pending. In particular, `moduleMembers`, the lexical
  `SelElem` shape shortcut, and the read-side lowering fallbacks are still present.
