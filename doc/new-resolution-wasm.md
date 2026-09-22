# New-resolution WASM investigation

## Findings and immediate fix

WASM arithmetic and ordinary method calls work with new resolution. The
`WasmBasics.mls` regression produces 3 for arithmetic and 4 for three method
calls in the same block.

The new-resolution tests inherit `:js` from the root test configuration. With
`:wasm`, lowering emits WASM-specific intrinsic references, but the harness also
tries to execute that same IR as JavaScript. This causes the missing `wasm`
binding and subsequent JavaScript ReferenceError; the WASM arithmetic itself
still succeeds. Make `:js` a flag supporting `:!js`, and use that override in
these WASM tests while retaining the inherited language configuration.

The remaining failure in `WasmMethodResolution.mls` is explicit projection
`a.A#get()`. Its elaboration still uses `c.symbol.flatMap(_.asCls)` and syntax
member lookup, bypassing the new resolver. `Class::member` has the same problem.
This is shared frontend logic, not a WASM-specific class lookup failure.
The projection regression remains marked `:fixme` until the design below is
implemented; suppressing JavaScript execution does not fix that failure.

Method calls across separate REPL blocks are being handled on another branch
and are outside this work.

## Proposed projection resolution

1. Give explicit projections a new-resolution representation that records the
   class expression, instance receiver, member name, and resolved candidates.
   Route both `instance.Class#member` and `Class::member` through one resolver
   operation. The latter can keep its existing lambda elaboration, using the
   same projection node in the body.
2. Elaborate the class expression with `Clss` and the instance with `Trm`.
   Register shape listeners in the normal elaboration walk. On a symbol shape,
   wait for definition completion, select its class interpretation independently
   of any term overload, then use the completed class/extension shapes for
   instance-member lookup. Share the relevant class-interpretation logic with
   `resolveNew` rather than duplicating eager symbol queries. Preserve capture
   marks through inherited member lookup and publish the member's shapes for
   calls and subsequent selections.
3. Retain class and wildcard-receiver identity alongside concrete selected
   members. Two candidate classes may expose the same inherited member, so
   deduplicating only by the final member would hide an ambiguous class lookup.
   Keep all candidates; callback ordering must not select a winner. Diagnose
   invalid classes and missing members in resolution, and ambiguity in lowering,
   consistently with other new-resolution references.
4. Lower reads, calls, and assignments from the recorded concrete targets only.
   In particular, the current application case for bare `SelProj` emits
   `Select(...)(N)`, relying on legacy resolution to wrap the node in `Resolved`.
   The new path must carry the selected definition into the IR for all uses;
   neither lowering nor the WASM backend should recover it by name. Preserve
   single evaluation of the instance and the existing projection semantics.
5. Cover forward class definitions, class/term overloads, aliases, wildcard
   ambiguity (including shared inherited members), inherited fields/methods,
   captures, missing members, and projection writes. Run frontend/JS coverage
   and same-block WASM coverage separately. Remove the existing `:fixme` once
   its WASM result is 4.

## Optional harness follow-up

If tests need both JS and WASM execution, lower separately for each target and
keep their backend scopes and session state separate. Respect the MIR rule that
each definition symbol owns at most one current IR definition: use isolated
compilation state or refresh symbols rather than retaining two IRs that mutate
the same symbols' `irDefn` fields. Binding the WASM support module in the JS
scope is insufficient: that module supplies compilation/instantiation helpers,
not JavaScript implementations of all WASM intrinsics.

## Validation

- `ctest`: passed.
- `dtest newres/wasm/`: both tests passed; explicit projection remains `:fixme`.
- `hkmc2AllTests/test`: passed, including all 662 diff tests.
