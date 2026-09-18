# Cross-Compilation-Unit Inlining

MLscript can inline a function whose definition was compiled from another source file. This is
more than a local optimizer feature: cached compilation units must share symbol identity, and the
JavaScript backend must preserve any file-private definitions exposed by the transformed body.

This document records the invariants that keep the implementation sound.


## Compilation-unit identity

A cached `Artifact` owns the identity of every definition it contains. All importers must therefore
observe the same artifact for a given source file.

`CompilerCtx` fixes the root configuration and compiler paths for its lifetime. Imported units are
elaborated under that configuration, not the importing file's configuration. In particular, an
importer's directory must not affect the cache identity or the runtime path embedded during
lowering.

Cache keys use normalized paths. JVM paths are normalized by `os.Path`; JavaScript `VirtualPath`
normalizes on construction, including clamping `..` at the root. The string-facing operations of
`InMemoryFileSystem` normalize their inputs as well, so alternate spellings cannot create distinct
artifacts for one file.

Cache insertion is atomic per path. Concurrent requests for one file share one artifact and one set
of symbols, while unrelated files may still be built concurrently. An artifact is reusable only
while all of the following remain current:

* its source;
* its shared Prelude identity; and
* the source timestamps of all transitive dependencies captured during elaboration.

If a dependency is stale, the requested importer is rebuilt. Its ordinary import traversal then
rebuilds any stale dependency before recording the new artifact.


## Authoritative IR

Every imported compilation unit is lowered and run through the complete `CompilationPipeline`.
The inliner reads `DefinitionSymbol.irDefn`, which must refer to the latest rewritten definition;
freshly lowered or partially transformed IR is not safe to splice into another unit.

The compilation unit's top-level symbols are preserved as a private ABI. They are collected after
the mandatory lowering passes have settled the unit's definitions. Collecting them too early would
preserve temporary forwarders left by transformations such as `TailRecOpt`, adding avoidable calls
and potentially breaking stack safety.

Automatic-inlining fuel is a budget per source file. The pipeline reuses one `BlockSimplifier`
across its simplification passes, and fuel is spent only after every argument list matches.


## Reachable call graph

Loop-breaker selection uses the reachable graph of functions that are plausible inline candidates,
including functions defined in other compilation units. Local definitions retain their established
traversal order. A non-local definition is rejected before graph traversal when the available
eligibility checks prove it ineligible: `noInline`, pattern-helper ownership, an unsupported method
receiver, an incompatible compilation policy, or an automatic-inlining body larger than the
applicable threshold. This uses the body's standard lazy `size` value; explicit `@inline` functions
are not size-limited.

An eligible non-local definition not already encountered is registered before being appended to a
worklist, so self- and mutual-recursive references terminate immediately. Traversing a body may
append previously unseen eligible callees; advancing an index through the append-only worklist
therefore computes the candidate closure without rescanning symbols. A separate visited-body set
ensures that every local or eligible non-local body is traversed exactly once. Calls in non-local
bodies contribute graph edges but not local use counts.

Each traversed `FunDefn` publishes an immutable `InlinerBodySummary` containing its direct call
occurrences and nested function definitions. A dedicated, configuration-independent traverser
computes this value without sharing mutable state with the inliner analysis that consumes it.
The summary belongs to that exact immutable IR node, so replacing a definition naturally
invalidates it. Later importing units replay the summary rather than walking the body, while still
applying their own eligibility checks and rebuilding their own candidate closure and SCCs.
Publication uses an unsynchronized reference slot: computing a summary is pure, JVM reference
writes are atomic, and racing threads may harmlessly compute and publish the same immutable value
more than once.

This is not incremental SCC maintenance. SCC and loop-breaker analysis starts only after the
worklist is exhausted and the candidate graph is complete. With populated body summaries, its work
is linear in the eligible reachable functions and call edges, plus computing the lazy sizes of
non-local automatic-inline candidates, with expected constant-time symbol lookup. A summary miss
adds one structural traversal of that function body. Generic inline fuel remains a defense against
excessive acyclic growth, not a substitute for recursion detection.


## Safe bodies

Only methods owned by true `module` symbols may be inlined as module methods. Instance and `object`
methods retain their receiver and initialization semantics and therefore stay in place. For a
nested module method, the copier rebuilds module `this` paths from the call-site qualifier so the
copied body remains correctly rooted.

Inlining is also rejected when moving a body could change its meaning or produce invalid IR:

* caller and callee disagree on `noFreeze`;
* the body refers to `import.meta.url`;
* a cross-unit body accesses a JavaScript-private member whose accessor exists only in the defining
  emitted module;
* generated pattern helpers reuse bound symbols across mutually exclusive blocks; or
* the body otherwise contains duplicate bound symbols.

The structural safety properties of a function are cached by its `InlinerFunInfo`; they do not need
to be rediscovered at every call site.


## JavaScript private ABI

Inlining can expose a reference to a top-level definition that was previously private to its file.
Compiled modules export such definitions under a scope-allocated name with the
`_$_modulePrivate_$_` prefix. Importing modules synthesize a matching named import. For example:

```js
// Dependency.mjs
export { helper as _$_modulePrivate_$_helper };
```
```js
// User.mjs
import { _$_modulePrivate_$_helper as helper } from "./Dependency.mjs";
```

The defining compilation state records symbol provenance and the allocated export names. Before
rendering either a module or a worksheet, `CompilerCtx` traverses the IR and builds one typed import
plan containing resolved module paths, default imports, and private imports. Collection and binding
are shared by both output modes.

Names are allocated through the ordinary JavaScript `Scope`, which handles escaping and collisions
without exposing state-local symbol UIDs. Dependencies are ordered by normalized module path and
then by their state-local symbol UID and name, making generated imports deterministic even when
sets, maps, or parallel elaboration produce a different traversal order.


## Shared ambient symbols

All units in a `CompilerCtx` share one Prelude and one `Runtime.mls` elaboration. A cached body thus
already refers to the ambient symbols known by its importer. `SymbolRefresher` only refreshes
definitions introduced by copying the body; it does not rebind builtins from one independently
elaborated Prelude onto another.


## Regression coverage

The principal tests are:

* `hkmc2/shared/src/test/mlscript/opt/InlineAcrossFiles.mls` for cross-file bodies and the private ABI;
* `hkmc2/shared/src/test/mlscript/opt/InlineModuleMethods.mls` for receiver rooting and eligibility;
* Scala.js compiler tests for virtual-path normalization, cache invalidation, and stable ABI names;
  and
* compile tests for the generated `.mjs` modules consumed by runtime diff tests.

Run `ctest` before runtime diff tests so those generated modules are current.
