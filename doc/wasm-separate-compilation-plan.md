# Separate WASM compilation and imports

Status: original design and implementation plan, 2026-09-08; implemented in
September 2026. See [WASM modules](wasm-modules.md) for the implemented contract,
architecture, test commands, and limitations. The sections below retain the
planning rationale and proposed sequence.

Base: upstream `hkust-taco/hkmc2`, commit
`1a86e1cffe509c826a04c7828c0c6e520653dc2a`. The local `hkmc2` commit is excluded.

Reference: [PR #472: Add WASM Backend Support with File Imports](https://github.com/hkust-taco/mlscript/pull/472).
That PR establishes the intended user-facing functionality; its implementation
should not be ported. This plan is based on inspecting the current compiler and
the PR's diff and review discussion.


## 1. Intended result

A source file can select the WASM backend:

```mls
#config(target: CompilationTarget.Wasm)

module Numbers with
  fun answer() = 42
```

Compiling `Numbers.mls` produces `Numbers.wat` and `Numbers.mjs`. The latter is a
small ES-module loader that loads the adjacent WAT, links dependencies, and
initializes the module. Another WASM-targeted source file can import
`"./Numbers.mls"` using the existing MLscript import syntax.

The implementation should provide:

1. Independent WAT artifacts with explicit imports and exports. Imported code
   remains in its defining module, except where the existing optimizer deliberately
   inlines it.
2. Ordinary same-name default-export semantics: the source definition named after
   the file is its default export. Do not introduce a second source-level export
   convention for WASM.
3. Functions, values, modules, classes, and objects across file boundaries, within
   the language features the WASM backend otherwise supports. Unsupported forms
   must produce explicit diagnostics.
4. Correct aliasing, shared mutable state, initialization order, nominal class
   identity, and singleton identity across repeated and diamond imports.
5. Reuse of the existing frontend cache, lowering pipeline, and optimizer.
6. Preservation of existing JavaScript compilation and WASM worksheet behavior.

The initial output contract remains WAT plus a loader, matching the PR. Direct
`.wasm` emission, a persistent binary/interface cache, and compilation without
dependency sources are separate extensions. They must not become accidental
requirements for the first implementation.

Mixed JS-targeted/WASM-targeted **source** imports remain unsupported initially,
as in the PR. Loading a generated WASM loader from JavaScript is a narrower host
interface, not a promise of transparent interoperability between all MLscript
JavaScript and WASM values.


## 2. What already exists

| Area | Current behavior | Consequence for the implementation |
| --- | --- | --- |
| `CompilerCtx.getElaboratedBlock` | Caches parsing, elaboration, resolution, and fully transformed IR; records transitive source dependencies. | Consume the cached artifact. Never independently elaborate or lower imported files. |
| `Elaborator.State` | Owns symbol identities and compilation-unit provenance; exposes `externalModuleImport` and private ABI names. | Preserve origin symbols and recover dependencies introduced by cross-file inlining. |
| `MLsCompiler.compileModule` | Small frontend-artifact-to-JavaScript emitter. | Add target dispatch, keeping WASM implementation in `codegen/wasm`. |
| `Config` | Already has `CompilationTarget.JS` and `.Wasm`; the retained changes add source parsing and placement restrictions. | Backend dispatch and validation still need implementing. |
| `WatBuilder.program` | Supports standalone/worksheet generation and REPL bindings, but rejects ordinary file imports and default exports. | Add a file-compilation entry point around shared emission machinery. |
| `SessionBinding` | Describes REPL functions, globals, classes, and singletons. | Useful starting point, but insufficient as a separate-compilation interface. |
| Class lowering | Generates instance structs, constructors, initializers, RTTI globals, and virtual slots. | All ABI-relevant parts must be represented when a class crosses a file boundary. |
| Compile/diff tests | Compile `.mls` fixtures before executing worksheets; golden output is embedded in `.mls` files. | Extend these workflows and validate real generated modules. |

The existing invariants are also documented in
[`cross-unit-inlining.md`](cross-unit-inlining.md), and in the design notes at the
start of `codegen/Block.scala`.

Several concrete hazards were found during inspection:

- REPL class metadata embeds `TypeInfo`/`CompType` values containing names allocated
  in the producing WASM context. RTTI imports also hardcode the `"repl"` module.
  These records cannot simply be copied into a separately named module.
- REPL class metadata does not describe every initializer, method, parent, and
  virtual-slot dependency needed by imported classes and subclasses.
- Symbol UIDs are unique only within an elaboration state. Two dependencies can
  contain symbols with the same UID and spelling.
- The backend's string pools each start at offset zero and are decoded when used.
  Sharing one literal memory between independently instantiated modules can
  overwrite strings that an earlier module will read later.
- Exception tags are currently defined per generated module.
- Nominal class tests rely on identity of RTTI references. Recreating a dependency's
  RTTI singleton locally changes the meaning of class tests.
- Standalone source modules lower to a synthetic class with a companion body.
  Merely accepting a `syntax.Mod` class kind does not implement them.
- `Program.imports` contains `.mjs` output paths even when the original import
  named an `.mls` source. A `.mjs` suffix alone does not identify a JavaScript
  dependency or prove that a source artifact exists.


## 3. Design invariants

### 3.1 One frontend identity per cached compilation unit

The source artifact returned by `CompilerCtx` is authoritative. All importers in
the compilation session share that artifact's symbols. The backend must not parse
again, lower a second copy, change the unit's configuration on behalf of an
importer, or reconstruct IR definitions merely to adapt them for WASM.

Constructing new definition nodes can update `DefinitionSymbol.irDefn`. Backend
adaptation should therefore use backend-owned descriptions and traversals, leaving
the cached optimized IR intact.

### 3.2 Separate semantic artifacts, backend artifacts, and output files

These are different states:

- A source artifact was elaborated and optimized.
- A WASM artifact and its interface were generated from that source artifact.
- The requested output files were written and are available to load.

Cache presence at the first level does not imply either of the others. In
particular, do not return a fabricated empty WASM module when elaboration was
already cached, and do not skip writing files merely because emission metadata
exists.

### 3.3 Origin identity and external names are distinct

Use the normalized source/output path and original symbols to identify definitions
within a session. Allocate deterministic external names in the defining module;
importers consume those names from its interface.

Do not derive external names from UIDs, depend on import traversal order, or use
basenames as globally unique module identifiers. Keep one collision-checked WASM
export namespace covering user bindings, the entry point, constructors, initializers,
methods, RTTI, singleton storage, and private helpers.

### 3.4 Initialization is observable

Repeated imports must share the same module instance and mutable globals. A diamond
must initialize the common dependency once. Source initialization belongs in the
generated entry function and follows dependency initialization.

Distinguish existing low-level WASM start actions from source module initialization;
do not accidentally execute constructors through both mechanisms. Exceptions must
leave module loading failed rather than publishing a usable-looking partial module.


## 4. Proposed architecture

### 4.1 Target selection and import provenance

Retain `#config(target: CompilationTarget.JS|Wasm)` and the short `JS`/`Wasm`
spellings already added. Permit target selection only through a top-level directive.
Reject target fields in `@config` and nested `#config` with ordinary compilation
diagnostics, while retaining unrelated valid configuration fields.

Keep existing cumulative directive semantics: the complete compilation unit's final
configuration determines its backend. Do not add a first-line-only restriction
without a separate language-design reason.

Validate source-target compatibility after the unit's `artifact.config` is known.
The elaborator stores directives as `SetConfig` statements; testing only its
constructor `cfg.target` inside `Importer.importPath` would be incorrect.

Preserve explicit source-import provenance through elaboration. Prefer a small
immutable direct-import record attached to the compilation-unit artifact, recording
the source path, resolved binding/default export, and dependency artifact identity
or a cache-resolvable reference. Keep it distinct from the existing transitive
timestamp set, which also contains compiler-internal dependencies.

This record should distinguish:

- `.mls` source imports, including aliased imports;
- explicit JavaScript/bare module imports;
- compiler-synthesized runtime imports;
- dependencies discovered in optimized foreign references.

Do not guess an original `.mls` import by replacing a `.mjs` suffix and checking
whether such a file happens to exist. Both files may legitimately exist with
different intended meanings.

Validate even source imports whose calls disappear through inlining. Otherwise an
unsupported mixed-target dependency could appear to work depending on optimization.

### 4.2 Backend-owned module interface

Introduce an immutable interface in `codegen/wasm`, separate from semantic symbols
and from the JavaScript private-name table. Suggested components are:

| Component | Required information |
| --- | --- |
| Module identity | Canonical defining-module identity, output location, default-export identity. |
| Value bindings | Export names and representation of functions, globals, constructors, and singletons. |
| Type graph | Context-independent identities and descriptions for every type needed by exported signatures/layouts. |
| Class ABI | Instance layout, parent, constructor, initializer, methods, virtual slots, and origin RTTI binding. |
| Module namespace | Resolved member symbols and their bindings; initialization and default-export representation. |
| Runtime requirements | Intrinsic imports, exception tag, Unit binding, and literal-memory requirement. |
| Loader metadata | Default-export access and any explicitly supported host wrappers. |

An illustrative boundary is:

```scala
def fileModule(
    program: Program,
    defaultExport: Opt[BlockMemberSymbol],
    moduleName: Str,
    imports: Seq[WasmModuleInterface],
    aliases: Map[ValueSymbol, ValueSymbol],
)(using Raise): CompiledWasmFile
```

`CompiledWasmFile` contains emitted WAT, entry-point information, and the interface.
The exact Scala types should follow implementation needs; this sketch describes
ownership and inputs, not a requirement to preserve these names or argument shapes.

Retain the existing worksheet API as a wrapper around shared binding/emission
machinery. A file module and a worksheet have different initialization and import
transport, but should not duplicate code for describing the same WASM binding.

### 4.3 Type reconstruction and linking

Do not export a producing context's allocated `TypeInfo.id` as a reusable type
description. Recreate ABI-relevant types in the importing context:

1. Collect the closed dependency graph of imported signatures and layouts.
2. Allocate destination type identities before rendering their references.
3. Remap all references: struct parents, field types, array elements, function
   parameters/results, virtual-slot types, and recursive references.
4. Preserve subtype finality, nullability, field mutability, field order, and any
   recursion-group structure needed for compatible WASM types.
5. Register functions/globals against those reconstructed types.

Start with a complete immutable type snapshot if it is materially simpler, but
isolate that choice behind the interface. It must still relocate every reference
and preserve runtime type compatibility. Do not copy unrelated local types into a
shared recursion group or assume textual name equality establishes compatibility.
Validate this with actual WebAssembly instantiation, not WAT string comparison.

Deduplicate diamond imports by origin identity. A re-export keeps its original
binding and RTTI origin; it does not create another nominal class or singleton.

### 4.4 External references after optimization

Use compilation-unit provenance to recover dependencies that optimization introduced
into the importing IR, following the existing JavaScript backend's approach.
`Program.imports` alone is insufficient.

Export the private definitions needed by such references through a WASM private ABI.
Reuse the existing policy for preserving top-level symbols; do not copy JavaScript
export spellings blindly or add a second ad-hoc source-name lookup mechanism.

Resolve aliases through their explicit import record and the dependency interface's
default export. Known module-member selections should resolve through symbols or
the corresponding namespace metadata. Unknown dynamic selections need an explicit
representation or a diagnostic, not a global name-based fallback.

### 4.5 Backend artifact caching and emission

Keep `MLsCompiler` responsible for obtaining the frontend artifact and dispatching
to the selected backend. Put WASM dependency traversal, interface generation, and
loader emission in a dedicated compiler/emitter under `codegen/wasm`.

For WASM compilation, emit the transitive source dependency closure so compiling a
root produces a loadable result. Preserve source import ordering for initialization;
sort otherwise unordered synthetic dependencies deterministically.

Key cached WASM results by the authoritative frontend artifact identity and the
relevant backend/runtime ABI version. Cache invalidation must follow rebuilt
dependencies and the existing fixed-session configuration. Record backend errors
as failures, not successful reusable artifacts.

Reuse the existing cache's per-path concurrency approach where practical. Do not
hold a new global backend lock while recursively requesting dependencies. Existing
source cycle diagnostics should remain authoritative; verify that new backend
requests cannot reintroduce a lock cycle.

Output materialization is a separate step. Repeated compilation should restore
deleted `.wat`/`.mjs` outputs from valid backend artifacts. Write complete content
before treating outputs as successful; use existing filesystem abstractions and
account for concurrent roots emitting a shared dependency.

### 4.6 Runtime and loaders

Generate/import one runtime support module per compilation runtime identity, with
a stable location and explicit version/update policy. It should supply shared
intrinsic functions, the MLscript exception tag, and canonical Unit identity.

Each compiled source module should receive its own literal memory and a decoder
closure bound to that memory. Intrinsics and identity-bearing runtime objects remain
shared. This avoids relocating every literal while preventing one module's data
segments from corrupting another's strings.

Unit requires particular care: `State.unitBlockMemberSymbol` is created per state,
while the semantic runtime Unit is shared. Map these backend aliases to a single
runtime Unit binding and RTTI identity; do not instantiate a Unit per file.

The generated `.mjs` loader should:

1. Import the shared runtime and the dependency loaders.
2. Load its sibling WAT using a URL relative to `import.meta.url`.
3. Parse/compile WAT using the repository's Binaryen support, disposing temporary
   Binaryen modules even when validation or binary emission fails.
4. Build the import object from the dependency interfaces and runtime requirements.
5. Instantiate WASM and invoke the source entry exactly once through ES-module
   evaluation.
6. Expose a namespaced raw export object for generated loaders/low-level tests and
   the same-name source default export through the agreed host representation.

Use existing string-literal escaping for generated JavaScript and explicit escaping
for WAT strings. File URLs must also encode path characters such as `#`, `%`, spaces,
and non-ASCII text correctly; JavaScript string escaping alone is insufficient.

Keep loader URLs relative so an emitted dependency tree can be moved together.
Distinguish link identity from filesystem location: canonical paths can identify
modules during compilation, but host absolute paths should not be required to load
the generated tree. A local import-key mapping is preferable if it avoids embedding
absolute paths in the WAT ABI.

Do not embed a second copy of WAT in `.mjs`, duplicate the intrinsic runtime in every
loader, or use a process-global mutable registry as a substitute for ES-module
instance identity. Specify Node loading first and keep any browser fetch path
explicit rather than promising untested browser support.

### 4.7 Modules and classes

Handle standalone modules using their actual lowered companion-body representation.
A static namespace is a promising implementation: module values have global storage,
methods have static function bindings, and the module's initialization remains in
the file entry point. Preserve source initialization order and live mutable members.

However, static namespace selection alone is not a complete representation of
first-class module values. Inspect existing lowering and tests before choosing
whether such values use a GC object, a dedicated namespace handle, or an explicit
initial limitation. Any unsupported first-class use must be diagnosed.

For classes, import the complete class ABI before declaring local subclasses.
Support imported parents in inheritance ordering, preserve inherited field and
virtual-slot order, and import the defining module's RTTI global. Do not rebuild a
class's nominal identity locally even if its instance layout is structurally equal.

Constructor and initializer imports are distinct: allocating an imported class and
initializing the imported part of a local subclass must both work. Virtual methods
need the correct receiver and stable slot layout. Existing unsupported combinations,
such as some class/companion or nested-definition forms, should remain explicit
unless deliberately included and tested.


## 5. Implementation sequence

Each phase should leave a reviewable change with focused validation. These are
implementation stages, not permission to declare the full feature complete early.

### Phase A — Finish the compilation contract

- Review and test the retained target parser/placement changes.
- Add direct source-import provenance without disturbing cache identity.
- Define output naming, dependency emission, supported exports, and cross-target
  diagnostics.
- Resolve the interface/host-boundary questions listed below.

### Phase B — Define and validate the WASM interface

- Add immutable backend interface types and deterministic export allocation.
- Factor REPL binding metadata away from its hardcoded import transport.
- Implement type reconstruction and test collisions and dependency closure.
- Add tag-import representation to the WASM AST/context if needed.

### Phase C — Compile and load separate functions and values

- Add the file-compilation entry point and predeclare exported functions/globals.
- Add backend artifact caching and output materialization.
- Generate the shared runtime and small loaders with per-module literal memory.
- Prove basic default exports, recursive/forward function references, aliases,
  shared mutable state, diamonds, and separate string pools end to end.

### Phase D — Preserve optimizer and module semantics

- Recover foreign references after optimization, including private helpers.
- Implement standalone module members and initialization using the current IR.
- Validate module default exports and the supported host facade.
- Verify cache reuse and regeneration after dependency changes.

### Phase E — Complete classes and runtime identities

- Import layouts, constructors, initializers, methods, and virtual tables.
- Support imported parents and nominal class tests across files.
- Ensure objects, Unit, and exception tags retain the required shared identity.
- Test errors for unsupported forms before code emission reaches failed lookups.

### Phase F — Integrate worksheet imports and complete review

- Let WASM worksheets obtain file interfaces/instances while retaining REPL imports.
- Add `.mls` source-import and generated `.mjs` host-import fixtures.
- Document commands, supported behavior, runtime dependencies, and remaining limits.
- Review generated artifacts and golden changes, then run the required full suite.


## 6. Regression matrix

Use both compiler API tests and the established compile/diff tests. At least one
test in each runtime row must compile WAT with Binaryen and instantiate/run the
result; checking for text in generated files cannot establish correct linking.

| Area | Cases and required observations |
| --- | --- |
| Target configuration | Qualified/short target names; invalid target; top-level selection; nested/annotated rejection; unrelated config fields still work; imported unit's own target wins. |
| Basic emission | Function, value, module, class, and object defaults; no-default entry-only file; real `.wat` plus loader; initializer result does not replace the source default. |
| Imports | One dependency, aliases, repeated imports, transitive imports, and diamond; relative/absolute source paths normalize correctly. |
| Names | Same basenames in different directories; same exported member names; user names colliding with entry/runtime/RTTI helpers; differing dependency traversal order. |
| Initialization | Observable side effects once; dependency order preserved; mutable globals shared through different import paths; thrown initialization fails loading. |
| Optimization | Non-inlined and inlined calls; inlined bodies referencing private helpers or transitive imports; no duplicated dependency definitions or mutated cached IR. |
| Cache behavior | Each source parsed once per valid artifact; compile-after-import works; changing a dependency invalidates importers; unrelated units remain cached; deleted outputs are recreated. |
| Concurrency | Two roots sharing a dependency; consistent backend artifact identity; no duplicate partial writes or deadlocks; existing circular-import diagnostics remain intact. |
| Classes | Imported construction; imported-base subclass; inherited fields; direct/virtual methods; overrides; two equal layouts from different modules remain nominally distinct. |
| Identity | Objects and Unit equal across modules as language semantics require; distinct objects/classes stay distinct; re-exports preserve origin. |
| Strings | Dependency returns its original string after another module loads; empty/Unicode strings; different-sized pools; memory growth if required. |
| Exceptions | A dependency throws and the host unwraps using the shared tag; cross-module catch when the supported exception path permits it; otherwise explicit existing limitation. |
| Diagnostics | Both directions of mixed-source targets; bare/JS imports in WASM; missing default; unsupported dynamic module use; unsupported backend features. |
| Loading | Actual generated `.mjs` import; loading from another working directory; relocation of output tree; paths with URL/string-sensitive characters; runtime helper freshness. |
| Existing behavior | WASM REPL bindings, inherited classes, virtual methods, strings, and exceptions; existing JS cross-unit inlining and cache tests; Scala.js in-memory compiler. |

Suggested locations:

- Normal compilation fixtures for dependency graphs, with Node execution through
  the existing diff tests. Keep cache/concurrency checks in the compiler API tests.
- `hkmc2/js/src/test/scala/hkmc2/CompilerTest.scala` for in-memory filesystem and
  cross-platform artifact behavior.
- `hkmc2/shared/src/test/mlscript-compile/wasm/` for durable source fixtures.
- `hkmc2/shared/src/test/mlscript/wasm/` for worksheet and import regressions.
- One small deliberately checked-in `.wat`/`.mjs` pair to make the output contract
  reviewable; keep other generated artifacts ignored as appropriate.

Follow `AGENTS.md` and `.github/skills/hkmc2-difftests`: use direct `sbt`, install npm
dependencies, compile fixture groups before dependent diff tests, and inspect
rewritten `//│` lines. Run `ctest` and `cwtest` as needed, focused `dtest`/`wdtest`
while iterating, and `hkmc2AllTests/test` before completing implementation. Include
intentional golden changes in any later implementation commit; do not commit
temporary experiments or unrelated rewrites.


## 7. Decisions to settle before the corresponding phase

1. **Type interface representation.** Prefer a context-independent graph of
   ABI-relevant types. A relocated snapshot can be an implementation step, provided
   runtime compatibility and recursion structure are preserved. Decide this in
   Phase B before spreading context-bound records through the compiler.
2. **Direct import records.** Choose the smallest extension to current artifact
   provenance that distinguishes source imports, aliases, and explicit `.mjs`
   imports. Keep resolution in the frontend and linking in the backend.
3. **Precompiled imports.** Initially require source artifacts for WASM source
   compilation; permit host JavaScript to load generated `.mjs`. Importing arbitrary
   precompiled WASM from WASM source requires an explicit interface/ABI mechanism,
   not suffix guessing. If required for the first deliverable, design that mechanism
   before Phase C.
4. **Host facade and first-class modules.** Define which values can cross the host
   boundary directly, which need wrappers, and which are opaque. Test numeric/ref
   behavior rather than assuming arbitrary JS values fit `anyref`. Specify live
   mutable module members and first-class module use explicitly.
5. **Runtime identity and placement.** Fix where the runtime lives, how stale
   generated helpers are refreshed, and how independently emitted modules agree
   on Unit/tag identity and ABI version. Avoid basename collisions and hidden
   compiler-machine path dependencies.
6. **Scope of existing WASM limitations.** Separate file-linking gaps from existing
   limitations such as unsupported class companions or exception forms. Document
   and diagnose deferred forms; do not silently accept them or suppress tests.


## 8. Completion criteria

The work is complete when a root WASM-targeted `.mls` compilation produces a
loadable dependency tree; imports preserve runtime and symbol identities; supported
functions, values, modules, classes, and objects work across files; optimizer and
cache behavior remain sound; and unsupported combinations report useful errors.

Review should show a small target-dispatch change in `MLsCompiler`, narrowly scoped
frontend provenance/configuration changes, and a cohesive backend implementation.
There should be no duplicate elaboration pipeline, mutable ABI fields on semantic
symbols, empty cached-result placeholders, embedded duplicate WAT, or broad
unrelated refactoring. Focused runtime tests and the required full suite must pass.

The implementation uses an in-process relocated type snapshot and static module
namespaces. Files and worksheet blocks share that interface. Host loading targets
Node, with opaque GC objects and explicit rejection of first-class module values.
