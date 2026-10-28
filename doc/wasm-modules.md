# Separate WASM modules

Select the backend with a top-level directive. Qualified and short target names
are accepted; a nested directive or an `@config` annotation cannot change target.

```mls
// Numbers.mls
#config(target: CompilationTarget.Wasm)

module Numbers with
  val base = 40
  fun answer() = base + 2
```

```mls
// Main.mls
#config(target: Wasm)

import "./Numbers.mls" as N
fun Main() = N.answer()
```

`MLsCompiler.compileModule` compiles the requested source and its source dependency
graph. It writes a `.wat` and `.mjs` beside each source. As with JavaScript
compilation, a definition named after the file is its default export. A root
without such a definition is an entry-only module; importing it as MLscript source
reports a missing-default diagnostic.

From Node:

```js
import main from "./Main.mjs";
console.log(main()); // 42
```

Run `npm install` at the repository root to install the pinned Binaryen build.
The loaders use its `parseText` API, `node:fs/promises`, and an engine
with WASM GC and exception-tag support. Tests execute them using Node 22.11.0.
Browser loading and direct `.wasm` emission are not provided by this loader.

To run the checked-in examples and regression tests, use the persistent SBT shell:

```text
ctest
cwtest
wdtest FileImports
wdtest HostImports
wdtest Modules
wdtest DiamondImports
wdtest FileInheritance
wdtest TypedFileImports
wdtest OverloadedFileImports
wdtest ModuleErrors
hkmc2AllTests/test
```

The `wasm/Box.mls` compilation fixture includes its generated WAT and loader as
a reviewable output example. Other generated modules are ignored.

Separate-compilation examples live in `mlscript-compile/wasm/modules/` and run
through the normal `cwtest` compilation tests. `Modules.mls` exercises their loaders
using `:js` and `:expect`; `DiamondImports.mls` checks the four-file diamond in
`modules/diamond/`: both branches exchange instances of shared classes, access
their fields, check nominal identity, and share module initialization state.
`FileInheritance.mls` extends a separately compiled subclass from a worksheet,
then extends it again in a later block. Compiled callers check inherited fields,
type tests, and virtual dispatch on these worksheet instances with inlining disabled.
`TypedFileImports.mls` covers concrete reference and unboxed numeric signatures,
typed globals, and recursive class layouts across those same boundaries.
`OverloadedFileImports.mls` checks that function companions and constructors retain
separate identities through aliases, inherited fields, virtual dispatch, and `super` calls.
Cache identity, output restoration, and concurrent requests
are tested by `CompilerCacheTest` because they require controlling the compiler
session and filesystem.

## Source and host boundaries

- Source imports use `.mls` and require both files to select the same target.
  The check runs even if optimization removes every use of the import, and is
  repeated on cache hits. Aliases retain the definition's symbol and therefore
  preserve statically known class and module information.
- Functions and constructors cross file boundaries as WASM function imports.
  Globals, singleton storage, and class RTTI retain their defining instance.
  Standalone modules are static namespaces: their fields have global storage and
  their methods are static functions. Module initialization runs in source order.
  Classes declared inside them have no enclosing instance and use the same ABI as
  top-level classes.
- Classes support the backend's existing field layouts, constructors, imported
  base initializers, direct methods, virtual methods, and nominal class tests.
  A class extended outside its compilation unit must be declared `open` or `abstract`.
  Structurally equal classes from different sources retain different RTTI objects.
- Host function defaults and module methods are callable wrappers. Module fields
  are live getters. Class constructor defaults return opaque WASM GC objects;
  object defaults are opaque GC objects themselves. This is not a JavaScript
  object-field or prototype mapping. Host getters do not expose assignment.
  An explicit function companion remains callable; its `.class` property wraps
  the separate class constructor. Omitted optional arguments bind `null` in both
  source calls and host wrappers; explicitly supplied host values are preserved.
- Signatures and storage retain the typed IR representation, including concrete
  class references and unboxed `Int32`, `Int64`, `Float32`, and `Float64` values.
  JavaScript callers use `BigInt` for `Int64` arguments and results. Arbitrary
  JavaScript objects and callbacks are not automatically marshalled. MLscript
  exceptions crossing a host wrapper are unwrapped using the shared exception tag.
- First-class standalone module values, arbitrary `.mjs`/bare imports from WASM
  source, mixed source targets, and precompiled imports without source interfaces
  are rejected. Existing unsupported backend features, including companion modules on classes,
  object methods/inheritance, closures, and several exception forms, retain
  explicit diagnostics. This change does not promise those language features.

JavaScript can explicitly import a generated `.mjs` loader through the host
boundary. WASM worksheets use `.mls` imports and the same backend interface as
file compilation, alongside instances of earlier worksheet blocks.

## Linking and ownership

`CompilerCtx.Artifact.sourceImports` records explicit source imports separately
from internal runtime dependencies and timestamp dependencies. `WasmCompiler`
walks this graph and consumes the already optimized IR. It neither re-elaborates
nor lowers dependencies again. The complete source closure supplies the private
definitions that foreign inlined bodies can still reference.

`FileInterface` is an immutable backend snapshot. Symbols are origin identities
within a compiler session; source type indices are only edges within that
snapshot. Importing registers a catalog; only bindings demanded by code generation
receive WAT names and declarations. Each demanded binding brings in its transitive
type dependencies, including parents, fields, arrays, function signatures, and RTTI. The
interface also carries initialization functions, singleton globals, namespaces,
and typed virtual tables. Recursive groups retain their original member order,
which is part of WASM type identity; demanding a member imports the entire group.
Declarations are ordered by all their type dependencies. Diamond imports
deduplicate types by origin and representation.
Internal names and external names are allocated separately; neither depends on
global uniqueness of source names or state-local UIDs.

Field accesses use numeric layout offsets. Classes with equal WASM layouts can
give different names to the same offsets; Binaryen's type canonicalization can
misresolve symbolic field accesses in that case. Numeric accesses preserve the
compiler's resolved field identity through assembly.

Files currently export all their defined backend functions and globals, including
private helpers, and snapshot the complete type table. This deliberately favors
correct cross-file inlining over minimal export sets. The raw `wasmExports` object
is an internal compiler ABI, not a stable source-level API. No persistent interface
format or compatibility guarantee between compiler versions is implied.

The shared runtime is generated as `RuntimeWasm.wat` and `RuntimeWasm.mjs` beside
the configured runtime source. It owns intrinsic implementations, canonical Unit
storage/RTTI, and the exception tag. Each file and worksheet instance receives its
own literal memory and decoder closure. A later module cannot overwrite strings
used by an earlier module.

`RuntimeWasm.mjs` in that directory is reserved for runtime support; a source
module that would overwrite it is rejected.

Loaders resolve sibling WAT and dependencies relative to `import.meta.url`, with
URL escaping separate from JavaScript string escaping. Dependencies are awaited
sequentially in source order: static sibling imports with top-level await would
allow observable initialization to run concurrently. ES-module caching provides
once-only initialization, including diamonds. Move the runtime, module outputs,
and dependency tree together while retaining their relative locations, and keep
the pinned Binaryen package resolvable from the runtime loader.

## Caching and failures

Backend results are memoized on the authoritative frontend artifact. A changed
source dependency invalidates its importers through the existing cache. Runtime
and ordinary emission have separate cache slots. The compiler version and session
configuration are fixed for these in-process artifacts; there is no disk cache.

Dependency requests happen before acquiring a backend artifact's lock. Concurrent
roots can therefore share a dependency without recursively holding backend locks.
Output materialization has its own synchronized step on that artifact and restores
missing or changed output files even on a cache hit. Backend errors do not publish
a successful memoized result. Cached frontend errors are replayed so an invalid
unit does not appear valid on the next request.

Failed entry execution does not publish a worksheet interface. A failed file
loader remains failed according to normal ES-module semantics; retrying requires
a fresh host session. Editing a source already imported into a running worksheet
also requires a fresh session to avoid mixing new interfaces with cached instances.
