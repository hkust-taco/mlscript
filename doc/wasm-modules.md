NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# Separate WASM modules

Select the backend with a top-level directive. Qualified and short target names
are accepted; a nested directive or an `@config` annotation cannot change target.

```mls
// Numbers.mls
#lang(0.3.x)
#config(target: CompilationTarget.Wasm)

module Numbers with
  val base = 40
  fun answer() = base + 2
```

```mls
// Main.mls
#lang(0.3.x)
#config(target: Wasm)

import "./Numbers.mls" as N
fun Main() = N.answer()
```

`MLsCompiler.compileModule` compiles the requested source and its source dependency
graph. It writes a `.wat` and `.mjs` beside each source, and returns whether it
emitted the requested module's code; a diagnostic loader for a failed build does
not count. As with JavaScript
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
  The importing unit reports a mismatch when it elaborates the import, even if
  optimization later removes every use of it, so the error is one of that unit's. Aliases retain the definition's symbol and therefore
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

Field declarations and accesses use symbolic identifiers with a zero-based layout
slot suffix, such as `(field $value@2 ...)` and `(struct.get $Box $value@2 ...)`.
The suffix keeps WAT readable while avoiding a Binaryen parser bug: after
canonicalizing structurally equal types, Binaryen
[merges their field name maps](https://github.com/WebAssembly/binaryen/blob/version_133/src/parser/parse-2-typedefs.cpp#L40-L49)
and keeps the first slot associated with each name. For example, two structs with
the same field types but names `{x, y}` and `{y, x}` can make an access to the
second struct's `x` silently read or write its `y` field. This reproduces in
Binaryen 131, 132 (the pinned version), and 133, as checked on 2026-11-06.

Appending the slot makes such collisions harmless: equal identifiers necessarily
refer to equal slots, while `$x@0` and `$x@1` remain distinct. It also distinguishes
shadowed inherited fields in a single layout. `Field.index` supplies the same
identifier for declarations and accesses, using the slot in the complete layout,
including inherited fields. The layout and type identity remain unchanged.
The `FieldLayouts` compilation fixture and
`slop/wasm/FieldNames.mls` cover colliding layouts, mutation, and shadowed fields.

Binaryen 132 also [automatically emits compact import groups when enabled](https://github.com/WebAssembly/binaryen/blob/version_132/CHANGELOG.md#v132).
Node 22 rejects that binary encoding with `unknown import kind 0x7e`.
`RuntimeWasm.withWat` disables `CompactImports` so the binary writer retains the
standard import entries, including for worksheets importing an earlier block.

Files currently export all their defined backend functions and globals, including
private helpers, and snapshot the complete type table. This deliberately favors
correct cross-file inlining over minimal export sets. The raw `wasmExports` object
is an internal compiler ABI, not a stable source-level API. No persistent interface
format or compatibility guarantee between compiler versions is implied.

The shared WASM runtime is generated as `RuntimeWasm.wat` beside the configured
runtime source. It owns intrinsic implementations, canonical Unit storage/RTTI,
and the exception tag. Its main block defines the Unit object, which its entry
function initializes like a file's entry function initializes that file's
singletons; the host library runs it before instantiating any other module. The host
library `RuntimeWasm.mjs` in that directory is compiled from `RuntimeWasm.mls` by
the main compilation tests. Git ignores this generated file; `hkmc2WasmTests/test`
runs the main compilation suite before executing WASM diff tests so a fresh
checkout generates it automatically. Distributions must include it alongside the
runtime sources. Its MLscript source handles Binaryen validation
and disposal, runtime initialization, dependency loading, export wrappers, and
worksheet sessions. Each file and worksheet instance receives its own literal
memory and decoder closure. A later module cannot overwrite strings used by an
earlier module.

`RuntimeWasm.mjs` in that directory is reserved for the host library; a WASM source
module that would overwrite it is rejected.

Generated loaders contain ABI metadata and a small native ES-module bridge to
`RuntimeWasm.loadModule`. The bridge supplies `import.meta.url`, dynamic `import()`,
and boxed raw calls that preserve JavaScript `undefined` results and exception
payloads across MLscript's foreign-call boundary. All loading and wrapping logic
lives in MLscript.

Loaders resolve sibling WAT and dependencies relative to `import.meta.url`, with
URL escaping separate from JavaScript string escaping. Dependencies are awaited
sequentially in source order: static sibling imports with top-level await would
allow observable initialization to run concurrently. ES-module caching provides
once-only file initialization, including diamonds. The host library caches the
runtime initialization promise by canonical WAT URL, including rejection, so
concurrent files and worksheets share the same Unit and exception tag. Move the
runtime sources' compiled JavaScript support, WAT, module outputs,
and dependency tree together while retaining their relative locations, and keep
the pinned Binaryen package resolvable from the runtime loader.

## Caching and failures

Backend results are memoized on the authoritative frontend artifact. A changed
source dependency invalidates its importers through the existing cache. The
compiler version and session configuration are fixed for these in-process
artifacts; there is no disk cache.

The runtime module defines the Unit object of the runtime source and identifies
it by that object's symbol, which every artifact takes from the runtime source's
artifact. So the runtime module is built from that artifact and memoized on it.
Rebuilding the runtime source's artifact, when the runtime source, a file it
imports, or the Prelude changes, creates a new Unit symbol; every artifact
depends on the runtime source, so all of them are rebuilt with a new runtime
module. Otherwise, the runtime module is built once per compilation session, as
the modules linked together refer to its bindings by the symbols of its
interface. The runtime source compiles to JavaScript and no WASM source can
import it, so it has no WASM module of its own.

Dependency requests happen before acquiring a backend artifact's lock. Concurrent
roots can therefore share a dependency without recursively holding backend locks.
Output materialization has its own synchronized step on that artifact and restores
missing or changed output files even on a cache hit.

Each artifact records whether elaborating its own unit reported an error; the
request that builds an artifact reports its diagnostics, and a request that
reuses it reports nothing. A module is compiled only if its artifact and the
runtime artifact have no errors, and the runtime and the modules of its imports
are compiled. A module whose import could not be compiled reports an error at
that import on every request, even when the imported artifact's own errors were
reported by an earlier request. A backend failure is not memoized, so the next
request compiles the module again and reports its errors again.

Failed compilation replaces the failed module's `.mjs` with a diagnostic loader that
throws `Cannot run <source>.mls because its compilation failed.` on import. It
exports the usual default and `wasmExports` bindings so static imports reach that
error, and it does not load the runtime or dependencies. The compilation result
remains `false`, and no WAT is emitted for the failed module. A successful rebuild
replaces the diagnostic loader. Failed compilation retains existing `.wat` files,
including `RuntimeWasm.wat` when runtime compilation fails. The reserved
`RuntimeWasm.mjs` host library never receives a diagnostic loader, even when a
source module collides with its path.

Dependencies compiled successfully during the request may already have been written;
failure does not roll back those writes. Existing output can therefore be stale or
mix build generations. Callers should check the result of `compileModule`, or the
`compiled` field returned by `Compiler.compile`, before automatically loading output.
A cached source or runtime error can make this result `false` without reporting
diagnostics again; that request also replaces any existing module loader with the
diagnostic loader. Retained WAT may be stale: WASM validation does not establish
that it matches the current sources.

When a loader cannot find its WAT file, it reports the missing compiled output
and asks the user to rebuild before running. The error retains the filesystem
exception as its `cause`; other filesystem errors pass through unchanged.

Failed entry execution does not publish a worksheet interface. A failed file
loader remains failed according to normal ES-module semantics; retrying requires
a fresh host session. Replacing a loader on disk also cannot revoke an older
instance that the host has already imported. Editing a source already imported
into a running worksheet also requires a fresh session to avoid mixing new
interfaces with cached instances.
