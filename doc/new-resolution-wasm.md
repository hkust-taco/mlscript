
## Existing WASM suite migration (partial)

The shared `mlscript/wasm/.mls` enables new resolution, strict resolution, and
WASM execution while disabling JS execution. Migrated tests start with `:.`,
before any blank line, so these commands apply throughout the file. No
`:global` is needed. The synthetic Predef import now explicitly targets JS,
and WASM emission checks the compilation target as well as `:wasm`; this avoids
sending the host-side bootstrap import to WASM when the option appears at the
very top of a file. `newres/wasm/FileWideFlags.mls` covers that placement across
two blocks. `Binaryen.mls` is unchanged.

Eight existing files migrate without compiler design changes: `ClassInheritance`,
`Exceptions`, `MainFunctions`, `Matching`, `ScopedLocals`, `SingletonUnit`,
`Singletons`, and `Strings`.

The remaining eleven files were tried with the shared configuration and failed.
Their original configurations and snapshots are retained, rather than marking
the migration failures as expected. The main remaining work is deferred type interpretation:

- `NumericTypes` and `BuiltinOperators`: annotations such as `Int64` and `Int32`
  are elaborated as new references, but `ErasedType.eraseSign` still queries
  legacy `sign.symbol` eagerly. Declared erased types become unknown, causing
  primitive/reference representation conversion errors. Type interpretation must
  resolve before erased signatures are consumed, including forward definitions,
  aliases, and wildcard names; replacing this query with another eager lookup
  would not establish that contract.
- `TailRecOptCasts`: the separately compiled declaration
  `fun useBox(b: Box): Int = b.v` has no resolved target for `v` before any call.
  Declared parameter types should publish instance shapes through the existing
  listener-based resolution infrastructure, independently of calls.

The trial also exposed smaller adaptation gaps: assignment lowering does not
accept `SimpleRef` or captured selection l-values; mutable tuple shape handling
throws an unimplemented-case exception; some old expected-error cases now
succeed. These were not changed after reaching the design boundary.

Blocked files: `Basics`, `BuiltinOperators`, `Casts`, `ClassMethods`, `ControlFlow`,
`NumericIntrinsicReview`, `NumericTypes`, `ReplImports`, `TailRecOptCasts`, `Tuples`,
and `VirtualMethods`. Cross-block method handling remains owned by the other
branch.
