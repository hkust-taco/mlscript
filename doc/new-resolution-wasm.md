
## Initial WASM migration milestone (`8e66dbefd`)

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

## Type interpretation migration in progress

Ten of the eleven remaining files now use the shared configuration. `Basics`
retains its previous configuration pending the capture fix below. Deferred type
interpretations preserve forward aliases and unboxed signatures, and annotations
publish nominal instance shapes before a function is called. Assignment lowering
accepts the new reference forms; mutable tuples forward their value shapes.
The old empty-call syntax for bare classes and paramless getters has been updated.

The retained WASM suite passes all 22 files, including the new forward-alias
regression. Trying `Basics` with new resolution exposes a capture-context assertion for:

```mlscript
class Foo(val x)
fun getX(f: Foo) = f.x
getX(Foo(42))
```

The nominal shape supplied by the annotation knows the field symbol but lacks the
construction context carried by its inferred value. Returning that value tries
to exit `getX` while its pending entry mark belongs to the constructor `Foo`.
This must be addressed in the relationship between declared interfaces and
call-derived value shapes, without bypassing capture invariants. The outstanding
semantic question is whether annotations fix the available member interface or
permit refinement from concrete arguments. This is an intermediate checkpoint; the migration is not complete until that
question and the assertion are resolved.
