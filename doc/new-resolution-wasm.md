# New resolution and WASM

The [migration worklist](new-resolution-suite-migration.md) tracks remaining ports.
The general [resolver invariants](new-resolution-design.md) also apply to WASM.

## Configuration and lowering contracts

`hkmc2/shared/src/test/mlscript/wasm/.mls` inherits the common non-strict
`#lang(0.3.x)` configuration and enables WASM execution. Migrated worksheets
start with `:.` before any blank line so the flags apply throughout the file;
no `:global` is needed. The common language configuration disables JS execution.

The synthetic Predef import explicitly targets JS. WASM emission checks the
compilation target as well as `:wasm`, so placing the directive at the top of a
file does not send the host-side bootstrap import to WASM.
`newres/wasm/FileWideFlags.mls` covers this across two blocks.

Type interpretation must finish before erased signatures are consumed, including
forward definitions, aliases, and wildcard names. Eager legacy symbol queries on
new-resolution annotations violate this ordering. Declared parameter types provide
interfaces independently of calls; they do not reveal unannotated field initializer
shapes. `newres/wasm/DeclaredTypes.mls` covers annotated receivers and tuple reads
and writes, which use indexed lowering.

## Remaining migration and backend gaps

Nineteen of the 21 existing worksheets use new resolution. The remaining files
retain their legacy configuration and goldens:

- `wasm/Basics.mls`: the last trial reached a capture assertion in the unannotated
  initializer `class Foo(val x) with val y = this.x`. Annotated-receiver regressions
  already pass; annotation opacity is a settled rule.
- `wasm/Binaryen.mls`: `WebAssembly.Instance.exports` needs a declared interface.

The compilation fixture `mlscript-compile/wasm/Wasm.mls` also needs the exports
interface and an interface for its exposed `wasmInst.imports` receiver.

The callback example and calls through tuple elements in
`newres/wasm/DeclaredTypes.mls` remain expected failures: WASM lacks the required
first-class function representation and anonymous-function lowering. Coordinate
cross-block method changes with the separate implementation work.
