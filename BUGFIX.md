# PR title

fix: preserve parameter assignments when lowering async functions

# PR description

An async function that mutates a parameter, such as `set n += 1`, currently reports
"No definition found in scope for member 'n'" during JavaScript generation. Async
lowering extracts the body into a helper with fresh parameters, but only rewrites
reads of those parameters; assignment destinations retain the original symbols.

Use the typed symbol substitution shared by the IR transformer so parameter
bindings, reads, and assignment destinations are renamed consistently. Preserve
the existing handling of the method receiver. This fixes ordinary parameter
mutation without changing the compilation pipeline or async calling convention.

The regression covers direct mutation, mutation after an await, and mutation
through a nested closure.

## Validation

- Confirmed that direct parameter mutation fails on unmodified `hkmc2`.
- `ctest` and `sdtest AsyncParameterAssignments`: passed.
- `hkmc2AllTests/test`: 1,132 tests passed.
- Reviewed the complete diff against `hkmc2` and included the generated golden outputs.
