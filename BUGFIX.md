# PR title

fix: preserve enclosing receivers when inlining module methods

# PR description

Inlining a nested module method can move its body away from an enclosing class or module whose receiver it still references. A nested module captured by a lifted function, or reached through an imported alias, does not necessarily retain a qualifier path to that outer receiver. On `hkmc2`, this can return `undefined` instead of the expected field value or generate JavaScript with an out-of-scope receiver reference.

Check every free receiver required by the method body against the receiver substitutions available at the call site before inlining. Receivers introduced by definitions inside the copied body remain local and are excluded from this check. Also recognize qualifier paths rooted at an explicit `This` value. When an enclosing receiver cannot be substituted, retain the method call and its original lexical context.

This preserves inlining for fully qualified module calls while protecting captured nested modules. Enable the existing nested-instance regression and add an independently compiled module fixture that exercises a lifted recursive worker, mutation of the outer module state, and direct calls through an imported alias. The separate compilation scope prevents the worksheet from accidentally supplying the missing receiver binding.

## Validation

- Reproduced the nested-instance and imported-module failures on unmodified `hkmc2`.
- `ctest`, `sdtest LiftedModuleInlining`, and `dtest InlineModuleMethods` pass.
- `hkmc2AllTests/test`: all 1,133 tests pass.
- Reviewed the complete diff from `hkmc2` and the generated JavaScript; committed the updated golden outputs.
