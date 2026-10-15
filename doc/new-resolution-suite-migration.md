NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# New-resolution suite migration

Remaining migration gaps are recorded below and in the corresponding `.mls`
regressions. Language rules are in the [language reference](reference.md#resolution-interfaces),
and implementation contracts are in the [design notes](new-resolution-design.md).

## Remaining compilation fixtures

| Fixtures | Remaining work |
| --- | --- |
| `CSP`, `QuoteExample1` | Quasiquote type selections and wildcard-reference lowering are unsupported. |
| `parsing/Lexer` | Token constructors with trailing `using` parameters need automatic contextual argument insertion. `newres/LexerMigration` reproduces the missing behavior. |
| `parsing/ParseRule` | Recursive rule inference exceeds the compilation time limit when compiling consumers. Callback inputs exposed by `Iter.mapping` also leave `rule.map` with an unknown receiver. |
| `nofib/sorting` | New resolution exceeds the compilation time limit, including with the required `int_of_char(c: Str)` parameter annotation. |

## Remaining worksheet constraints

Legacy worksheets require more than enabling the language configuration. The
following constraints identify the current failing behavior and representative tests.

- **Contextual calls and module checks:** `basics/CompanionModules_Classes` can
  produce a function instead of the completed result because implicit `using`
  arguments are not inserted. Several `ctx` and module worksheets also lose
  required negative diagnostics. `basics/CyclicModuleForwarders` needs a decision
  about nominal module-forwarding compatibility. Passing contextual arguments
  explicitly would bypass the feature these tests exercise.
- **Constructor and anonymous-object interfaces:** `codegen/ParamClasses`,
  `basics/ValMemberSymbols`, and `lifter/AnonClasses` exercise constructor members, partially
  constructed objects, or anonymous refinements that lack the required interfaces.
  `lifter/PrivateMutableFields` cannot resolve anonymous `new with` expressions.
- **Mutation and returned shapes:** `codegen/SetStmt` retains an initializer's
  tuple length after reassignment (`newres/MutationFlow`). `basics/Records` needs
  callable result precision across branches with different parameter lists.
  `std/LazyFingerTreeTest` loses the private view interface through slicing helpers;
  its general slice result also includes finger trees without `materialize`.
- **Generators:** `codegen/Generators` needs the iterator interface produced by
  generator lowering. `newres/GeneratorResults` records the unresolved `.next`.
- **Handlers:** handler-generated receiver and member references remain unresolved
  in `handlers`, `codegen/ScopedBlocksAndHandlers`, and handler cases in `lifter`.
  Receiver flow, resumption arguments, and abortive results need distinct handling
  (`newres/HandlerResults`).
- **Tail-call annotations and staged functions:** `tailrec/Annots` needs `@tailcall`
  support for getter references and contains an unresolved handler receiver.
  `block-staging/Functions` and `codegen/FirstClassFunctionTransform` encounter
  unfinished generated symbols.
- **Legacy flow analysis:** the `flows` worksheets run a separate flow pass that
  does not handle new-resolution selections and can throw on `NewSel` nodes.
- **Runtime instrumentation and privacy:** `codegen/ObjectMethodDebinding` loses
  an expected runtime error. `codegen/PrivateMembers` loses privacy diagnostics
  and required runtime errors. These worksheets must preserve their checks.
- **Pattern values and transformations:** `ucs/patterns/where`, `ups/MatchResult`,
  `ups/SimpleTransform`, `std/RenderingTest`, and regex worksheets use pattern
  values or direct `.unapply`/`.unapplyStringPrefix` access. Range and higher-order
  transformations lack result interfaces in `ups/examples/Computation` and
  `ups/examples/ListPredicates`. `ups/examples/EvaluationContext2` and the
  Hindley–Milner worksheets additionally need recursive member interfaces.
- **Quasiquotes:** `codegen/Quasiquotes` needs type-selection and generated-reference
  support. Pattern and quote lowering must preserve source targets and receiver paths.

Focused coverage for capture identity and nominal interfaces is in `newres/CtxSens`,
`ValCtxSens`, `Projections`, `RecursiveEnvironment`, `SpreadCalls`, `ScopePaths`,
`InheritedTypeArguments`, and `InterfaceExposure`. These tests constrain fixes to
recursive and exposed interfaces; unknown shapes must not silently become dynamic.
`newres/RecursiveGetters` covers cyclic getter inference, productive results,
captured and generic activations, imports, and invalid member access.

Host-interface precision still needs work for `Array.concat`, `Array.splice`, and
`Array.from`. `Array.reduce` without an initial accumulator also needs a signature
that includes the element type; declared methods cannot overload by arity.
`newres/MutableArrays` covers the missing insertion constraint for `splice`.
