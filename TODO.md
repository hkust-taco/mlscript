
# TODO: Case-of-case optimization

We want to optimize successive Match blocks where all of the following hold:
  * the branches of the previous match assign known constructors to some variable, except at most one branch which can be assigning an unknown value or not assigning at all to this variable
  * the second match scrutinizes that variable and either:
    * the branches of the second match can be inlined into the first match without introducing any code duplication; or
    * the branches that would be duplicated are below the inlining threshold
  * all the statements between the two matches are pure and can thus be moved out of the way, similar to how `MergeMatchArmTransformer` works (in `hkmc2/shared/src/main/scala/hkmc2/codegen/Lowering.scala`) – we can reuse the `TrivialStatementsAndMatch` extractor

The relevant test file, to be used to track progress on this task, is `hkmc2/shared/src/test/mlscript/opt/CaseOfCase.mls`.


# Notes

Please add any important design notes, problems you encounter, decisions you made, and partial progress notes below.

---

Implemented in `BlockSimplifier.CaseOfCase`.

Design notes:
  * The pass runs after dead-code elimination and value propagation, before each
    inliner round. This lets it see normalized arms from the preceding inliner
    round instead of temporary inliner labels.
  * Constructor knowledge currently covers literals, classes, and objects. It
    uses semantic definitions as a fallback for imported constructors, whose
    more precise MIR symbol information is not always available.
  * At most one unknown producer path is retained with the original consumer
    match. Known paths are specialized around it.
  * Consumer branches are refreshed with `SymbolRefresher` when copied. A copy
    is only allowed when its branch size is at most the configured inlining
    threshold.



