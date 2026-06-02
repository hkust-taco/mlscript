
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




