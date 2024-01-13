This file will be deleted after we migrate all test cases and fixed all
problems located by test cases.

- [x] shared/src/test/diff/codegen/AuxiliaryConstructors.mls
- [x] shared/src/test/diff/codegen/Mixin.mls
      Fix that `PreTyper` does not traverse type definitions.
- [x] shared/src/test/diff/codegen/MixinCapture.mls
- [x] shared/src/test/diff/codegen/Nested.mls
- [x] shared/src/test/diff/codegen/NewMatching.mls
      Destructing unparameterized class no longer causes code generation errors.
- [x] shared/src/test/diff/codegen/ValLet.mls
- [x] shared/src/test/diff/ecoop23/ComparePointPoly.mls
      Desugar UCS shorthands in `PreTyper`.
- [x] shared/src/test/diff/ecoop23/ExpressionProblem.mls
- [x] shared/src/test/diff/ecoop23/Intro.mls
- [x] shared/src/test/diff/ecoop23/PolymorphicVariants.mls
- [x] shared/src/test/diff/ecoop23/SimpleRegionDSL_annot.mls
- [x] shared/src/test/diff/ecoop23/SimpleRegionDSL_raw.mls
- [x] shared/src/test/diff/fcp/QML_exist_nu.mls
- [x] shared/src/test/diff/gadt/Exp1.mls
- [x] shared/src/test/diff/gadt/Exp2.mls
- [x] shared/src/test/diff/gadt/ThisMatching.mls
- [x] shared/src/test/diff/nu/Andong.mls
- [x] shared/src/test/diff/nu/ArrayProg.mls
- [x] shared/src/test/diff/nu/BadUCS.mls
      Add many `:ge` to cases where match scrutinee against mixins.
      Add dummy class symbol so that we don't need to throw any
      errors during desugaring.
- [x] shared/src/test/diff/nu/BasicClassInheritance.mls
- [x] shared/src/test/diff/nu/BasicClasses.mls
- [x] shared/src/test/diff/nu/CaseExpr.mls
- [x] shared/src/test/diff/nu/ClassSignatures.mls
- [x] shared/src/test/diff/nu/ClassesInMixins.mls
      Improve error messages in `PreTyper`.
- [x] shared/src/test/diff/nu/CommaOperator.mls
- [x] shared/src/test/diff/nu/CtorSubtraction.mls
- [x] shared/src/test/diff/nu/Eval.mls
- [x] shared/src/test/diff/nu/EvalNegNeg.mls
- [x] shared/src/test/diff/nu/ExpressionProblem_repro.mls
- [x] shared/src/test/diff/nu/ExpressionProblem_small.mls
- [x] shared/src/test/diff/nu/FilterMap.mls
- [x] shared/src/test/diff/nu/FlatIfThenElse.mls
- [x] shared/src/test/diff/nu/FlatMonads.mls
- [x] shared/src/test/diff/nu/FunnyIndet.mls
- [x] shared/src/test/diff/nu/GADTMono.mls
- [x] shared/src/test/diff/nu/GenericClasses.mls
- [x] shared/src/test/diff/nu/GenericModules.mls
- [x] shared/src/test/diff/nu/HeungTung.mls
- [x] shared/src/test/diff/nu/Huawei1.mls
- [x] shared/src/test/diff/nu/InterfaceMono.mls
- [ ] shared/src/test/diff/nu/Interfaces.mls
      What? Traits can't be patterns?
- [x] shared/src/test/diff/nu/LetRec.mls
- [x] shared/src/test/diff/nu/ListConsNil.mls
- [x] shared/src/test/diff/nu/LitMatch.mls
- [x] shared/src/test/diff/nu/MissingTypeArg.mls
- [x] shared/src/test/diff/nu/NamedArgs.mls
- [ ] shared/src/test/diff/nu/New.mls **OLD**
- [x] shared/src/test/diff/nu/NewNew.mls
- [x] shared/src/test/diff/nu/Object.mls
- [x] shared/src/test/diff/nu/OpLam.mls
      Function `extractParameters` no longer raise errors.
- [x] shared/src/test/diff/nu/OptionFilter.mls
- [x] shared/src/test/diff/nu/OverrideShorthand.mls
- [x] shared/src/test/diff/nu/ParamPassing.mls
- [x] shared/src/test/diff/nu/PolymorphicVariants_Alt.mls
- [x] shared/src/test/diff/nu/PostHocMixinSignature.mls
- [x] shared/src/test/diff/nu/PrivateMemberOverriding.mls
- [x] shared/src/test/diff/nu/SelfRec.mls
- [x] shared/src/test/diff/nu/Subscripts.mls
- [x] shared/src/test/diff/nu/TODO_Classes.mls
- [x] shared/src/test/diff/nu/Unapply.mls
- [x] shared/src/test/diff/nu/UndefMatching.mls
- [x] shared/src/test/diff/nu/WeirdUnions.mls
- [x] shared/src/test/diff/nu/i180.mls
- [ ] shared/src/test/diff/nu/repro0.mls
      - `PreTyper` does not accept top-level `val` bindings.
- [x] shared/src/test/diff/nu/repro1.mls
- [x] shared/src/test/diff/nu/repro_EvalNegNeg.mls
- [x] shared/src/test/diff/nu/repro_PolymorphicVariants.mls
- [x] shared/src/test/diff/pretyper/ucs/examples/JSON.mls
- [x] shared/src/test/diff/pretyper/ucs/examples/LispInterpreter.mls
- [x] shared/src/test/diff/pretyper/ucs/examples/Option.mls
- [x] shared/src/test/diff/pretyper/ucs/examples/STLC.mls
- [x] shared/src/test/diff/ucs/AppSplits.mls
- [x] shared/src/test/diff/ucs/CrossBranchCapture.mls
      Fix the mentioned problems.
      TODO: Warn duplicated pattern bindings.
- [ ] shared/src/test/diff/ucs/DirectLines.mls **OLD**
- [x] shared/src/test/diff/ucs/ElseIf.mls
- [ ] shared/src/test/diff/ucs/ErrorMessage.mls **OLD**
- [x] shared/src/test/diff/ucs/Exhaustiveness.mls
- [ ] shared/src/test/diff/ucs/Humiliation.mls **OLD**
- [x] shared/src/test/diff/ucs/Hygiene.mls
      Problem fixed!
- [ ] shared/src/test/diff/ucs/HygienicBindings.mls
- [ ] shared/src/test/diff/ucs/InterleavedLet.mls **OLD**
- [x] shared/src/test/diff/ucs/JSON.mls
      Deleted. This one is not completed and we have a new version.
- [x] shared/src/test/diff/ucs/LeadingAnd.mls
- [x] shared/src/test/diff/ucs/LitUCS.mls
- [x] shared/src/test/diff/ucs/MultiwayIf.mls
- [ ] shared/src/test/diff/ucs/NestedBranches.mls
      Found a bug in transformation.
- [x] shared/src/test/diff/ucs/NestedOpSplits.mls
- [x] shared/src/test/diff/ucs/NestedPattern.mls
- [x] shared/src/test/diff/ucs/NuPlainConditionals.mls
- [x] shared/src/test/diff/ucs/Or.mls
- [ ] shared/src/test/diff/ucs/OverlappedBranches.mls **OLD**
- [x] shared/src/test/diff/ucs/ParseFailures.mls
- [x] shared/src/test/diff/ucs/PlainConditionals.mls
      Maybe we should keep this old one...
- [x] shared/src/test/diff/ucs/SimpleUCS.mls
      Migrate this test case to new defintion typing.
      Remove a `???` and raise error during transformation.
- [x] shared/src/test/diff/ucs/SplitAfterOp.mls
      Wrap tests in functions so that errors are clearer.
- [ ] shared/src/test/diff/ucs/SplitAnd.mls
      Should report missing else branches.
- [x] shared/src/test/diff/ucs/SplitAroundOp.mls
- [x] shared/src/test/diff/ucs/SplitBeforeOp.mls
- [x] shared/src/test/diff/ucs/SplitOps.mls
- [x] shared/src/test/diff/ucs/SplitScrutinee.mls
      Fixed.
- [x] shared/src/test/diff/ucs/ThenIndent.mls
- [x] shared/src/test/diff/ucs/Tree.mls
- [ ] shared/src/test/diff/ucs/TrivialIf.mls **OLD**
- [ ] shared/src/test/diff/ucs/WeirdIf.mls
      Should report redundant cases.
- [ ] shared/src/test/diff/ucs/WeirdSplit.mls **OLD**
- [ ] shared/src/test/diff/ucs/Wildcard.mls
      Some unexpected empty splits.
- [x] shared/src/test/diff/ucs/zipWith.mls