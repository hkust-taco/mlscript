- The paper uses simplified names such as `Rule`, `Tree.Reference`,
  `Tree.Application`, `Token.Symbol`, and bracket-specific token constructors.
  The implementation uses `ParseRule`, `Tree.Ident`, `Tree.App`, and a single
  `Token.Identifier(name, symbolic)` constructor for both word identifiers and
  symbolic tokens.

  We adjusted these names while writing the paper, but we didn't have time to update the code. We also feel that the AST (Abstract Syntax Tree) currently used in the code is too complex, so we'd like you to change it to a simpler AST implementation.
  
  This isn't very urgent. You can continue using the current version for now and then modify it during the final wrap-up phase.

- The paper's core `Ref` has one optional binding-power field. The implementation
  has `Choice.Ref(kind, process, outerPrec, innerPrec, rest)`, with separate
  outer and inner precedence thresholds. The implementation also has `Siding`
  choices for optional or alternative rule fragments, which the main paper
  presentation does not foreground.

  As we have gradually found that the second precedence (inner prec) is not very useful, I would like you to modify the implementation to align it with the paper.

  For `Siding`, Please draft a request to perform the following tasks:
  
  We did not include "siding" in the paper because we discovered it can be composed using other choices. Therefore, siding should be treated as a separate helper function that generates rules with the same effect.
  
  Please handle the following refactoring: reconstruct siding as a standalone helper function; remove the current implementation of siding from the codebase.

- The paper describes an `afterRef` helper as the continuation extracted from a
  rule. The implementation does not expose that name. Equivalent behavior is
  split between `ParseRule.refChoice`, the self-reference loop in `parseKind`,
  and the specialized `exprCont` loop.

  Right, this also needs to be changed to be consistent with the paper.

- The paper says terms and types keep separate `expr`/`exprCont` and
  `typeExpr`/`typeExprCont` pairs. The implementation has one parameterized
  `expr` and `exprCont` pair, selected by `termOptions` and `typeOptions`.

  Right. Initially, during the implementation for our previous paper, we thought we could unify them through parameterization. However, we now feel that this isn't as easy to achieve as we expected.
  
  For now, please proceed with the implementation using the current separate pairs method. We will look into unification at a later stage.

- The paper proposes a future or ideal `Infix` choice that would make
  precedence-driven symbolic operators part of the rule representation. The
  implementation still handles symbolic infix operators directly inside
  `exprCont` through `Keywords.opPrecOpt`.

  Yes, this also needs to be implemented by you. You will need to modify the implementation to include the infix choice.
  
  By doing this, we will be able to perform unification on the separate pairs mentioned above.

- The paper's simple Pratt section includes prefix operators and a `prefixPower`.
  `Parser.mls` does not implement symbolic prefix operators in that same form;
  symbolic identifiers are parsed as identifiers when term options permit them,
  and infix use is handled later by `exprCont`.

  That is correct; this is indeed one of our current shortcomings.
  
  However, we recall that Camlite (the Caml Light programming language) doesn't seem to have prefix precedence. Therefore, you need to verify whether this is actually the case at the very end.
  
  If prefix operators in Camlite do have precedence, we will need to add that functionality as well. Please conduct an investigation into this first, but do not start any implementation yet.

- The dynamic extension syntax differs. The paper sketches directives like
  `#keyword` and `#extend` with labeled fragments and replacement expressions.
  The implementation accepts `#newKeyword`, `#newCategory`, and
  `#extendCategory`. Its `parseChoiceTree` parses a tuple of target kind,
  bracketed keyword/category sequence, and a function identifier; it then builds
  nested applications of that function rather than performing the replacement
  scheme shown in the paper.

  This needs to be identical to the implementation in the paper.

- The paper mentions built-in terminal kinds such as `literal` or
  `string-literal`. `Parser.mls` only has built-in `ident` and `typevar`
  categories in `parseKind`; literals are accepted by the term/type `expr`
  routine rather than as a generic dynamically referenceable syntax kind.

  Indeed, that is correct. In an ideal scenario, most elements could be implemented through a comprehensive set of rules—such as expressions and types—combined with a rich variety of built-in terminal kinds.
  
  However, at this stage, only "ident" and "type var" are recognized as built-in terminal kinds.
  
  Because of this limitation, you need to develop a proposal to handle the current situation.

- The paper claims railroad diagrams plus a precedence table as generated
  specifications. The implementation has `ParseRuleVisualizer` for railroad
  diagrams, but no corresponding precedence-table renderer is visible in the
  parsing or web-demo source.

  Correct, you should add this implementation at the very end.
  
  Since this part of the implementation is relatively separate, you can just include it when you're finishing up the project and building the web demo.

- The paper's introduction says the implementation covers the full Caml Light
  language, with slight adaptations. The checked-in parser covers a broad
  Caml-like subset and the tests include substantial Caml examples, but the
  source still has ad-hoc top-level handling and visible gaps: for example,
  `class` is registered as a keyword but has no rule in `Rules.mls`, patterns are
  parsed through term rules, and some top-level `let` behavior is manually
  repaired in `Parser.mls`.

  The use of "class" as a keyword is actually an error, so you need to delete it. At the same time, please check if there are any other registered keywords that are not being used; if there are, delete those as well.
  
  Regarding the "pattern" implementation: for now, let's implement it this way, in the future, I would like you to treat "pattern" as a separate syntax kind and establish a dedicated series of rules for it.
  
  As for the top-level "let," just leave it where it is for now. We will discuss how to modify it later.
