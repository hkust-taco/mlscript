# Generalized Pratt Parser Notes

This note summarizes the parser implementation in
`hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`, the approach
described by the generalized Pratt parsing paper source at
`/Users/chengluyu/Developer/generalized-pratt-parsing/paper.tex`, and the main
inconsistencies between them.

## Implementation Structure

The parsing app is organized as a small Caml Light-like parser compiled through
the `mlscript-compile/apps/parsing` test app. The main data flow is:

1. `Lexer.mls` turns source text into a stack of tokens.
2. `Parser.mls` consumes that token stack and produces `Tree.mls` AST nodes.
3. `Rules.mls` defines the initial grammar-like rule graph for terms, types,
   declarations, and helper categories.
4. `ParseRule.mls` defines the reified rule representation interpreted by the
   parser.
5. `Extension.mls` mutates the keyword and syntax-kind registries when parsed
   directives request syntax extensions.
6. `ParseRuleVisualizer.mls` renders the same rule objects as railroad
   diagrams for the web demo.

The web demo in `mlscript-compile/apps/parsing-web-demo` reuses the same parser.
`main.mls` lexes editor text, calls `Parser.parse`, renders collapsible syntax
trees, catches runtime errors, and renders syntax diagrams through
`ParseRuleVisualizer.render`. `Examples.mls` supplies a Caml Light Hanoi example
and an extensible-syntax example.

## `Parser.mls`

`Parser.parse(tokens)` is a closure-based parser. It stores the remaining tokens
in a mutable variable, tracks a consumed-token counter for tracing, and defines
all parsing routines locally. `consume` advances the token stream and writes to
the `TreeTracer` when tracing is enabled.

`parseKind(kind, prec)` is the dispatcher for syntax categories. It has special
cases for `term`, `type`, `ident`, and `typevar`. `term` and `type` delegate to
the Pratt-shaped `expr` routine with different options; identifiers reject
registered keywords; type variables require names starting with `'`. Any other
kind is looked up in `Rules.syntaxKinds` and interpreted by `parseRule`. If the
kind's rule begins with a self-reference, `parseKind` loops over the continuation
rule to support direct left-recursive shapes such as repeated postfix or infix
extensions.

`parseRule(prec, rule)` interprets `ParseRule.ParseRule` objects. It first checks
keyword choices: if the next token names a registered keyword and the current
rule has a matching `Keyword` choice, the parser consumes the keyword and parses
the rest of that rule. Otherwise, it checks the rule's first `Ref` choice. A
`Ref` names another syntax kind, has a process function, has optional outer and
inner precedence thresholds, and has a rest rule. The parser only follows the
reference when its outer precedence is above the current threshold. If no keyword
or reference applies, `parseRule` returns the rule's `End` value when available;
otherwise it emits a `Tree.Error`.

`expr(prec, options)` is the Pratt atom parser for both terms and types.
`termOptions` allow symbolic operators and literals; `typeOptions` reject
symbolic identifiers but allow literals. For a keyword token, `expr` consults the
current kind's keyword choices and only parses the keyword-led form when the
keyword's left precedence is high enough. For non-keyword identifiers and
literals, it constructs `Tree.Ident` or `Tree.Literal`, then calls `exprCont`.

`exprCont(acc, prec, options)` is the Pratt continuation loop. It extracts the
self-reference continuation from the current kind's rule and then tries three
kinds of continuations:

1. Infix keyword rules, such as `:`, `.`, `;`, `,`, `==`, `*`, and application
   rules represented in `Rules.mls`.
2. Symbolic infix operators, using `Keywords.opPrecOpt` to compute left and
   right binding powers from the operator spelling.
3. Term-start continuations, most importantly ML-style function application,
   where another term following the accumulated term becomes an argument.

The top-level `mod` and `modCont` routines parse whole modules. They skip `;;`,
try term-led constructs before declaration rules, convert a `let ...` with no
body into a top-level `Tree.Define`, and route directives through
`handleDirective`. `handleDirective` recognizes `#newKeyword`, `#newCategory`,
and `#extendCategory`; those directives mutate the global keyword and syntax-kind
registries, then continue parsing without returning the directive as a regular
AST node.

## Paper Approach

The paper presents Pratt parsing as a disciplined form of recursive descent.
The core idea is that parsing first reads an atom, then repeatedly extends it
with continuations whose left binding power is above the current threshold.
Using separate left and right binding powers makes precedence and associativity
data-driven. The paper also proposes determining multi-character operator powers
from the first and last characters of an operator, so asymmetric operators like
`|>` and `<|` can behave symmetrically.

The paper then generalizes the operator table into a first-class rule
representation. A syntax kind is similar to a grammar nonterminal, but it is
implemented as an extensible `Rule` made from `Choice` values. The key choices
are:

- `End`, which accepts the empty continuation and returns a value.
- `Keyword`, which consumes a specific keyword and continues with another rule.
- `Ref`, which parses another syntax kind under a binding-power threshold and
  combines that result through a process function.

The generalized parser keeps the Pratt control flow but reifies more of the
language definition. `parseKind` dispatches on syntax kinds, `parseRule`
interprets rule objects, and the continuation logic is derived from reference
choices. This keeps syntax modular and inspectable while preserving the ability
to insert custom recursive-descent logic where the language demands it.

The paper also emphasizes dynamic extensibility: programs can add keywords,
syntax kinds, and syntax rules while being parsed. Because rules are data, the
same definitions can be used to generate user-facing railroad diagrams and, in
principle, precedence tables.

## Inconsistencies

The paper's exposition and the checked-in parser are clearly related, but they
are not the same artifact.

- The paper uses simplified names such as `Rule`, `Tree.Reference`,
  `Tree.Application`, `Token.Symbol`, and bracket-specific token constructors.
  The implementation uses `ParseRule`, `Tree.Ident`, `Tree.App`, and a single
  `Token.Identifier(name, symbolic)` constructor for both word identifiers and
  symbolic tokens.

- The paper's core `Ref` has one optional binding-power field. The implementation
  has `Choice.Ref(kind, process, outerPrec, innerPrec, rest)`, with separate
  outer and inner precedence thresholds. The implementation also has `Siding`
  choices for optional or alternative rule fragments, which the main paper
  presentation does not foreground.

- The paper describes an `afterRef` helper as the continuation extracted from a
  rule. The implementation does not expose that name. Equivalent behavior is
  split between `ParseRule.refChoice`, the self-reference loop in `parseKind`,
  and the specialized `exprCont` loop.

- The paper says terms and types keep separate `expr`/`exprCont` and
  `typeExpr`/`typeExprCont` pairs. The implementation has one parameterized
  `expr` and `exprCont` pair, selected by `termOptions` and `typeOptions`.

- The paper proposes a future or ideal `Infix` choice that would make
  precedence-driven symbolic operators part of the rule representation. The
  implementation still handles symbolic infix operators directly inside
  `exprCont` through `Keywords.opPrecOpt`.

- The paper's simple Pratt section includes prefix operators and a `prefixPower`.
  `Parser.mls` does not implement symbolic prefix operators in that same form;
  symbolic identifiers are parsed as identifiers when term options permit them,
  and infix use is handled later by `exprCont`.

- The dynamic extension syntax differs. The paper sketches directives like
  `#keyword` and `#extend` with labeled fragments and replacement expressions.
  The implementation accepts `#newKeyword`, `#newCategory`, and
  `#extendCategory`. Its `parseChoiceTree` parses a tuple of target kind,
  bracketed keyword/category sequence, and a function identifier; it then builds
  nested applications of that function rather than performing the replacement
  scheme shown in the paper.

- The paper mentions built-in terminal kinds such as `literal` or
  `string-literal`. `Parser.mls` only has built-in `ident` and `typevar`
  categories in `parseKind`; literals are accepted by the term/type `expr`
  routine rather than as a generic dynamically referenceable syntax kind.

- The paper claims railroad diagrams plus a precedence table as generated
  specifications. The implementation has `ParseRuleVisualizer` for railroad
  diagrams, but no corresponding precedence-table renderer is visible in the
  parsing or web-demo source.

- The paper's introduction says the implementation covers the full Caml Light
  language, with slight adaptations. The checked-in parser covers a broad
  Caml-like subset and the tests include substantial Caml examples, but the
  source still has ad-hoc top-level handling and visible gaps: for example,
  `class` is registered as a keyword but has no rule in `Rules.mls`, patterns are
  parsed through term rules, and some top-level `let` behavior is manually
  repaired in `Parser.mls`.

Overall, the repository implementation is best read as a working prototype of
the paper's generalized Pratt architecture. It already reifies keyword and
reference rules, supports dynamic extension, and renders diagrams, but it still
keeps several practical shortcuts and older naming/design choices that the paper
either simplifies away or presents as future cleanup.
