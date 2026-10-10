NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# Lexical paths in resolution

This note gives the scope calculus used by `Shape.scala`, the invariant needed
by its assertions, and the obligations on operations that construct paths.
The paths describe lexical environments, not the runtime call stack.

## Scopes and endpoints

Contract the source's scope tree to the boundaries represented by resolution:
function and method bodies, and class instance bodies. A constructor and its
class name the same boundary. Local blocks, anonymous lambdas, modules, and
objects do not add boundaries in this analysis; their bindings live at the
nearest represented scope. In particular, a type alias performs substitution
and has no value activation. `OuterCtx.resolutionBoundary` makes this decision
at elaboration, before either term or type references are constructed.

Each inference host has one lexical endpoint. An ordinary parameter's host is
inside its function; a class parameter's host is inside its instance scope.
Instantiating a type parameter changes the host's identity, not this endpoint.
An argument reaches the parameter by traversing the reverse of the callable's
path to the caller. A result traverses that same path forward. Recursion goes
out of one activation and into another along the lexical tree; it does not
add another copy of the function to the lexical tree.

A core shape describes a value at its origin. Its marks describe a walk from
that origin to the host observing it. A compound shape may contain references
with their own endpoints: tuple fields, declared type arguments, and the head
of an applied constructor are examples. Moving the compound delays movement of
those references until they are observed; it must not reinterpret their hosts
at the compound's destination.

## Reduction and its proof

Write `E(b, i)` for entering boundary `b` at static site `i`, and `X(b, i)` for
exiting it. An absent site is a wildcard, used for a lexical capture or a
declared interface that does not identify an activation. Here words are written
in execution order; the linked `Marks` representation stores that order reversed.

There is one reduction rule:

```
E(b, i) X(b, j)  =  identity    if i = j or either site is absent
E(b, i) X(b, j)  =  no flow     otherwise
```

The rejected case is an ordinary result of inference, represented by `NoShape`.
It prevents a candidate supplied by one call from returning through an
incompatible call. An entry followed immediately by an exit must name the same
boundary: both steps traverse the edge between the current scope and its parent.
Different boundary names at this point are an incorrectly composed path, not
a reason to discard a possible source program.

An exit followed by an entry is retained, even for two wildcard sites. On an
incoming activation stack it can remove an identified activation and replace
it with an unidentified one. Cancelling this pair would change subsequent
filtering. It also records the provenance of a closure or instance that left
one activation before entering another.

For any finite, well-scoped walk:

1. Each reduction shortens the word by two, so reduction terminates.
2. Removing an entry/exit pair preserves the walk's endpoints. Its stack action
   is the identity when compatible; otherwise no activation can traverse it.
3. A nonempty reduced word has only exits followed by entries. Any later exit
   after an entry would contain another adjacent entry/exit pair.
4. Its exits ascend a tree and its entries descend a tree. Neither run can
   repeat a boundary. Its length is at most the source depth plus destination
   depth, independently of runtime recursion depth.
5. Two reducible pairs cannot overlap, since a crossing cannot be both entry
   and exit. Reductions of disjoint pairs commute, including rejection.
   Thus normalization is independent of grouping, and composition is associative.

These facts establish the three mark assertions for well-scoped walks: adjacent
entry/exit boundaries agree, and neither entries nor exits repeat a boundary.
They apply to arbitrary lexical depth, call-site labels, recursion, and scope
trees, not only to the programs in the test suite. `MarksTest` also compares
generated walks against a separate activation-stack interpreter, including
every prefix and the depth bound. Its purpose is to check the implementation
of the algebra, beyond what a worksheet's final result can observe.

This proof has a necessary premise: edges must be composed at the same lexical
endpoint. Finite marks alone do not establish that premise for compiler code.
The assertions remain enabled to catch a violation by a producer. Suppressing
them, treating a boundary mismatch as `NoShape`, or truncating a repeated scope
would hide an incorrectly located host and could silently change resolution.

## Maintaining the endpoint premise

The producer rules are compositional:

| Operation | Endpoint obligation |
| --- | --- |
| Lexical reference | Elaboration adds one `Capture` per represented boundary between the binding and the use. Explicit `this` follows the same rule. |
| Call or constructor application | Enter argument paths in reverse fragment order; leave results in forward order. Curried lists retain the original callable path. Class and constructor symbols share `ResolutionBoundary`. |
| Assignment | Undo the left-hand reference's captures before publishing to its binding host. |
| Inferred member | Observe its definition through the receiver's path; class fields keep their class parameter endpoint. |
| Declared member | Interpret the signature at its declaration, bind supplied class arguments there, then traverse the member/class exits and the path to the use. |
| Type reference | Retain the selected declaration, its receiver bindings, its substitution, and its path. Identity alone is sufficient for erasure, but not for interpreting free binders. |
| Type application | Move supplied arguments back to the template endpoint before substituting; move the interpreted result forward. Omitted arguments stay at their original inference host. |
| Deferred type projection | Compose transport on the `InstanceShape` reference before observation, including references nested in fields or arguments. |
| Import or activation view | Copy or instantiate hosts without moving their lexical endpoints. |

For declared nominal members, distinguish the receiver's origin from the member's
declaration. A tuple literal can be created inside a function even though its
`Array` methods are declared globally. `splitReceiverPath` partitions the
receiver's leading upward journey: exits from scopes below the declaration's
enclosing scopes belong to the argument bindings' provenance. The remaining
path locates the declaration at the consumer. Tree ancestry makes this a prefix
split; a later exit cannot return to a deeper, unrelated scope. Moving the
member itself through the provenance portion would assign different endpoints
to the same method-parameter host for different receiver candidates.

`TypeShape.Reference` is the common representation for a syntactic capture and
a qualified type selection. It is an **open** expression: the enclosing
declaration can still substitute its free binders. Receiver bindings override
those ambient bindings, and captured instances override ambient instances.
Interpretation closes the expression with `declaredType` and transports the
result with `transportType`. `TypeShape.Contextual`, in contrast, holds an
already interpreted `DeclaredType` with its own bindings and normalized path.
Confusing the two loses the enclosing substitution or applies it twice.

For example, in a generic `make[A]`, a local module can declare `Parent` with a
field of type `A`. A nested `read(x: Types.Parent)` must retain the path from
`Types` to `read`. Dropping it reads `A` in `make` but later tries to leave
`read`, violating the endpoint premise. The same rule applies to an alias,
a nested class, a returned module, or a reference through an imported definition.
Type aliases must also be excluded at elaboration: ignoring an alias capture
only in type interpretation would leave the same fictitious boundary on the
term receiver used by a qualified selection.

## Finite paths and finite inference graphs

Bounded path length does not by itself prove that inference reaches a fixed
point. Core shapes and synthesized type references need stable identities too.
Publishers deduplicate candidates, and synthesized nodes must be memoized by
their semantic inputs before downstream observation can revisit them.

Class-pattern refinement is one such operation. For an unknown input tested
against `Array`, it constructs a declared `Array` interface whose element is
unknown. A recursive `every` callback can send that element back to the same
test. Allocating a fresh element-type host on each visit produces infinitely
many different `Array` candidates even though all paths are bounded.

`patternRefinements` therefore keys the synthesized type by the pattern's syntax
identity, selected class, constructor path, and input shape. The path is part
of the key because the same class can be reached through different captured
activations. For each such tuple there is one refinement graph, installed before
its interface is observed. Revisiting the tuple reuses the graph and publisher
deduplication closes the cycle. Diagnostic provenance does not create new
semantic candidates. The cache lives in `NewResolverState`, so imported graphs
retain the existing consumer-isolation rules.

This is distinct from the regularity check for recursive declared types and
the widening of recursive tuple spreads. Those operations have their own
finiteness arguments; path truncation is not a substitute for either one.

`newres/InheritedTypeArguments.mls`, `ScopePaths.mls`, and `NominalMemberPaths.mls`
exercise declaration endpoints and separate activations. `RecursiveEquality.mls`
checks both deep equality and mutually recursive array callbacks without
expected-failure markers. LazyFingerTree and the parser compilation fixtures
exercise the same rules in larger programs.
