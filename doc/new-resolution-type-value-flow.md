# Type values, instances, and bounds in new resolution

This note records the semantic requirements and compares possible representations.
The wrapper placement is undecided; the earlier plan to add `TypeValueShape` was
premature. No compiler implementation has been selected. The
[current resolver notes](new-resolution-design.md) describe existing behavior;
the [migration worklist](new-resolution-suite-migration.md) lists remaining ports.

## The distinction to preserve

Supplying a type argument and adding a bound are different operations. If `Int`
is supplied as the type argument for a contextual parameter `A`, it affects both
positive and negative uses of `A`:

```text
A has the supplied type Int:

L <: A    produces    L <: Int
A <: U    produces    Int <: U
```

In contrast, inferring `Int <: A` from an ordinary integer argument only adds a
lower bound. It does not supply `Int` as the meaning of `A` in all positions.
The distinction applies to input and output positions generally. Function
parameters reverse polarity; function results preserve it. Array operations are
one example, not the organizing principle of the design.

If two distinct type values, `Int` and `Str`, reach the same activation of `A`,
each bound is applied to both. A lower bound `L <: A` produces both `L <: Int`
and `L <: Str`; an upper bound `A <: U` produces both `Int <: U` and `Str <: U`.
This differs from supplying the single type value `Int | Str`, against which
constraints must retain the meaning of that union type.

Concrete mismatches such as `Str <: Int` may remain quiet for now. Constraints
must still reach the appropriate types, even when no loud diagnostic is emitted.

## What can be inferred at a generic call

“Preserve wrappers through inferred generic arguments” conflates two cases.

**Inferring bounds from ordinary arguments.** For a function with parameters
`x: A` and `y: A`, supplying an integer and a string contributes lower bounds
`Int <: A` and `Str <: A`. It must not manufacture two supplied type values,
`Int` and `Str`: under the rule above, that would require each argument to satisfy
both types. An ordinary argument's inferred bound is not an exact type argument.

One possible representation introduces a type inference variable `alpha` for
this call. The formal parameter `A` denotes `alpha`, and ordinary arguments add
bounds to `alpha`. A wrapper, if used, would refer to `alpha`, not to each shape
that becomes a lower bound of it. This is a conceptual inference cell, not a
requirement for a fresh global `Symbol`; the existing symbol plus call context
might identify it. Such a cell can retain ordinary shape bounds; this does not
require reconstructing a complete type expression for every closure or value.
Choosing this representation requires an explicit design.

**Matching an existing type argument.** In the motivating `Array[Int]` against
`Array[A]` example, the actual array already carries an element type. Matching
must preserve that type's meaning in both input and output uses of `A`, rather
than extract integer instance shapes and forward only those lower bounds.
Likewise, an array with an inferred element parameter `E` must retain a live
reference to `E`, including its future constraints. Merely copying `E`'s current
positive candidates loses this information.

This does not establish a rule that every nominal type-argument match binds an
exact type. The treatment of a parameter used only covariantly or contravariantly
must follow the chosen matching/variance rules. Neither wrapper placement by
itself determines those rules.

## Option 1: wrap type values

Use `TypeValueShape(T)` for a type carried by the flow graph. Both ends of a
type-value constraint should be represented explicitly:

```text
TypeValueShape(Int) <: TypeValueShape(A)
```

Here the outer `<:` is the graph's relation between type-valued shapes. Its
processing rule must preserve both uses of the supplied type. It must not simply
strip the wrappers and install the ordinary lower bound `Int <: A`.
The earlier notation `TypeValueShape(Int) -> A` described publication into a
parameter host while leaving the host's meaning implicit. It was not an adequate
specification of a constraint between shapes.

The wrapper must refer to a type description or a contextual type parameter,
including its originating host. It needs an explicit interpretation on both
sides of a constraint. Ordinary values described by that type remain represented
separately, through the existing instance shapes or another explicit operation.
For example, a parameter annotated `x: A` expects an instance of `A`, not a type
value; wrapping the type argument alone does not represent that expectation.

Advantages:

- Type arguments have an explicit tag when sharing transport with ordinary value
  shapes. This makes accidental publication of an instance as a type argument
  detectable.
- Explicit type application and forwarding of existing type arguments have a
  direct representation, including nested type expressions and captured type
  parameters.
- The current graph uses `Publisher.Data[Shape]`, so a new type-valued alternative
  can fit that transport, provided the context operations are extended as well.

Costs:

- A symmetric source/target interpretation is needed; a wrapper around published
  candidates alone is insufficient.
- Ordinary annotated values still need a separate representation or conversion.
  Function constraints, member selection, and mixed type/value constraints must
  consistently distinguish the two levels.
- `ShapeLike.enter` and `exit` currently return `TermShape | NoShape`. Transporting
  type-valued wrappers requires changing that contract or representing their
  contexts separately.
- Ordinary inference still needs a model for bounds. Wrapping every observed
  instance shape would incorrectly turn inferred lower bounds into supplied types.

## Option 2: wrap instances described by types

Keep type descriptions as types and use `InstanceShape(T)` for an ordinary value
view described by `T`. The wrapper can occur in positive or negative position;
its name does not restrict it to a producer.

```text
shape of an integer <: InstanceShape(A)
    contributes an integer lower bound to A

InstanceShape(A) <: an expected value interface
    constrains A in the corresponding output use
```

With `Int` supplied for `A`, these operations use `Int` in the appropriate
polarity. A value viewed through `InstanceShape(Base)` exposes `Base`'s interface;
a supplied `Child` produces a constraint against `Base` without replacing that
view with `Child`'s more specific interface.

In this representation, matching
`InstanceShape(Array[Int])` against `InstanceShape(Array[A])` reaches a relation
between the element types. It must implement the agreed `Array` behavior above.
The instance wrapper alone does not decide whether a nested relation is a type
binding, a lower/upper bound, or both bounds for an invariant parameter.

Advantages:

- The conversion from a type description to an ordinary value use is explicit.
  Parameter annotations, result annotations, and member interfaces all use the
  same distinction, in either polarity.
- This is close to the existing split between `TypeShape`/`DeclaredType` and
  `TermShape`. Despite its name, `NominalTypeShape` is already a `TermShape`
  describing an instance; its description is “value of type ...”.
- A live `InstanceShape(A)` can retain the type reference while `A` is unresolved,
  instead of immediately expanding it into whichever instance candidates happen
  to be known. This may make delayed constraints easier to handle, though it
  still requires an order-independent propagation rule.
- It provides a natural place to distinguish an annotated value's permitted
  interface from a more specific implementation shape.

Costs:

- Type-argument flow still needs an explicit representation or API. Removing
  `TypeValueShape` does not make ordinary `T <: A` lower-bound propagation stand
  for type instantiation.
- `NominalTypeShape`, `CallableTypeShape`, `RecordTypeShape`, and annotated tuples
  already provide specialized instance views. A general wrapper must organize or
  reuse these views, rather than add a second path with different behavior.
- Contexts for the type reference and for the ordinary value must remain correct
  when the type contains captured parameters or an instance is passed through a
  function. Moving the wrapper does not remove this requirement.
- Positive and negative interpretation cannot use the same eager expansion for
  every type constructor. Function parameters reverse direction; union and
  intersection constraints need their own rules.

## Comparison and current recommendation

| Concern | Type-value wrapper | Instance wrapper |
| --- | --- | --- |
| Boundary made explicit | A type enters the shared shape graph. | A type describes an ordinary value use. |
| Existing type-argument matching | Directly carries type-valued shapes. | Uses type references and a separate matching operation. |
| Annotated term values | Retains existing instance views or adds a conversion. | Directly represented by the wrapper. |
| Ordinary generic inference | Needs bounds distinct from supplied type values. | Needs bounds distinct from supplied type values. |
| Fit with current representations | Extends the shared shape transport. | Builds on the current type-description/instance-view split. |

The current recommendation is to explore the instance wrapper first, because it
makes the meaning of annotated term shapes explicit and fits the existing type
interpretation graph. This is a preference, not an implementation decision.
A type-value wrapper remains useful if representing types inside the same shape
constraint language is a deliberate goal. The representations can also coexist,
but adding both needs a demonstrated use for each boundary.

The more fundamental unresolved choice is how a formal type parameter denotes an
inferred type. Two approaches merit a small comparison:

- Keep supplied type values and ordinary lower/upper bounds as distinct kinds of
  information on the contextual parameter. Constraints must be replayed as type
  values arrive; positive observations must not become dependent on arrival order.
- Let an omitted argument denote an inference cell whose bounds are accumulated.
  The formal parameter refers to that cell, while explicit arguments refer to
  their supplied types. Matching an existing type argument then constrains or
  binds that cell according to the matching rule.

The second approach gives a clear meaning to a wrapper around an inferred type:
it wraps a reference to the cell. It does not establish that this is the smallest
or best change to this resolver. Neither approach should be selected merely to
make the current array regression pass.

## Next design and implementation steps

1. Specify the rules for supplying a type argument, adding lower/upper bounds,
   and using a type to describe a value. Use separate operation names while
   comparing the designs; choose any overloaded `<:` notation only after the
   kinds of its operands determine the rule unambiguously.
2. Work through explicit `identity[Int](...)`, inference from two ordinary
   arguments, `Array[Int]` against `Array[A]`, an initially empty mutable array,
   and a callback using the same parameter in both polarities. Include constraints
   arriving before and after the type argument and its observers.
3. Choose the inference-variable representation and wrapper placement from those
   derivations before changing compiler code. Retain existing context identities
   and consumer-owned hosts; a new symbol per mutable array is unnecessary.
4. Update `applyTypeArguments`, nominal argument matching in `inferTypeArguments`,
   and annotation interpretation together. Split the ambiguously named
   `listenTypeValues`, which currently returns positive instance shapes. Replace
   constraint suppression for explicit arguments with delivery to the supplied
   type. Audit the snapshot conversion in `instanceBindings` as well.
5. Verify constraints in both polarities, multiple supplied type values versus one
   union type, ordinary inferred bounds, aliases, recursive propagation, separate
   calls, and separate importers. Check constraint delivery directly when a loud
   mismatch diagnostic is intentionally absent. Preserve generic-body checks,
   exposed-function checking, and completed-reference targets.
6. Make `appendTyped` in `newres/MutableArrays.mls` pass using the common mechanism.
   Run `ctest` before focused worksheets and `hkmc2AllTests/test` before completion;
   review and commit the golden outputs.

Precise array positions/lengths, loud concrete-mismatch diagnostics, optional
`splice` arguments, general storage reassignment, and handler inference remain
separate work.
