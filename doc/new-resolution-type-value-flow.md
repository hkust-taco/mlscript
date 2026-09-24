# Type values and value constraints in new resolution

This is the proposed design and implementation plan for separating type-value
flow from constraints on ordinary values. It is not implemented yet. The
[current resolver notes](new-resolution-design.md) describe the implementation;
the [migration worklist](new-resolution-suite-migration.md) lists remaining ports.
The flow rules below are the agreed design; the Scala representation and migration
steps are proposals for implementing it.

## Type-value flow is different from bound propagation

There are three distinct relationships. Here `L` and `U` denote bounds; an
ordinary value's shape can supply such a bound without first being converted into
an explicit type value.

| Relationship | Meaning |
| --- | --- |
| `TypeValueShape(T)` flows into `A` | The type `T` supplies the meaning of `A` in both input and output uses. |
| `L <: A` | `L` is a lower bound of `A`: positive information about values supplied for `A`. |
| `A <: U` | `U` is an upper bound of `A`: a negative requirement on values described by `A`. |

The first relationship is not a lower-bound or output flow. Once the type value
`Int` has reached `A`, both of the following rules apply:

```text
TypeValueShape(Int) -> A

L <: A    produces    L <: Int
A <: U    produces    Int <: U
```

This is about inputs and outputs of types, including positive and negative
positions inside compound types. In a function type `A -> B`, the parameter
position reverses polarity and the result position preserves it. The distinction
must therefore work through function parameters and results, callbacks, nominal
type arguments, and other declared interfaces, not just mutable storage.

Arrays give one example. Matching `Array[Int]` against `Array[A]` sends the type
value `Int` into `A`. Inserting a string then supplies the lower-bound constraint
`Str <: A`, which reaches `Int` as `Str <: Int`. That operation must create a
constraint, rather than discard the string's contribution or treat `Str` as
another type value assigned to `A`.

Creating the `Str <: Int` constraint does not require a new diagnostic in this
change. Concrete mismatches currently need not report a loud error. The required
change is that the constraint reaches the supplied type.

## The role of TypeValueShape

`TypeValueShape` represents a type being passed through the flow graph. It knows
how to turn ordinary shape flows involving that type into constraints with the
appropriate direction:

| Operation involving `A`, after it receives `TypeValueShape(T)` | Required behavior |
| --- | --- |
| Propagate a lower bound `L <: A` | Constrain `L <: T`. |
| Propagate an upper bound `A <: U` | Constrain `T <: U`. |
| Forward the type value to another type parameter | Preserve the wrapper and both uses of `T`. |

These operations describe the wrapper's contract, not final Scala method names.
Converting a type to its positive value shapes is still useful for resolving
operations on ordinary values. It is insufficient for passing that type as a
type argument, because that conversion loses its behavior in negative positions.
Likewise, an ordinary value's lower bound must not silently become a fixed type
argument.

If one activation of `A` receives both `TypeValueShape(Int)` and
`TypeValueShape(Str)`, each bound is applied to both type values. For example,
`L <: A` produces `L <: Int` and `L <: Str`; `A <: U` produces `Int <: U` and
`Str <: U`. This is different from receiving the single type value
`TypeValueShape(Int | Str)`. In that case the constraints target the union type,
whose structure must be retained for the constraint implementation.

The proposed payload is a live type reference, based on `DeclaredType`, together
with the context needed to interpret that reference. `DeclaredType` already
retains a `TypeResolution` and its parameter bindings. References to parameters
must also retain their originating inference hosts. The wrapper must preserve
aliases, type arguments, and captures. A snapshot of positive value shapes
cannot replace the type reference, since it cannot accept subsequent constraints
in both directions.

For an inferred mutable array, call its element parameter `E`. This is a name for
the existing `Array` type-parameter symbol in that array's allocation context,
not a proposal for a new symbol per array. Matching that array against `Array[A]`
passes a type value referring to `E` into `A`. A subsequent bound on `A` is then
constrained through `E` in the appropriate direction. In particular, the lower
bound from an element insertion reaches `E` even if the array was initially empty.

An explicit type argument such as `Base` continues to determine the interface
of values described by it. A `Child` value supplied against that type creates a
`Child <: Base` constraint; it does not replace the type value `Base` with `Child`.

This replaces the earlier suggestion to connect the array's ordinary value
publishers in both directions. Type-value flow preserves both polarities;
ordinary bound propagation retains its direction.

## Where the current implementation loses the distinction

The relevant code is in
[`NewResolver.scala`](../hkmc2/shared/src/main/scala/hkmc2/semantics/NewResolver.scala),
[`TypeShape.scala`](../hkmc2/shared/src/main/scala/hkmc2/semantics/TypeShape.scala), and
[`NewResolverState.scala`](../hkmc2/shared/src/main/scala/hkmc2/semantics/NewResolverState.scala).

- `listenTypeValues` currently produces **ordinary value shapes described by a
  type**, despite its name. Both `Array[Int]`'s element interface and ordinary
  integer values can consequently arrive as `TermShape`s.
- `applyTypeArguments` calls that operation and publishes the resulting value
  shapes into the type-parameter host. The fact that a type was supplied is lost.
- The nominal-argument branch of `inferTypeArguments` also extracts value shapes
  from the actual argument's type parameters before constraining the expected
  parameters. Thus `Array[Int]` against `Array[A]` becomes a value-bound flow.
- The parameter branch of `inferTypeArguments` suppresses incoming constraints
  for explicit type arguments. That protects the declared result interface, but
  also discards the constraints that should reach the supplied type.
- `mutableArray` publishes initializer element shapes into `Array`'s parameter.
  These are ordinary value lower bounds and must stay distinguishable from type
  arguments. `TypeShape.Inferred` and `instanceBindings` need the same audit:
  their current uses include both inferred elements and explicit type interfaces.

Adding a wrapper only at the explicit type-application call site would therefore
be insufficient. Extracting nominal arguments and interpreting parameter uses
must preserve the distinction too.

## Implementation plan

1. **Define the wrapper and the flow operations.** Add `TypeValueShape` and explicit
   operations for passing a type value and propagating lower and upper bounds.
   Distinguish those operations from obtaining positive value shapes from a type. Keep wrapper transport distinct from runtime
   value consumption. Audit `Shape`/`ShapeLike` and context-mark operations: today
   their entry/exit results are restricted to `TermShape | NoShape`. Extend the
   transport deliberately so type values retain context without masquerading as
   array elements or callable runtime values. Rename or split `listenTypeValues`
   so callers state which operation they need.

2. **Implement constraint delivery through type values.** When a parameter receives
   a type value, connect its existing and future bounds to that type. When a bound
   arrives first, retain it so it is processed when the type value becomes known.
   Follow aliases, captures, parameter bindings, and structural/function types
   through one shared constraint implementation. Keep constraint direction
   explicit, including when function parameter positions reverse it. Concrete
   mismatches may remain quiet, but must reach this implementation.

3. **Preserve type values at generic argument boundaries.** Change
   `applyTypeArguments` and nominal argument matching in `inferTypeArguments` to
   transport wrappers instead of the wrapped type's output value shapes.
   `Array[Int]` against `Array[A]` must pass `Int` as a type value; an inferred
   `Array[E]` must pass a live reference to `E`. Ordinary argument, field, and
   callback-result values continue to create bounds. Preserve declared type
   expressions such as `Int | Str` inside their wrapper instead of flattening
   them into separate type-value deliveries.

4. **Replace constraint suppression with constraint routing.** Explicit type
   arguments must continue to determine the interface used for ordinary values.
   Incoming value constraints must reach those types instead of being skipped by
   `hasExplicitTypeArgument`. Audit other uses of that flag separately, including
   detection of omitted constructor type arguments in `listenArrayElements`;
   removing the constraint guard does not justify changing unrelated behavior.
   Replace the positive-shape snapshot in `instanceBindings` with the wrapper's
   lower- and upper-bound operations. Preserve the abstract activation used to
   check generic bodies independently of their callers.

5. **Apply the common operations to mutable-array interfaces.** Keep the existing
   `Array` parameter symbol and allocation/call contexts. Initializer elements,
   indexed assignments, `fill`, and `push`/`unshift` arguments create lower bounds.
   Element uses receive the corresponding positive shapes and impose constraints
   through their expected types. A generic helper taking `Array[A]` must propagate
   these constraints through the wrapped reference to the caller's element
   parameter. Reuse this machinery for nested arrays and declared member
   signatures; do not add a special reverse edge just for arrays.

6. **Preserve graph ownership and compiler boundaries.** Store bound listeners,
   wrapper caches, and processed-constraint sets in `NewResolverState`, using the
   existing consumer-local host mechanism. Include the kind of flow, referenced
   hosts, and contexts in deduplication keys. Install edges before replay so cycles
   terminate and subscription order does not change results. In particular, a
   value bound arriving before a type value must not permanently publish a more
   specific output interface that the supplied type does not expose. Resolve how
   positive shape observation distinguishes bound-only inference from supplied
   type values before wiring them into ordinary value listeners; do not rely on callback registration order.
   Check `InterfaceExposure`, shape-pattern matches, and erasure/lowering consumers so
   wrappers neither hide escaping functions nor become runtime shapes. Do not
   mutate shared symbols or change completed member targets.

7. **Add regressions, then remove the generic-array FIXME.** Test the semantic
   distinctions below, run `ctest` before focused worksheets, and finish with
   `hkmc2AllTests/test`. Review and commit all changed golden outputs. Update the
   implementation notes and migration worklist only for behavior actually covered
   by the completed implementation.

## Acceptance tests

- Supply `TypeValueShape(Int)` to `A`. Verify both that a lower bound `L <: A`
  reaches `L <: Int` and that an upper bound `A <: U` reaches `Int <: U`. Check
  delivery at the constraint layer, since loud concrete-mismatch diagnostics
  are not required.
- Match `Array[Int]` against `Array[A]`, then supply a string to an element
  parameter of type `A`. Verify that this creates `Str <: Int` while the positive
  interface supplied by the type value remains `Int`.
- Repeat with the lower bound installed before the type value, and with a type
  alias or captured parameter between them. Results must not depend on arrival
  order, including when an output listener was registered first.
- Supply two type values to the same activation and verify that both receive
  each bound. Separately supply `Int | Str` as one type value and verify that the
  constraint targets the union type rather than each alternative independently.
- Distinguish supplying the type argument `Int` from inferring a lower bound from
  an ordinary integer argument. Only the former supplies that type value.
- Make the `appendTyped` regression in `newres/MutableArrays.mls` pass: writing
  through `Array[A]` into an initially empty mutable array must make the inserted
  element available to reads of the original array. Also cover later writes,
  nested arrays, and several generic forwarding helpers.
- Keep `Array[Base]` reads limited to `Base`'s declared members after a `Child`
  insertion, for explicit constructor arguments and annotated parameters alike.
- Exercise both input and output uses in function types and generic callbacks,
  along with ordinary explicit and inferred generic function calls.
- Check distinct allocations, distinct calls to the same function, recursive
  propagation, later worksheet blocks, separate importers, and re-exports.
  Preserve the `PublisherTest` and `CompilerTest` ownership assertions.
- Keep generic-body checks, unknown-versus-dynamic behavior, exposed-closure
  checking, and completed-reference assertions intact.

## Scope

Precise array positions and lengths, a new policy for concrete type-mismatch
diagnostics, optional `splice` arguments, general storage reassignment, and
handler-result inference remain separate work. Rules for bounds or variance
beyond those needed by the existing interfaces require a separate design
decision; type-value flow must not be mislabeled as covariant lower-bound
propagation.
