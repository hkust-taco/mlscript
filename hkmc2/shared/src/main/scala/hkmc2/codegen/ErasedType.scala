package hkmc2
package codegen

import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import utils.*

import semantics.*
import semantics.Elaborator.{Ctx, State, ctx}
import semantics.Term.*

/** A primitive type of the block IR. */
enum PrimitiveType:
  case Int32, Int64, Float32, Float64

  /** The symbol for this primitive type. */
  def sym(using Ctx, State): TypeSymbol = this match
    case Int32 => ctx.builtins.Int32
    case Int64 => ctx.builtins.Int64
    case Float32 => ctx.builtins.Float32
    case Float64 => ctx.builtins.Float64

object ErasedType:
  /** A canonicalized reference type.
    *
    * Instances should be created using [[CanonicalErasedValueType.apply]] or [[ValueLike]] to ensure the correct
    * representation is used for a given type symbol.
    *
    * - `rsc` is true if this reference is a resource class.
    *
    * Implementation Note: This type should **not** be used to represent references of type aliases or the top type -
    * [[ValueLike]] and [[Unknown]] should be used instead.
    */
  case class AnyRef(rsc: Opt[Bool], tpeSym: TypeSymbol) extends ErasedValueType, CanonicalErasedValueType

  /** A value type that is not yet canonicalized.
    *
    * - `rsc` is true if this reference is a resource type.
    *
    * Implementation Notes:
    *
    * - This transient type is needed to represent value types before the `Prelude` is fully elaborated. The IR should
    *   always operate on the canonicalized type.
    * - This type implements identity equality, so that two instances with the same `getTpeSym` function are not
    *   considered equal - Use the canonicalized type for equality comparisons.
    */
  final class ValueLike(val rsc: Opt[Bool], getTpeSym: (Ctx, State) ?=> TypeSymbol) extends ErasedValueType:
    type Canonical = CanonicalErasedValueType
    def sym(using Ctx, State): TypeSymbol = getTpeSym
    override protected def computeCanonicalize(using Ctx, State): CanonicalErasedValueType =
      CanonicalErasedValueType(rsc, sym)
    // Ensures `toString` returns a stable string
    override def toString: Str = "ValueLike(?)"

  /** A primitive type. */
  case class Primitive(prim: PrimitiveType) extends ErasedValueType, CanonicalErasedValueType

  /** A union of erased types.
    *
    * Implementation Note: This transient type is needed to represent union types before the `Prelude` is fully
    * elaborated - See the implementation note of `ValueLike`. The IR should always operate on the canonicalized type.
    */
  case class Union(members: Ls[ErasedValueType]) extends ErasedValueType:
    type Canonical = CanonicalErasedValueType
    override protected def computeCanonicalize(using Ctx, State): CanonicalErasedValueType =
      members.map(_.canonicalize).reduceLeft((a, b) => lub(a, b))

  object Union:
    /** Creates a nonempty union, flattening nested unions and collapsing a singleton to its sole member.
      * The result is not canonicalized into the LUB of its members.
      */
    def mk(members: Iterable[ErasedValueType]): ErasedValueType =
      def flatten(et: ErasedValueType): Iterator[ErasedValueType] = et match
        case Union(ms) => ms.iterator.flatMap(flatten)
        case other => Iterator.single(other)
      // `ValueLike` types are identity-equal; canonicalization collapses any remaining equivalent members.
      val flattened = members.iterator.flatMap(flatten).distinct.toList
      require(flattened.nonEmpty, "an erased union must have at least one member")
      flattened match
        case single :: Nil => single
        case ms => Union(ms)

  /** The representation of a value required to satisfy every member. Resolve nominal ancestry at
    * canonicalization time, once the IR has class headers for the types appearing in the intersection.
    */
  final case class Intersection(members: Ls[ErasedValueType]) extends ErasedValueType:
    require(members.nonEmpty)
    type Canonical = CanonicalErasedValueType
    protected def computeCanonicalize(using Ctx, State): CanonicalErasedValueType =
      def flatten(tpe: ErasedValueType): Iterator[CanonicalErasedValueType] = tpe match
        case Intersection(parts) => parts.iterator.flatMap(flatten)
        case other => Iterator.single(other.canonicalize)
      // An erased source type can lose a constraint. In particular, Any and an unbounded type parameter
      // both erase to Unknown on their own. Neither rules out the Int32 values of T & Int32.
      // A known reference class, on the other hand, does rule out an unboxed primitive.
      val types = members.iterator.flatMap(flatten).filterNot(_ == Unknown).distinct.toList
      types.collectFirst { case error: Incompatible => error }.getOrElse:
        // With single inheritance an inhabited intersection of known nominal types has a most specific member.
        types.filter(tpe => types.forall(needsCast(tpe, _).contains(false))) match
          case bound :: Nil => bound
          case Nil =>
            if types.exists(a => types.exists(b => needsCast(a, b).isEmpty)) then Nothing
            else Unknown // No known bound, or incomplete class headers leave the subtype relation undecided.
          case equivalent =>
            // Casts ignore resource metadata. Preserve the common class when only this metadata differs.
            equivalent.collect { case AnyRef(_, sym) => sym }.distinct match
              case sym :: Nil => AnyRef(N, sym)
              case _ => Unknown // A cyclic hierarchy has no unique most specific class.

  /** The top type of reference types, i.e. any value on JS and `anyref` on Wasm.
    *
    * Reached by an absent annotation (`erasedType_!` folds `N` here), by an alias the IR cannot resolve, and
    * by the surface top `Anything`, which has no erased counterpart of its own.
    */
  case object Unknown extends ErasedValueType, CanonicalErasedValueType

  /** The bottom type: a value supplies no constraint on its destination's representation.
    * `undefined` has this type and can inhabit every representable slot. It does not imply that evaluation
    * diverges or has no effects; backends must evaluate the operand before materializing an unspecified value.
    */
  case object Nothing extends ErasedValueType, CanonicalErasedValueType

  /** Two types with no common upper bound.
    *
    * Unboxed primitives have no common upper bound with references or other primitives. `Nothing` lies below
    * every representable type, but a union mixing distinct representations still has nothing to erase to.
    *
    * Erasure rejects such a type where a declaration writes it. A type joined from other representations, such as
    * a loop's exits, is reported wherever a value has to be coerced into or out of it, by [[Result.coerceTo]].
    * Both members are carried so that each diagnostic can name them.
    *
    * `reported` records that a declaration of this type was already rejected, so coercions into or out of it do
    * not report it again. It does not take part in equality.
    */
  case class Incompatible(lhs: CanonicalErasedValueType, rhs: CanonicalErasedValueType)(val reported: Bool)
      extends ErasedValueType, CanonicalErasedValueType

  /** The builtin `Unit` reference type. */
  def Unit: ErasedValueType = ErasedType.ValueLike(rsc = S(false), summon[State].unitSymbol)

  /** The type of the results of the pattern protocol: an instance of the `MatchSuccess` or of the
    * `MatchFailure` class of the runtime, as its `MatchResult` type says. */
  def MatchResult: ErasedValueType = union(
    ErasedType.ValueLike(rsc = S(false), summon[State].matchSuccessClsSymbol),
    ErasedType.ValueLike(rsc = S(false), summon[State].matchFailureClsSymbol))

  /** The builtin `Bool` reference type. */
  def Bool: ErasedValueType = ErasedType.ValueLike(rsc = S(false), ctx.builtins.Bool)

  /** The builtin `Int` reference type. */
  def Int: ErasedValueType = ErasedType.ValueLike(rsc = S(false), ctx.builtins.Int)
  
  /** The builtin `Num` reference type. */
  def Num: ErasedValueType = ErasedType.ValueLike(rsc = S(false), ctx.builtins.Num)

  /** The builtin `Str` reference type. */
  def Str: ErasedValueType = ErasedType.ValueLike(rsc = S(false), ctx.builtins.Str)
  
  /** The builtin `Array` reference type. */
  def Array: ErasedValueType = ErasedType.ValueLike(rsc = S(false), ctx.builtins.Array)

  /** The builtin `Int31` reference type. */
  def Int31: ErasedValueType = ErasedType.ValueLike(rsc = S(false), ctx.builtins.Int31)

  /** The runtime representation of a literal. `null` is a reference value. The unspecified value
    * `undefined` can inhabit any destination representation, including an unboxed primitive.
    */
  def ofLiteral(lit: syntax.Literal): ErasedValueType = lit match
    case _: syntax.Tree.IntLit => Int
    case _: syntax.Tree.DecLit => Num
    case _: syntax.Tree.StrLit => Str
    case _: syntax.Tree.BoolLit => Bool
    case syntax.Tree.UnitLit(true) => Unknown
    case syntax.Tree.UnitLit(false) => Nothing

  /** The builtin `Function` reference type, used as the value type of a first-class function.
    *
    * - `rsc` is true if this reference is a resource function.
    */
  def Function(rsc: Opt[Bool]): ErasedValueType = ErasedType.ValueLike(rsc, ctx.builtins.Function)

  /** WORKAROUND (see [[semantics.BuiltinOperatorResults]]): the representation of an application of the builtin
    * operator named `op`, approximated from the representations of its operands with the same rules as resolution.
    * Comparing representations requires a context, so the choice is deferred until the type is canonicalized.
    * Only the JavaScript backend sees these applications: lowering for Wasm replaces them by intrinsic calls.
    */
  def builtinOperatorResult(op: Str, operands: Ls[Path]): Opt[ErasedValueType] =
    import semantics.BuiltinOperatorResults, BuiltinOperatorResults.{PrimitiveClass, Alternative}
    if !BuiltinOperatorResults.approximates(op, operands.length) then N
    else S(ErasedType.ValueLike(rsc = S(false), {
      val builtins = ctx.builtins
      def primitiveOf(operand: Path): Opt[PrimitiveClass] =
        val actual = operand.erasedType_!.canonicalize
        def within(cls: ClassSymbol) =
          needsCast(actual, ErasedType.ValueLike(rsc = S(false), cls).canonicalize).contains(false)
        if within(builtins.Int) then S(PrimitiveClass.Int)
        else if within(builtins.Num) then S(PrimitiveClass.Num)
        else if within(builtins.Str) then S(PrimitiveClass.Str)
        else if within(builtins.Bool) then S(PrimitiveClass.Bool)
        else if within(builtins.BigInt) then S(PrimitiveClass.BigInt)
        else N
      BuiltinOperatorResults(op, operands.map(primitiveOf)) match
        case S(Alternative.Of(primitive) :: Nil) => primitive match
          case PrimitiveClass.Int => builtins.Int
          case PrimitiveClass.Num => builtins.Num
          case PrimitiveClass.Str => builtins.Str
          case PrimitiveClass.Bool => builtins.Bool
          case PrimitiveClass.BigInt => builtins.BigInt
        // Applications that yield an operand (the comma and short-circuiting operators) do not reach the IR as
        // calls. Like applications without an approximation, they keep the top representation.
        case _ => builtins.Anything
    }))

  /** Determines the direct parent from published metadata, treating a missing header as unknown. */
  private def parentOf(sym: BaseTypeSymbol): ClassHeader.Parent =
    sym.irClassHeader.fold(ClassHeader.Parent.Unknown)(_.parent)

  /** A symbol's ancestors, nearest first, starting with the symbol itself and following its single parent chain.
    *
    * `complete` may be false if the walk ran out of information first: the parent chain is not available in the IR
    * (e.g. an unlinked import), it cycles back onto an already-visited symbol, or it reaches a type alias, which the
    * walk cannot step through.
    *
    * When `complete` is false, the *absence* of a symbol from `ancestors` proves nothing.
    *
    * Note that this does not include implicit supertypes (`Object` and `Anything`).
    */
  private case class AncestorChain(ancestors: Ls[TypeSymbol], complete: Bool):
    /** Whether `sym` is on this chain, or `N` when the chain ran out of information before deciding. */
    def hasAncestor(sym: TypeSymbol): Opt[Bool] =
      if ancestors.exists(_ is sym) then S(true)
      else if complete then S(false)
      else N

  /** Walks the parent chain of `sym`. See [[AncestorChain]]. */
  private def ancestorChain(sym: TypeSymbol)(using Ctx, State): AncestorChain =
    @tailrec
    def loop(cur: TypeSymbol, seen: Set[TypeSymbol], acc: Ls[TypeSymbol]): AncestorChain =
      if seen(cur) then AncestorChain(acc.reverse, complete = false)
      else cur match
        case base @ (_: ClassSymbol | _: ModuleOrObjectSymbol) => parentOf(base) match
          case ClassHeader.Parent.Known(parent) => loop(parent, seen + cur, cur :: acc)
          case ClassHeader.Parent.Root => AncestorChain((cur :: acc).reverse, complete = true)
          case ClassHeader.Parent.Unknown => AncestorChain((cur :: acc).reverse, complete = false)
        case _: TypeAliasSymbol => AncestorChain((cur :: acc).reverse, complete = false)
    loop(sym, Set.empty, Nil)

  /** The least upper bound of two reference symbols.
    *
    * Returns `Object` if the two symbols are unrelated but both sit under it, and `Anything` if they share no
    * common ancestor at all - which is the case whenever either side is `Num`, `Str`, `Bool` or a descendant of
    * one, since those are represented as host primitives and so sit outside `Object`.
    */
  private def lubSym(a: TypeSymbol, b: TypeSymbol)(using Ctx, State): TypeSymbol =
    // * `Object` is only a candidate when `a` is itself under it: appending it unconditionally would return
    // * `Object` for a pair like `Int` and some class, which is not an upper bound of `Int` at all.
    // TODO(Derppening): Skip appending `Object` and/or `Anything` if the symbols explicitly extend either of them
    val objectCandidate =
      if isSubtypeOf(a, ctx.builtins.Object).contains(true) then ctx.builtins.Object :: Nil else Nil
    val candidates = ancestorChain(a).ancestors ::: objectCandidate ::: ctx.builtins.Anything :: Nil
    candidates.find(anc => isSubtypeOf(b, anc).contains(true)).getOrElse(ctx.builtins.Anything)

  /** Creates a union of two erased types.
    *
    * Unlike the `Union` constructor, this method also flattens nested unions, and collapses a singleton to its sole
    * member.
    *
    * Note that the resulting union type is **not** canonicalized into the LUB of its members.
    */
  def union(lhs: ErasedValueType, rhs: ErasedValueType): ErasedValueType =
    Union.mk(lhs :: rhs :: Nil)

  /** The least upper bound of two canonical erased types. */
  def lub(lhs: CanonicalErasedValueType, rhs: CanonicalErasedValueType)(using Ctx, State): CanonicalErasedValueType =
    (lhs, rhs) match
      case _ if lhs == rhs => lhs
      // * An incompatibility absorbs everything, keeping the pair that first had no upper bound: that is the
      // * conflict worth reporting, rather than whichever type happened to be folded in last.
      case (i: Incompatible, _) => i
      case (_, i: Incompatible) => i
      case (Nothing, tpe) => tpe
      case (tpe, Nothing) => tpe
      // * A primitive shares no supertype with any other non-bottom type - the `Unknown` type
      // * included.
      case (_: Primitive, _) | (_, _: Primitive) => Incompatible(lhs, rhs)(reported = false)
      // * The top type absorbs every reference type.
      case (Unknown, _) | (_, Unknown) => Unknown
      // * Two reference types: their nearest common ancestor, at worst `Object`.
      case (AnyRef(_, l), AnyRef(_, r)) => CanonicalErasedValueType(rsc = S(false), lubSym(l, r))

  /** Erases a type-annotated term to an [[ErasedValueType]].
    *
    * Used by the legacy resolver after resolution. Canonicalization is separate and may inspect the
    * nominal hierarchy published by Erasure.
    */
  def eraseSign(sign: Term)(using Erasure): Opt[ErasedValueType] = sign match
    case Capture(base, _) => eraseSign(base)
    case CompType(lhs, rhs, true) =>
      // * A union is kept as a transient `Union` surface form; `canonicalize` collapses it to the members' LUB.
      for
        l <- eraseSign(lhs)
        r <- eraseSign(rhs)
      yield ErasedType.union(l, r)
    case CompType(lhs, rhs, false) =>
      S(Intersection(eraseSign(lhs).getOrElse(Unknown) :: eraseSign(rhs).getOrElse(Unknown) :: Nil))
    case DynTy() => S(ErasedType.Unknown)
    case UnitVal() => S(ErasedType.Unit)
    // * A written arrow denotes a function value, and every function value is a `Function`.
    case FunTy(_, _, _) => S(ErasedType.Function(rsc = S(false)))
    // * Quantification erases away: what a `forall` denotes is what its body denotes.
    case Forall(_, _, body) => eraseSign(body)
    case _ =>
      sign.symbol.flatMap(_.asTpe).map(sym => ErasedType.ValueLike(rsc = S(false), sym))

  /** Whether `actual` is a subtype of `expected`, walking the class hierarchy.
    *
    * Both symbols are expected to come from an already-canonicalized type, i.e. to have had their type aliases
    * resolved away by [[CanonicalErasedValueType.apply]] - which is also where an unresolvable alias becomes the top
    * type. A `TypeAliasSymbol` reaching here instead truncates the ancestor walk, which returns `N`.
    *
    * Returns `S(true)`/`S(false)` when the relationship can be decided, or `N` when deciding would require
    * information not available in the IR (e.g. an unlinked parent chain on an imported class).
    */
  def isSubtypeOf(actual: TypeSymbol, expected: TypeSymbol)(using Ctx, State): Opt[Bool] =
    if actual is expected then S(true)
    else if expected is ctx.builtins.Anything then S(true)
    else if actual is ctx.builtins.Anything then S(false)
    else if expected is ctx.builtins.Object then
      // * `Object` is the base of the types whose identity can be tested at runtime. That excludes both the
      // * unboxed primitives and the classes represented as host primitives (`Num`/`Str`/`Bool` and their
      // * descendants, notably `Int`); every other reference type is implicitly `<: Object`.
      // * The second test walks the parent chain instead of testing the roots directly, so that the exclusion
      // * stays descendant-closed: a user class extending `Int` must be excluded along with `Int` itself.
      // * Unlike the general case below, the chain's `complete` flag is deliberately ignored: a chain truncated
      // * before reaching a root does not make this undecidable, which is the answer this branch has always given.
      // TODO(Derppening): Remove this fallback once `extends Object` is explicit
      if PrimitiveType.values.exists(_.sym === actual)
        || ancestorChain(actual).ancestors.exists(ctx.builtins.primitivelyRepresentedRoots)
      then S(false)
      else S(true)
    // * Otherwise, consult the ancestor chain and see if the expected symbol is on it.
    else ancestorChain(actual).hasAncestor(expected)

  /** Determines whether a cast is needed to make a value of erased type `actual` fit an `expected` slot.
    *
    * Returns `S(true)` if a cast is needed, `S(false)` if no cast is needed, or `N` if the two types are unrelated.
    */
  def needsCast(actual: CanonicalErasedValueType, expected: CanonicalErasedValueType)(using Ctx, State): Opt[Bool] =
    (actual, expected) match
      // * A type with no upper bound has no representation of its own, so nothing can be coerced into or out of
      // * it - not even widened into the top type.
      case (_: Incompatible, _) | (_, _: Incompatible) => N
      case (Nothing, _) => S(false)
      // * Bottom lies below every representable type, so narrowing to it is a downcast like `Unknown -> T`.
      // * No ordinary value has type `Nothing`, so the cast is only reached by values that break their
      // * annotation; it usually guards code that never runs, such as the result of a call to an unannotated
      // * function that always throws. Backends do not test it: the cast has type `Nothing`, so its consumers
      // * materialize an unspecified value of their own representation.
      case (_, Nothing) => S(true)
      case (Primitive(a), Primitive(b)) => if a == b then S(false) else N
      // * A primitive is compatible only with the same primitive in either direction.
      case (Primitive(_), _) | (_, Primitive(_)) => N
      // * `T -> Unknown` needs no cast; `Unknown -> T` needs a checked downcast.
      case (_, Unknown) => S(false)
      case (Unknown, _) => S(true)
      case (AnyRef(_, a), AnyRef(_, e)) =>
        if a is e then S(false)
        else (isSubtypeOf(a, e), isSubtypeOf(e, a)) match
          // * The value is already a subtype of the slot -> no cast needed.
          case (S(true), _) => S(false)
          // * The slot is a subtype of the value -> a narrowing (checked) cast.
          case (_, S(true)) => S(true)
          // * Provably unrelated along the `ext` chain -> narrowing is a compile error.
          case (S(false), S(false)) => N
          // * Undecidable (unlinked import / cyclic chain): treat the value's type as the top type `Unknown`
          // * for this decision and emit a conservative checked cast.
          case _ => S(true)

/** An erased type or signature of the Block IR, which has a canonical form that is computed once and memoized. */
sealed trait Canonicalizable:
  type Canonical <: Canonicalizable

  /** Memoized canonical form with the `State` that it was computed under, written by [[canonicalize]] and read
    * only through it.
    *
    * The canonical form is only meaningful within that `State`: it refers to symbols of the runtime that the
    * state loaded, such as the `Unit` object. A type of the Prelude is shared by the states of all the
    * compilation units, including the ones that load a rebuilt runtime, whose symbols are other ones. A form
    * memoized for one of them would name a `Unit` that is unrelated to the `Unit` of the others.
    */
  private var _canonicalized: Opt[(State, Canonical)] = N

  /** The canonical form in the given state, computed by [[computeCanonicalize]] on first use in that state and
    * memoized until another state asks for it.
    *
    * Callers are encouraged to always canonicalize types before using them.
    */
  final def canonicalize(using Ctx)(using state: State): Canonical = _canonicalized match
    case S((owner, n)) if owner is state => n
    case _ =>
      val n = computeCanonicalize
      _canonicalized = S((state, n))
      n

  /** Computes the canonical form, by resolving type aliases to their target type, reclassifying unboxed primitive
    * symbols to [[ErasedType.Primitive]], and collapsing unions to their least upper bound (LUB).
    *
    * Each overriding implementation performs the ones that apply to it; alias resolution and primitive
    * reclassification both happen in [[CanonicalErasedValueType.apply]], and a signature canonicalizes its parameter
    * and return types.
    *
    * Intersections canonicalize their members together to find the representation shared by every component.
    *
    * Call [[canonicalize]] rather than this, so that the result is memoized.
    */
  protected def computeCanonicalize(using Ctx, State): Canonical

/** A generics-erased type of a value in the Block IR. */
sealed abstract class ErasedValueType extends Canonicalizable:
  type Canonical <: CanonicalErasedValueType

  /** Renders this type for a user-facing diagnostic.
    *
    * Outputs the canonicalized name of the type symbol, qualified by its owner chain, or the node's own name when
    * no symbol denotes it.
    *
    * Implementation Note: `Printer` is deliberately not used here: it needs a `Scope` and a `SymbolPrinter`, which the
    * backends reporting these diagnostics do not have.
    */
  final def describe(using Ctx, State): Str =
    def ownerOf(s: Symbol): Opt[InnerSymbol] = s match
      case s: (ClassSymbol | ModuleOrObjectSymbol) => s.owner
      case _ => N
    def qualify(s: Symbol, acc: Ls[Str]): Ls[Str] =
      ownerOf(s).fold(s.nme :: acc)(o => qualify(o, s.nme :: acc))
    canonicalize match
      case ErasedType.Unknown => "Unknown"
      case ErasedType.Nothing => "Nothing"
      case ErasedType.Incompatible(l, r) => s"‹incompatible(${l.describe}, ${r.describe})›"
      case ErasedType.Primitive(prim) => qualify(prim.sym, Nil).mkString(".")
      case ErasedType.AnyRef(_, sym) =>
        val name = qualify(sym, Nil).mkString(".")
        if sym.asMod.isDefined then s"module $name" else name


/** The result behavior of a definition, before any async or generator wrapping.
  * `bodyType` types explicit and implicit returns; `callType` types a fully applied call
  * (or a getter read). In particular, Async(Int) and Direct(Promise) have the same call
  * representation but different body representations. Generator's payload is its final
  * return; yielded values and values passed to `next` are not tracked here.
  */
enum ErasedResult[+T <: ErasedValueType](val bodyType: Opt[T]):
  case Direct(tpe: Opt[T]) extends ErasedResult(tpe)
  case Async(tpe: Opt[T]) extends ErasedResult(tpe)
  case Generator(tpe: Opt[T]) extends ErasedResult(tpe)

  def callType: Opt[ErasedValueType] = this match
    case Direct(tpe) => tpe
    case Async(_) => S(ErasedType.ValueLike(S(false), ctx.builtins.Promise))
    case Generator(_) => S(ErasedType.ValueLike(S(false), ctx.builtins.Iterator))

  def map[U <: ErasedValueType](f: T => U): ErasedResult[U] = this match
    case Direct(tpe) => Direct(tpe.map(f))
    case Async(tpe) => Async(tpe.map(f))
    case Generator(tpe) => Generator(tpe.map(f))
end ErasedResult

object ErasedResult:
  def fromAnnotations(bodyType: Opt[ErasedValueType], annotations: Ls[semantics.Annot]): ErasedResult[ErasedValueType] =
    if annotations.exists(_.isInstanceOf[semantics.Annot.Async]) then Async(bodyType)
    else if annotations.exists(_.isInstanceOf[semantics.Annot.Generator]) then Generator(bodyType)
    else Direct(bodyType)


/** Immutable result information shared by parameterized definitions and getters.
  * TermSymbol publishes the complete signature once, before lowering or importing it.
  * Copying a source body must rename its payload types along with the parameter types.
  *
  * Every IR [[Call]] also carries one of these, describing the callee as seen by that call site.
  */
sealed abstract class ErasedCallableSignature extends Canonicalizable:
  type Canonical <: ErasedCallableSignature
  val result: ErasedResult[ErasedValueType]
  def ret: Opt[ErasedValueType] = result.callType

  /** The number of argument lists that a call can apply at most: none for a getter. */
  def paramListCount: Int = this match
    case sig: ErasedFuncSignature => sig.paramLists.length
    case _: ErasedGetterSignature => 0

  def mapTypes(f: ErasedValueType => ErasedValueType): ErasedCallableSignature

end ErasedCallableSignature


/** The erased types of one physical parameter list: its fixed parameters, followed by its rest parameter if it has
  * one. As with fixed parameters, the type of a rest parameter may be unknown, so `rest` is `N` when the list has no
  * rest parameter and `S(N)` when it has one of unknown type.
  */
final case class ErasedParamList[+T <: ErasedValueType](params: Ls[Opt[T]], rest: Opt[Opt[T]]):
  def map[U <: ErasedValueType](f: T => U): ErasedParamList[U] =
    ErasedParamList(params.map(_.map(f)), rest.map(_.map(f)))

object ErasedParamList:
  /** The physical layout of a lowered parameter list, typed by its parameter symbols. */
  def of(ps: LoweredParamList): ErasedParamList[ErasedValueType] =
    ErasedParamList(ps.params.map(_.sym.erasedType), ps.restParam.map(_.sym.erasedType))


object ErasedFuncSignature:
  /** The signature of a definition, whose parameter and body-result types may be unknown. */
  case class Signature(override val paramLists: Ls[ErasedParamList[ErasedValueType]],
      override val result: ErasedResult[ErasedValueType]) extends ErasedFuncSignature:
    assertHasParamLists(paramLists)
    type Canonical = CanonicalSignature
    override protected def computeCanonicalize(using Ctx, State): CanonicalSignature =
      CanonicalSignature(paramLists.map(_.map(_.canonicalize)), result.map(_.canonicalize))
  /** An analogue to `Signature` with canonicalized parameter and result representations. */
  case class CanonicalSignature(override val paramLists: Ls[ErasedParamList[CanonicalErasedValueType]],
      override val result: ErasedResult[CanonicalErasedValueType])(using Ctx, State) extends ErasedFuncSignature:
    assertHasParamLists(paramLists)
    override val ret: Opt[CanonicalErasedValueType] = result.callType.map(_.canonicalize)
    type Canonical = this.type
    override protected def computeCanonicalize(using Ctx, State): this.type = this

  /** Enforces the invariant that `paramLists` must be non-empty.
    *
    * See the documentation of [[ErasedFuncSignature]] for the rationale.
    */
  def assertHasParamLists(paramLists: Ls[?]): Unit =
    assert(paramLists.nonEmpty, "a signature must describe at least one parameter list")

  /** The signature of a call whose callee is not known: `listCount` argument lists, each passed to a function value
    * that accepts any number of arguments of any type, as in `(...Array) => (...Array) => ?` for two lists.
    *
    * Lowering applies a single argument list to each callee it knows nothing about, so a call starts with one list;
    * passes that merge such a call with the call of its result accumulate the lists. `super` calls also take this
    * form, because the `super` builtin has no fixed signature: its parameters are those of the parent constructor.
    *
    * Each use builds its own signature: a signature memoizes its canonical form, which is only meaningful in the
    * state that computed it.
    */
  def dynamic(listCount: Int): Signature =
    Signature(List.fill(listCount)(ErasedParamList(Nil, S(S(ErasedType.Array)))), ErasedResult.Direct(N))


/** The erased signature of a definition with parameter lists.
  *
  * A signature is not an [[ErasedValueType]], as it types no value: a reference to a definition evaluates to a
  * first-class function, whose value type is [[ErasedType.Function]].
  *
  * `paramLists` mirrors the definition's parameter *lists*, so that calls to curried functions can be typed by the
  * number of argument lists they apply. A partial application returns Function; only the last application wraps
  * an async or generator result.
  *
  * `paramLists` is nonempty. A definition with no written parameter lists is either a getter, described by
  * [[ErasedGetterSignature]], or takes an implicit empty parameter list, which this signature includes.
  */
sealed abstract class ErasedFuncSignature extends ErasedCallableSignature:
  type Canonical <: ErasedFuncSignature.CanonicalSignature
  val paramLists: Ls[ErasedParamList[ErasedValueType]]
  def mapTypes(f: ErasedValueType => ErasedValueType): ErasedFuncSignature =
    ErasedFuncSignature.Signature(paramLists.map(_.map(f)), result.map(f))
  /** The signature of applying the first parameter list alone, which returns a function when other lists
    * follow. Two functions with this signature in common accept the same call of one argument list, even when
    * their later lists differ.
    */
  def firstApplication: ErasedFuncSignature = paramLists match
    case first :: _ :: _ =>
      ErasedFuncSignature.Signature(first :: Nil, ErasedResult.Direct(S(ErasedType.Function(S(false)))))
    case _ => this
  /** The signature of the function that the application of the first `count` parameter lists returns, or `N`
    * when no parameter list remains.
    */
  def afterLists(count: Int): Opt[ErasedFuncSignature] =
    if count == 0 then S(this)
    else paramLists.drop(count) match
      case Nil => N
      case remaining => S(ErasedFuncSignature.Signature(remaining, result))


object ErasedGetterSignature:
  case class Signature(override val result: ErasedResult[ErasedValueType]) extends ErasedGetterSignature:
    type Canonical = CanonicalSignature
    override protected def computeCanonicalize(using Ctx, State): CanonicalSignature =
      CanonicalSignature(result.map(_.canonicalize))
  case class CanonicalSignature(override val result: ErasedResult[CanonicalErasedValueType])
      (using Ctx, State) extends ErasedGetterSignature:
    override val ret: Opt[CanonicalErasedValueType] = result.callType.map(_.canonicalize)
    type Canonical = this.type
    override protected def computeCanonicalize(using Ctx, State): this.type = this

  /** The signature of reading a property that resolution did not identify: it may be a plain field or a getter,
    * and its value is unknown.
    */
  def dynamic: Signature = Signature(ErasedResult.Direct(N))

/** A getter evaluates to its call result, without allocating a first-class function.
  * It still needs the body's result descriptor for async payload coercions.
  */
sealed abstract class ErasedGetterSignature extends ErasedCallableSignature:
  type Canonical <: ErasedGetterSignature.CanonicalSignature
  def mapTypes(f: ErasedValueType => ErasedValueType): ErasedGetterSignature =
    ErasedGetterSignature.Signature(result.map(f))


/** The canonical form of an [[ErasedValueType]]. */
sealed trait CanonicalErasedValueType extends ErasedValueType:
  type Canonical = this.type
  override protected def computeCanonicalize(using Ctx, State): this.type = this

object CanonicalErasedValueType:
  /** Creates an instance with the given type symbol, canonicalizing it if needed.
    *
    * - `rsc` is true if this is a resource type.
    */
  def apply(rsc: Opt[Bool], tpeSym: TypeSymbol)(using Ctx, State): CanonicalErasedValueType =
    // Preserve unions and intersections through alias chains until canonicalization. Type arguments
    // erase away. An abstract or cyclic alias supplies no known representation.
    def resolve(sym: TypeSymbol, seen: Set[TypeAliasSymbol]): Opt[ErasedValueType] = sym match
      case alias: TypeAliasSymbol =>
        if seen(alias) then N else alias.defn.flatMap(_.rhs).flatMap(underlying(_, seen + alias))
      case base => PrimitiveType.values.find(_.sym === base) match
        case S(primitive) => S(ErasedType.Primitive(primitive))
        case N => S(ErasedType.AnyRef(rsc, base))
    def underlying(tpe: Term, seen: Set[TypeAliasSymbol]): Opt[ErasedValueType] = tpe match
      case Term.CompType(lhs, rhs, true) =>
        for
          left <- underlying(lhs, seen)
          right <- underlying(rhs, seen)
        yield ErasedType.union(left, right)
      case Term.CompType(lhs, rhs, false) =>
        S(ErasedType.Intersection(underlying(lhs, seen).getOrElse(ErasedType.Unknown) ::
          underlying(rhs, seen).getOrElse(ErasedType.Unknown) :: Nil))
      case _ => tpe.symbol.flatMap(_.asTpe).flatMap(resolve(_, seen))
    resolve(tpeSym, Set.empty).fold(ErasedType.Unknown)(_.canonicalize)

end CanonicalErasedValueType


/** Erased types of source declarations are initialized by Erasure after resolution finishes.
  * `null` means no representation has been assigned; `N` is an initialized, unknown representation.
  * The checked getter also protects derived values from caching an early `N`.
  * IR-generated symbols may initialize the same slot directly at construction.
  */
trait HasDelayedErasedType[T <: ErasedValueType]:
  private var assignedErasedType: Opt[T] = null
  final def isErasureReady: Bool = assignedErasedType != null
  final def erasedType: Opt[T] =
    assert(isErasureReady, "Erased type read before erasure")
    assignedErasedType
  final def erasedType_=(value: Opt[T]): Unit =
    assert(!isErasureReady, "Erased type initialized more than once")
    assert(value != null, "An initialized erased type cannot be null")
    assignedErasedType = value


/** The calling conventions of the function values that a source application can call, as far as resolution
  * of its block knows them. Lowering reads them when the callee publishes no signature of its own: it is then
  * a function value, such as a parameter, a field, a variable, or the result of another call.
  */
enum ErasedCallee:
  /** A value whose applications follow `signature`: a value of a declared function type, or a function
    * definition, including the constructor function of a class, or a lambda. `signature` has the parameter lists that the value expects, starting with the one
    * that the application supplies. It has several lists for a curried definition, of which the application
    * then supplies the first.
    */
  case Known(signature: ErasedFuncSignature)
  /** A value of which resolution knows no calling convention, such as a dynamic value or a `Function`. It also
    * describes the callee of an application that resolution did not reach.
    */
  case Unknown
  /** A value that satisfies each of `components`, as a value of an intersection type does. */
  case All(components: Ls[ErasedCallee])
  /** A value that is one of `alternatives`. */
  case OneOf(alternatives: Ls[ErasedCallee])

  /** The signatures that every possible callee follows, one for each canonical form. A value follows the
    * `view` of its known signature, a value that satisfies several components follows the signatures of them
    * all, and alternatives only share the signatures that each of them follows.
    *
    * `view` selects what the callees must agree on: their whole signatures, or the application of their first
    * parameter list (see `ErasedFuncSignature.firstApplication`).
    */
  def sharedSignatures(view: ErasedFuncSignature => ErasedFuncSignature)(using Ctx, State): Ls[ErasedFuncSignature] =
    this match
      case Known(signature) => view(signature) :: Nil
      case Unknown => Nil
      case All(components) =>
        components.iterator.flatMap(_.sharedSignatures(view)).distinctBy(_.canonicalize).toList
      case OneOf(Nil) => Nil
      case OneOf(first :: others) => others.foldLeft(first.sharedSignatures(view)): (shared, alternative) =>
        val followed = alternative.sharedSignatures(view).map(_.canonicalize)
        shared.filter(signature => followed.contains(signature.canonicalize))

  /** The signature of a call that applies `listCount` argument lists to this callee, when its possible values
    * agree on one: the signature that they all have, or, for a call of one list, that of the application of
    * their first parameter list.
    */
  def callSignature(listCount: Int)(using Ctx, State): Opt[ErasedFuncSignature] =
    def unique(view: ErasedFuncSignature => ErasedFuncSignature): Opt[ErasedFuncSignature] =
      sharedSignatures(view) match
        case signature :: Nil => S(signature)
        case _ => N
    unique(identity).filter(_.paramListCount >= listCount).orElse:
      if listCount == 1 then unique(_.firstApplication) else N

  /** The signatures of all the possible callees that have a known one. */
  def knownSignatures: Iterator[ErasedFuncSignature] = this match
    case Known(signature) => Iterator.single(signature)
    case Unknown => Iterator.empty
    case All(components) => components.iterator.flatMap(_.knownSignatures)
    case OneOf(alternatives) => alternatives.iterator.flatMap(_.knownSignatures)

  def mapTypes(f: ErasedValueType => ErasedValueType): ErasedCallee = this match
    case Known(signature) => Known(signature.mapTypes(f))
    case Unknown => Unknown
    case All(components) => All(components.map(_.mapTypes(f)))
    case OneOf(alternatives) => OneOf(alternatives.map(_.mapTypes(f)))


/** Holds the possible callees of a source application. Erasure of the program that contains the application
  * assigns them once, and cloning the application copies them. An application that erasure never visits, such
  * as one that the desugaring of pattern matching synthesizes, keeps an unknown callee.
  */
final class ErasedCalleeSlot:
  private var assigned: Opt[ErasedCallee] = N
  def isErasureReady: Bool = assigned.isDefined
  def callee: ErasedCallee = assigned.getOrElse(ErasedCallee.Unknown)
  def callee_=(value: ErasedCallee): Unit =
    assert(!isErasureReady, "The callees of an application are erased once")
    assigned = S(value)
