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
  case class AnyRef(rsc: Opt[Bool], tpeSym: TypeSymbol) extends ErasedValueType, CanonicalErasedValueType:
    override def sym(using Ctx, State): TypeSymbol = tpeSym

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
    override type Canonical = CanonicalErasedValueType
    override def sym(using Ctx, State): TypeSymbol = getTpeSym
    override protected def computeCanonicalize(using Ctx, State): CanonicalErasedValueType =
      CanonicalErasedValueType(rsc, sym)
    // Ensures `toString` returns a stable string
    override def toString: Str = "ValueLike(?)"

  /** A primitive type. */
  case class Primitive(prim: PrimitiveType) extends ErasedValueType, CanonicalErasedValueType:
    override def sym(using Ctx, State): TypeSymbol = prim.sym

  /** A union of erased types.
    *
    * Implementation Note: This transient type is needed to represent union types before the `Prelude` is fully
    * elaborated - See the implementation note of `ValueLike`. The IR should always operate on the canonicalized type.
    */
  case class Union(members: Ls[ErasedValueType]) extends ErasedValueType:
    override type Canonical = CanonicalErasedValueType
    override def sym(using Ctx, State): NoSymbol =
      // * Only canonicalized unions have a symbol, so this is always `NoSymbol`.
      NoSymbol
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

  /** The top type of reference types, i.e. any value on JS and `anyref` on Wasm.
    *
    * Reached by an absent annotation (`erasedType_!` folds `N` here), by an alias the IR cannot resolve, and
    * by the surface top `Anything`, which has no erased counterpart of its own.
    */
  case object Unknown extends ErasedValueType, CanonicalErasedValueType:
    // * No symbol denotes this type: `Anything` is the surface top, which is a different thing.
    override def sym(using Ctx, State): NoSymbol = NoSymbol

  /** Two types with no common upper bound.
    *
    * The erased types form a forest rather than a lattice: an unboxed primitive is a root of its own, so a union
    * mixing one with a distinct type has nothing to erase to.
    *
    * Writing such a type is not itself an error - the error is raised wherever a value has to be coerced into or
    * out of it, by [[Result.coerceTo]]. Both members are carried so that the diagnostic can name them at that use
    * site.
    */
  case class Incompatible(lhs: CanonicalErasedValueType, rhs: CanonicalErasedValueType)
      extends ErasedValueType, CanonicalErasedValueType:
    override def sym(using Ctx, State): NoSymbol = NoSymbol

  /** The builtin `Unit` reference type. */
  def Unit: ErasedValueType = ErasedType.ValueLike(rsc = S(false), summon[State].unitSymbol)

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

  /** The builtin `Function` reference type, used as the value type of a first-class function.
    *
    * - `rsc` is true if this reference is a resource function.
    */
  def Function(rsc: Opt[Bool]): ErasedValueType = ErasedType.ValueLike(rsc, ctx.builtins.Function)

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
      // * A primitive is a root of its own: it shares no supertype with any distinct type - the `Unknown` type
      // * included.
      case (_: Primitive, _) | (_, _: Primitive) => Incompatible(lhs, rhs)
      // * The top type absorbs every reference type.
      case (Unknown, _) | (_, Unknown) => Unknown
      // * Two reference types: their nearest common ancestor, at worst `Object`.
      case _ => (lhs.sym, rhs.sym) match
        // * `Unknown` and `Incompatible` are the only symbol-less canonical types, and both are absorbed above.
        case (NoSymbol, _) | (_, NoSymbol) =>
          lastWords(s"no upper bound is defined for '$lhs' and '$rhs'")
        case (l: TypeSymbol, r: TypeSymbol) => CanonicalErasedValueType(rsc = S(false), lubSym(l, r))

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
    // * An intersection is never decomposed: narrowing to one member would call for a GLB, which this lattice
    // * cannot express.
    case CompType(_, _, false) => S(ErasedType.Unknown)
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
      case (Primitive(a), Primitive(b)) => if a == b then S(false) else N
      // * A primitive is compatible only with the same primitive in either direction.
      case (Primitive(_), _) | (_, Primitive(_)) => N
      // * `T -> Unknown` needs no cast; `Unknown -> T` needs a checked downcast.
      case (_, Unknown) => S(false)
      case (Unknown, _) => S(true)
      case (da, de) => (da.sym, de.sym) match
        // * `Unknown` and `Incompatible` are the only symbol-less canonical types, and both are decided above.
        case (NoSymbol, _) | (_, NoSymbol) =>
          lastWords(s"no cast is defined from '$da' to '$de'")
        case (a: TypeSymbol, e: TypeSymbol) =>
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

  /** Memoized canonical form, written once by [[canonicalize]] and read only through it.
    *
    * Note that the canonical form is only meaningful within the `State` it was computed under.
    */
  private var _canonicalized: Opt[Canonical] = N

  /** The canonical form, computed by [[computeCanonicalize]] on first use and memoized thereafter.
    *
    * Callers are encouraged to always canonicalize types before using them.
    */
  final def canonicalize(using Ctx, State): Canonical = _canonicalized match
    case S(n) => n
    case N =>
      val n = computeCanonicalize
      _canonicalized = S(n)
      n

  /** Computes the canonical form, by resolving type aliases to their target type, reclassifying unboxed primitive
    * symbols to [[ErasedType.Primitive]], and collapsing unions to their least upper bound (LUB).
    *
    * Each overriding implementation performs the ones that apply to it; alias resolution and primitive
    * reclassification both happen in [[CanonicalErasedValueType.apply]], and a signature canonicalizes its parameter
    * and return types.
    *
    * Intersections are never decomposed and are erased to [[ErasedType.Unknown]].
    *
    * Call [[canonicalize]] rather than this, so that the result is memoized.
    */
  protected def computeCanonicalize(using Ctx, State): Canonical

/** A generics-erased type of a value in the Block IR. */
sealed abstract class ErasedValueType extends Canonicalizable:
  type Canonical <: CanonicalErasedValueType

  /** The symbol denoting this erased type, or `NoSymbol` for [[ErasedType.Union]], [[ErasedType.Unknown]] and
    * [[ErasedType.Incompatible]].
    */
  def sym(using Ctx, State): TypeSymbol | NoSymbol

  /** Renders this type for a user-facing diagnostic.
    *
    * Outputs the canonicalized name of the type symbol, qualified by its owner chain, or the node's own name when
    * no symbol denotes it.
    *
    * Implementation Note: `Printer` is deliberately not used here: it needs a `Scope` and a `SymbolPrinter`, which the
    * backends reporting these diagnostics do not have.
    */
  final def describe(using Ctx, State): Str =
    def ownerOf(s: Symbol): Opt[InnerSymbol] = s.asClsOrMod.flatMap: s =>
      s.irClsLikeDefn.map(_.owner).orElse(s.defn.map(_.owner)).flatten
    def qualify(s: Symbol, acc: Ls[Str]): Ls[Str] = s match
      case _: TopLevelSymbol => acc
      case _ => ownerOf(s).fold(s.nme :: acc)(o => qualify(o, s.nme :: acc))
    canonicalize match
      case ErasedType.Unknown => "Unknown"
      case ErasedType.Incompatible(l, r) => s"‹incompatible(${l.describe}, ${r.describe})›"
      case cet => cet.sym match
        case NoSymbol => lastWords(s"no name is defined for '$cet'")
        case tpeSym: TypeSymbol =>
          val name = qualify(tpeSym, Nil).mkString(".")
          if tpeSym.asMod.isDefined then s"module $name" else name

object ErasedFuncSignature:
  /** The signature of a definition, whose parameter and return types may be unknown. */
  case class Signature(override val paramLists: Ls[Ls[Opt[ErasedValueType]]], override val ret: Opt[ErasedValueType]) extends ErasedFuncSignature:
    assertHasParamLists(paramLists)
    override type Canonical = CanonicalSignature
    override protected def computeCanonicalize(using Ctx, State): CanonicalSignature =
      CanonicalSignature(paramLists.map(_.map(_.map(_.canonicalize))), ret.map(_.canonicalize))

  /** An analogue to `Signature` with canonicalized parameter and return types. */
  case class CanonicalSignature(override val paramLists: Ls[Ls[Opt[CanonicalErasedValueType]]], override val ret: Opt[CanonicalErasedValueType]) extends ErasedFuncSignature:
    assertHasParamLists(paramLists)
    override type Canonical = this.type
    override protected def computeCanonicalize(using Ctx, State): this.type = this

  /** Enforces the invariant that `paramLists` must be non-empty.
    *
    * See the documentation of [[ErasedFuncSignature]] for the rationale.
    */
  def assertHasParamLists(paramLists: Ls[Ls[?]]): Unit =
    assert(paramLists.nonEmpty, "a signature must describe at least one parameter list")

/** The erased signature of a definition.
  *
  * A signature is not an [[ErasedValueType]], as it types no value: a reference to a definition evaluates to a
  * first-class function, whose value type is [[ErasedType.Function]].
  *
  * `paramLists` mirrors the definition's parameter *lists*, so that calls to curried functions can be typed by the
  * number of argument lists they apply.
  *
  * Note that `paramLists` should never be empty: a definition declaring no parameter list at all is either compiled
  * to a getter and erased to its result instead, or given an implicitly-added empty parameter list which the erased
  * signature mirrors.
  */
sealed abstract class ErasedFuncSignature extends Canonicalizable:
  type Canonical <: ErasedFuncSignature.CanonicalSignature
  val paramLists: Ls[Ls[Opt[ErasedValueType]]]
  val ret: Opt[ErasedValueType]

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
    /** Resolves through an arbitrary chain of type aliases to the type symbols the alias denotes.
      *
      * A union alias denotes each of its members, so the result is a list; every other resolvable alias denotes a
      * single symbol. Type arguments are erased along the way, so `type Opt[A] = Some[A] | None` resolves to
      * `Some :: None :: Nil`.
      *
      * If the chain is not defined (e.g. in `declare type ...`), is cyclic, or contains a member that is itself
      * unresolvable, `sym` is returned unchanged.
      */
    def resolveTpeSymAlias: Ls[TypeSymbol] =
      // * Resolves a single type symbol, or `N` if it is an alias that cannot be resolved.
      def loop(cur: TypeSymbol, seen: Set[TypeSymbol]): Opt[Ls[TypeSymbol]] = cur match
        case als: TypeAliasSymbol =>
          if seen(als) then N
          else als.defn.flatMap(_.rhs).flatMap(alternatives(_, seen + als))
        case base => S(base :: Nil)
      // * Resolves the alternatives denoted by the right-hand side of an alias, flattening nested unions.
      // * Only unions are expanded: an intersection would call for a GLB, which the erased lattice cannot express.
      def alternatives(tpe: Term, seen: Set[TypeSymbol]): Opt[Ls[TypeSymbol]] = tpe match
        case Term.CompType(lhs, rhs, true) =>
          for
            ls <- alternatives(lhs, seen)
            rs <- alternatives(rhs, seen)
          yield ls ::: rs
        case _ => tpe.symbol.flatMap(_.asTpe).flatMap(loop(_, seen))
      loop(tpeSym, Set.empty).getOrElse(tpeSym :: Nil)
    
    // * A union alias denotes each of its members, and erases to their LUB; every other symbol resolves to itself
    // * or to a single alias target.
    resolveTpeSymAlias.map(resolved(rsc, _)).reduceLeft((lhs, rhs) => ErasedType.lub(lhs, rhs))

  /** Creates an instance from an already-resolved symbol. */
  private def resolved(rsc: Opt[Bool], sym: TypeSymbol)(using Ctx, State): CanonicalErasedValueType = sym match
    // * An unresolvable alias becomes the top type.
    case _: TypeAliasSymbol => ErasedType.Unknown
    case base =>
      // * `Unknown` drops `rsc`, which is meaningless on the top type. Every construction site passes
      // * `rsc = false` today; a future resource-type implementation must revisit this.
      // *
      // * Note that `base is ctx.builtins.Anything` is only necessary for `InvalMLPrelude.mls` - the `Anything` type
      // * is `declare class`-ed there (since `declare type` is not supported in `invalml`).
      if base is ctx.builtins.Anything then ErasedType.Unknown
      else PrimitiveType.values.find(_.sym === base) match
        case S(prim) => ErasedType.Primitive(prim)
        case _ => ErasedType.AnyRef(rsc, base)

/** Erased types of source declarations are initialized by Erasure after resolution finishes.
  * `null` means no representation has been assigned; `N` is an initialized, unknown representation.
  * The checked getter also protects derived values from caching an early `N`.
  * IR-generated symbols may initialize the same slot directly at construction.
  */
trait HasDelayedErasedType[T <: ErasedValueType]:
  private var assignedErasedType: Opt[T] = null
  final def isErased: Bool = assignedErasedType != null
  final def erasedType: Opt[T] =
    assert(isErased, "Erased type read before erasure")
    assignedErasedType
  final def erasedType_=(value: Opt[T]): Unit =
    assert(!isErased, "Erased type initialized more than once")
    assert(value != null, "An initialized erased type cannot be null")
    assignedErasedType = value
