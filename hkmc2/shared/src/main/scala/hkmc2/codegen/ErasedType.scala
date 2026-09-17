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

object PrimitiveType:
  /** The primitive type whose symbol is `sym`, if any. */
  def of(sym: TypeSymbol)(using Ctx, State): Opt[PrimitiveType] = values.find(_.sym === sym)

object ErasedType:
  /** A canonicalized reference type.
    *
    * Instances should be created using [[CanonicalErasedValueType.apply]] or [[ValueLike]] to ensure the correct
    * representation is used for a given type symbol.
    *
    * Implementation Note: This type should **not** be used to represent references of type aliases or the top type -
    * [[ValueLike]] and [[Unknown]] should be used instead.
    */
  case class AnyRef(rsc: Opt[Bool], tpeSym: TypeSymbol) extends ErasedValueType, CanonicalErasedValueType, HasRsc:
    override def sym(using Ctx, State): TypeSymbol = tpeSym

  /** A value type that is not yet canonicalized.
    *
    * Implementation Notes:
    *
    * - This transient type is needed to represent value types before the `Prelude` is fully elaborated. The IR should
    *   always operate on the canonicalized type.
    * - This type implements identity equality, so that two instances with the same `getTpeSym` function are not
    *   considered equal - Use the canonicalized type for equality comparisons.
    */
  final class ValueLike(val rsc: Opt[Bool], getTpeSym: (Ctx, State) ?=> TypeSymbol) extends ErasedValueType, HasRsc:
    override type Canonical = CanonicalErasedValueType
    override def sym(using Ctx, State): TypeSymbol = getTpeSym
    override protected def computeCanonicalize(using Ctx, State): CanonicalErasedValueType =
      val canon = CanonicalErasedValueType(rsc, sym)
      // * A canonical type with resource-ness takes it from this reference if it is `rsc`, which overrides the
      // * modifiers written inside the alias referred to. Otherwise, it can only differ from this reference's
      // * resource-ness because of such a modifier.
      canon match
      case h: HasRsc if h.rsc =/= rsc =>
        assert(rsc =/= S(true) && CanonicalErasedValueType.resolveTpeSymAlias(sym).exists(_.ownRsc.isDefined),
          s"the resource-ness of '$canon' must come from this reference ($rsc), or from a modifier inside '$sym' " +
            "when this reference is not `rsc`")
      case _ => ()
      canon
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
    * Reached by an absent annotation, an alias the IR cannot resolve, a resource-modified type-parameter reference,
    * and by the surface top `Anything`, which has no erased counterpart of its own.
    */
  case class Unknown(rsc: Opt[Bool]) extends ErasedValueType, CanonicalErasedValueType, HasRsc:
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

  /** The builtin `Function` reference type, used as the value type of a first-class function. */
  def Function(rsc: Opt[Bool]): ErasedValueType = ErasedType.ValueLike(rsc, ctx.builtins.Function)

  /** Determines the direct parent of a class-like symbol.
    *
    * Returns:
    * - `S(S(parent))` for a class with a resolvable parent.
    * - `S(N)` for a root class with no parent.
    * - `N` for a class whose parent chain is not available in the IR (e.g. an unlinked import).
    */
  private def parentOf(sym: BaseTypeSymbol)(using Ctx, State): Opt[Opt[TypeSymbol]] =
    sym.asClsOrMod.flatMap: sym =>
      sym.irClsLikeDefn.flatMap: defn =>
        defn.parentPath match
        case S(parent) => parent.targetSymbol.collect { case s: TypeSymbol => s }.map(S(_))
        case N => S(N)
      .orElse:
        // FIXME: remove this fallback once imported classes have their `irClsLikeDefn` properly linked
        sym.defn.flatMap: defn =>
          defn.ext match
            case S(parent) => parent.cls.resolvedSym.flatMap(_.asClsOrMod).map(S(_))
            case N => S(N)

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
          case S(S(parent)) => loop(parent, seen + cur, cur :: acc)
          case S(N) => AncestorChain((cur :: acc).reverse, complete = true)
          case N => AncestorChain((cur :: acc).reverse, complete = false)
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

  /** The prefix naming a resource-ness in rendered output.
    *
    * A non-resource prints nothing: it is both the common case and the unannotated default, so spelling it
    * out would put a prefix on almost every type in a dump.
    */
  private[codegen] def rscPrefix(rsc: Opt[Bool]): Str = rsc.fold("rsc? ")(if _ then "rsc " else "")

  /** The least upper bound of two types' resource-ness. */
  private[codegen] def lubRsc(lhs: Opt[Bool], rhs: Opt[Bool]): Opt[Bool] =
    if lhs === rhs then lhs else N

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
      // * The top type absorbs every reference type, while the resource-ness joins.
      case (l: Unknown, r: HasRsc) => Unknown(lubRsc(l.rsc, r.rsc))
      case (l: HasRsc, r: Unknown) => Unknown(lubRsc(l.rsc, r.rsc))
      // * Two reference types: their nearest common ancestor, at worst `Object`.
      case (l: AnyRef, r: AnyRef) => CanonicalErasedValueType(lubRsc(l.rsc, r.rsc), lubSym(l.tpeSym, r.tpeSym))

  /** Erases a type-annotated term to an [[ErasedValueType]].
    *
    * Note that the resulting erased type is **not** canonicalized to avoid using `ctx.builtins` during elaboration
    * of `Prelude`.
    */
  def eraseSign(sign: Term): Opt[ErasedValueType] = eraseSign(sign, rsc = S(false))

  /** Whether erasing the `target` term under a resource modifier denoting `rsc` keeps the modifier.
    *
    * The modifier is dropped when `target` has no erased counterpart (e.g. a negation type), or when `target` erases to
    * a type that is never a resource (`()`).
    */
  def keepsRsc(target: Term, rsc: Opt[Bool]): Bool = eraseSign(target, rsc).exists:
    case h: HasRsc => h.rsc === rsc
    case _ => false

  /** Erases `sign` under the resource-ness gathered from the modifiers wrapping it so far. */
  private def eraseSign(sign: Term, rsc: Opt[Bool]): Opt[ErasedValueType] = sign match
    // * The resource modifiers reach here as annotations.
    // * Note that this arm has to be part of the recursion: a union erases its members by recursive call, and each
    // * carries its own modifier, so `rsc C | rsc D` would otherwise erase to nothing at all.
    case Term.Annotated(Annot.Resource(own), target) =>
      eraseSign(target, CanonicalErasedValueType.combineRsc(rsc, S(own)))
    case CompType(lhs, rhs, true) =>
      // * A union is kept as a transient `Union` surface form; `canonicalize` collapses it to the members' LUB.
      for
        l <- eraseSign(lhs, rsc)
        r <- eraseSign(rhs, rsc)
      yield ErasedType.union(l, r)
    // * An intersection is never decomposed: narrowing to one member would call for a GLB, which this lattice
    // * cannot express.
    case CompType(_, _, false) => S(ErasedType.Unknown(rsc))
    case UnitVal() => S(ErasedType.Unit)
    // * A written function type denotes a function value, and every function value is a `Function`.
    case FunTy(_, _, _) => S(ErasedType.Function(rsc))
    // * Quantification erases away: what a `forall` denotes is what its body denotes.
    case Forall(_, _, body) => eraseSign(body, rsc)
    // * A type parameter has no erased counterpart, so a reference to one erases to the top type under the modifier
    // * written on it. `rsc` starts as `S(false)` and no syntax writes a non-resource modifier, so `S(false)` here
    // * means that the reference is unannotated: it then erases to nothing, as it did before resource modifiers.
    case Ref(sym: VarSymbol) if ModuleChecker.isTypeParam(sym) && rsc =/= S(false) => S(ErasedType.Unknown(rsc))
    case _ => sign.symbol.flatMap(_.asTpe).map(sym => ErasedType.ValueLike(rsc, sym))

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
    // * A value has to fit the slot in both its identity and its resource-ness: a cast is needed when either
    // * dimension calls for one, and the coercion is impossible when either says it is.
    needsClassCast(actual, expected).flatMap: byClass =>
      (actual, expected) match
      case (a: HasRsc, e: HasRsc) => needsRscCast(a.rsc, e.rsc).map(byClass || _)
      // * The class dimension only admits a primitive into the same primitive, which has no resource-ness.
      case (_: Primitive, _: Primitive) => S(byClass)
      case _ => lastWords(s"a coercion from '$actual' to '$expected' passed the class dimension")

  /** Whether the resource-ness dimension of a coercion needs a cast.
    *
    * A resource and a non-resource have different resource-tracking strategies, so neither can be coerced to the other.
    * Both widen freely into the undetermined layout, and narrowing back out of it is the runtime ref-count test.
    */
  private def needsRscCast(actual: Opt[Bool], expected: Opt[Bool]): Opt[Bool] =
    (actual, expected) match
    case _ if actual === expected => S(false)
    case (_, N) => S(false)
    case (N, _) => S(true)
    case (S(_), S(_)) => N

  /** Whether the class dimension of a coercion needs a cast, ignoring resource-ness. */
  private def needsClassCast(actual: CanonicalErasedValueType, expected: CanonicalErasedValueType)(using Ctx, State): Opt[Bool] =
    (actual, expected) match
      // * A type with no upper bound has no representation of its own, so nothing can be coerced into or out of
      // * it - not even widened into the top type.
      case (_: Incompatible, _) | (_, _: Incompatible) => N
      case (Primitive(a), Primitive(b)) => if a == b then S(false) else N
      // * A primitive is compatible only with the same primitive in either direction.
      case (Primitive(_), _) | (_, Primitive(_)) => N
      // * `T -> Unknown` needs no cast; `Unknown -> T` needs a checked downcast.
      case (_, _: Unknown) => S(false)
      case (_: Unknown, _) => S(true)
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
    * Intersections are never decomposed and is erased to [[ErasedType.Unknown]].
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
      case ErasedType.Unknown(rsc) => s"${ErasedType.rscPrefix(rsc)}Unknown"
      case ErasedType.Incompatible(l, r) => s"‹incompatible(${l.describe}, ${r.describe})›"
      case cet => cet.sym match
        case NoSymbol => lastWords(s"no name is defined for '$cet'")
        case tpeSym: TypeSymbol =>
          val name = qualify(tpeSym, Nil).mkString(".")
          val rscPrefix = cet match
            case r: HasRsc => ErasedType.rscPrefix(r.rsc)
            case _ => ""
          if tpeSym.asMod.isDefined then s"${rscPrefix}module $name" else s"$rscPrefix$name"

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

/** An [[ErasedValueType]] that may be associated with resource-ness. */
sealed trait HasRsc extends ErasedValueType:
  /** Whether this type is a resource, or `N` if that is not known statically.
    *
    * Note that `rsc?` (represented by `N`) and non-`rsc` (represented by `S(false)`) represent two different things:
    * `N` indicates that the resource-ness is not known statically and requires a runtime test, while `S(false)`
    * indicates that it is not a resource.
    */
  val rsc: Opt[Bool]

object CanonicalErasedValueType:
  /** A member of what a type alias denotes (see [[resolveTpeSymAlias]]).
    *
    * - `sym` is the member's type symbol, or `N` if the member cannot be resolved: a recursive occurrence of an
    *   alias, a type parameter, or an alias without a definition.
    * - `ownRsc` is the resource modifier written on the member inside the alias - the outer `Opt` representing whether
    *   a resource modifier is present, and the inner `Opt` the resource-ness it denotes, encoded as in `HasRsc.rsc`.
    */
  case class AliasMember(sym: Opt[TypeSymbol], ownRsc: Opt[Opt[Bool]])

  /** Creates an instance with the given type symbol, canonicalizing it if needed. */
  def apply(rsc: Opt[Bool], tpeSym: TypeSymbol)(using Ctx, State): CanonicalErasedValueType =
    val members = resolveTpeSymAlias(tpeSym)
    // * An unannotated reference has `rsc = S(false)`, which a member's own modifier takes precedence over.
    def rscOf(m: AliasMember): Opt[Bool] = combineRsc(rsc, m.ownRsc)
    if members.forall(_.sym.isDefined) then
      // * A union alias denotes each of its members, and erases to their LUB; every other symbol resolves to itself
      // * or to a single alias target.
      members.flatMap(m => m.sym.map(resolved(rscOf(m), _))).reduceLeft((lhs, rhs) => ErasedType.lub(lhs, rhs))
    else
      // * An alias with a member that cannot be resolved erases to the top type while preserving its resource-ness.
      val rscs = members.filterNot(_.sym.exists(PrimitiveType.of(_).isDefined)).map(rscOf)
      ErasedType.Unknown(rscs.reduceLeft(ErasedType.lubRsc))

  /** Resolves through an arbitrary chain of type aliases to the members the alias denotes.
    *
    * A union alias denotes each of its members, so the result is a list; every other alias denotes a single member.
    * Type arguments are erased along the way, so `type Opt[A] = Some[A] | None` resolves to `Some :: None :: Nil`.
    *
    * A member that cannot be resolved has its resource modifier kept. A modifier on a reference to an alias combines
    * with the ones written inside it as described in [[combineRsc]].
    */
  def resolveTpeSymAlias(tpeSym: TypeSymbol)(using Ctx): Ls[AliasMember] =
    def resolveSym(cur: TypeSymbol, seen: Set[TypeAliasSymbol]): Ls[AliasMember] = cur match
      case als: TypeAliasSymbol => als.defn.flatMap(_.rhs) match
        case S(rhs) if !seen(als) => alternatives(rhs, seen + als, N)
        case _ => AliasMember(N, N) :: Nil
      case base => AliasMember(S(base), N) :: Nil
    // * Resolves the alternatives denoted by the right-hand side of an alias under the resource modifier written
    // * around it, flattening nested unions.
    // * Only unions are expanded: an intersection would call for a GLB, which the erased lattice cannot express.
    def alternatives(tpe: Term, seen: Set[TypeAliasSymbol], ownRsc: Opt[Opt[Bool]]): Ls[AliasMember] = tpe match
      case Term.Annotated(Annot.Resource(own), target) =>
        alternatives(target, seen, S(ownRsc.fold(own)(combineRsc(_, S(own)))))
      case Term.CompType(lhs, rhs, true) => alternatives(lhs, seen, ownRsc) ::: alternatives(rhs, seen, ownRsc)
      // * As in `ErasedType.eraseSign`, quantification erases away, and a written function type denotes a function
      // * value, which is a `Function`.
      case Term.Forall(_, _, body) => alternatives(body, seen, ownRsc)
      case Term.FunTy(_, _, _) => AliasMember(S(ctx.builtins.Function), ownRsc) :: Nil
      case _ =>
        tpe.symbol.flatMap(_.asTpe).fold(AliasMember(N, N) :: Nil)(resolveSym(_, seen))
          .map(m => m.copy(ownRsc = ownRsc.map(combineRsc(_, m.ownRsc)).orElse(m.ownRsc)))
    resolveSym(tpeSym, Set.empty)

  /** The resource-ness of a member of an alias or of a written union, given the resource-ness `outer` stated around it
    * (on a reference to the alias, or on the union) and the resource modifier `own` written on the member itself
    * (encoded as in [[AliasMember.ownRsc]]).
    *
    * `rsc` asserts that the whole type is a resource, so it overrides the member's own modifier: `rsc List` is a
    * resource where `type List = Cons | Nil`. Any other resource-ness leaves the member's own modifier in place:
    * `rsc? U` where `type U = rsc A | B` is `rsc A | rsc? B`, which erases to `rsc? lub(A, B)`.
    */
  private[codegen] def combineRsc(outer: Opt[Bool], own: Opt[Opt[Bool]]): Opt[Bool] =
    if outer === S(true) then outer else own.getOrElse(outer)

  /** Creates an instance from an already-resolved symbol. */
  private def resolved(rsc: Opt[Bool], sym: TypeSymbol)(using Ctx, State): CanonicalErasedValueType = sym match
    // * `resolveTpeSymAlias` resolves every alias, or yields a member without a symbol for it.
    case als: TypeAliasSymbol => lastWords(s"the type alias '$als' was not resolved")
    case base =>
      // * Note that `base is ctx.builtins.Anything` is only necessary for `InvalMLPrelude.mls` - the `Anything` type
      // * is `declare class`-ed there (since `declare type` is not supported in `invalml`).
      if base is ctx.builtins.Anything then ErasedType.Unknown(rsc)
      else PrimitiveType.of(base) match
        // * A primitive has no resource-ness, so `rsc` is dropped.
        case S(prim) => ErasedType.Primitive(prim)
        case _ => ErasedType.AnyRef(rsc, base)

extension (s: ValueSymbol | DefinitionSymbol[?])
  /** Maps the symbol to its erased value type, if it has one.
    *
    * This is the type of the *value* a reference to the symbol denotes, so a function's symbol maps to the first-class
    * `Function` type rather than to its [[ErasedFuncSignature]].
    */
  def mapErasedValueType(using Raise): Opt[ErasedValueType] = s match
    case l: LocalVarSymbol => l.erasedType
    case c: (ClassSymbol | ModuleOrObjectSymbol) => c.erasedType
    case t: TermSymbol => t.erasedType
    // * A pattern is not a value and carries no erased type of its own, so a reference to one is
    // * left unknown rather than treated as an unexpected symbol.
    case _: PatternSymbol => N
    // * A builtin operator carries no erased type, as one symbol stands for its nullary, unary and binary forms.
    case _: BuiltinSymbol => N
    // * What a member reference denotes depends on the member: a function value has the `Function` type, but a
    // * class object has none, so this is left unknown rather than guessed from the disambiguating term symbol.
    case _: BlockMemberSymbol => N
    // * No reference to a value is expected to resolve to these symbols.
    case s: (TypeAliasSymbol | TopLevelSymbol) =>
      softAssert(false, s"Unexpected symbol type for symbol `$s`: ${s.getClass.getName}")
      N
