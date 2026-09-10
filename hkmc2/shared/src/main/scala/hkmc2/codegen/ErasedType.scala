package hkmc2
package codegen

import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import utils.*

import semantics.*
import semantics.Elaborator.{Ctx, State, ctx}
import semantics.Term.*
import sourcecode.{FileName, Line}

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
  case class AnyRef(rsc: Opt[Bool], tpeSym: TypeSymbol) extends ErasedValueType, CanonicalErasedType:
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

  /** A reference to a function of a possibly-known shape.
    *
    * - `rsc` is true if this reference is a resource function.
    */
  case class FuncRef(override val rsc: Opt[Bool], override val paramLists: Ls[Ls[Opt[ErasedValueType]]], override val ret: Opt[ErasedValueType]) extends ErasedFuncType:
    ErasedFuncType.assertHasParamLists(paramLists)
    override type Canonical = CanonicalFuncRef
    override protected def computeCanonicalize(using Ctx, State): CanonicalFuncRef =
      CanonicalFuncRef(rsc, paramLists.map(_.map(_.map(_.canonicalize))), ret.map(_.canonicalize))

  /** An analogue to `FuncRef` for function types with canonicalized parameter and return types. */
  case class CanonicalFuncRef(override val rsc: Opt[Bool], override val paramLists: Ls[Ls[Opt[CanonicalErasedValueType]]], override val ret: Opt[CanonicalErasedValueType]) extends ErasedFuncType with CanonicalErasedType:
    ErasedFuncType.assertHasParamLists(paramLists)

  /** A primitive type. */
  case class Primitive(prim: PrimitiveType) extends ErasedValueType, CanonicalErasedType:
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

  /** The top type of reference types, i.e. any value on JS and `anyref` on Wasm.
    *
    * Reached by an absent annotation (`erasedType_!` folds `N` here), by an alias the IR cannot resolve, and
    * by the surface top `Anything`, which has no erased counterpart of its own.
    */
  case object Unknown extends ErasedValueType, CanonicalErasedType:
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
      extends ErasedValueType, CanonicalErasedType:
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
    def flatten(et: ErasedValueType): Ls[ErasedValueType] = et match
      case Union(ms) => ms
      case other => other :: Nil
    // Note: `distinct` has no effect on `ValueLike` types, which are identity-equal, but that is fine since they will
    // be collapsed during canonicalization.
    (flatten(lhs) ::: flatten(rhs)).distinct match
      case single :: Nil => single
      case ms => Union(ms)

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

  /** Erases a type-annotated term to an [[ErasedType]].
    *
    * Note that the resulting erased type is **not** canonicalized to avoid using `ctx.builtins` during elaboration
    * of `Prelude`.
    */
  def eraseSign(sign: Term): Opt[ErasedValueType] = sign match
    case CompType(lhs, rhs, true) =>
      // * A union is kept as a transient `Union` surface form; `canonicalize` collapses it to the members' LUB.
      for
        l <- eraseSign(lhs)
        r <- eraseSign(rhs)
      yield ErasedType.union(l, r)
    // * An intersection is never decomposed: narrowing to one member would call for a GLB, which this lattice
    // * cannot express.
    case CompType(_, _, false) => S(ErasedType.Unknown)
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
  def needsCast(actual: CanonicalErasedType, expected: CanonicalErasedType)(using Ctx, State): Opt[Bool] =
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

/** A generics-erased type of the Block IR. */
sealed abstract class ErasedType:
  type Canonical <: CanonicalErasedType

  /** The symbol denoting this erased type, or `NoSymbol` when none does.
    *
    * The lattice is keyed on `TypeSymbol`, so `NoSymbol` means this type has no place in it: no ancestor chain to
    * walk and no name to report.
    */
  def sym(using Ctx, State): TypeSymbol | NoSymbol

  /** Memoized canonical form, written once by [[canonicalize]] and read only through it.
    *
    * Note that the canonicalized type is only meaningful within the `State` it was computed under.
    */
  private var _canonicalized: Opt[Canonical] = N

  /** The canonical form of this type, computed by [[computeCanonicalize]] on first use and memoized thereafter.
    *
    * Callers are encouraged to always canonicalize types before using them.
    */
  final def canonicalize(using Ctx, State): Canonical = _canonicalized match
    case S(n) => n
    case N =>
      val n = computeCanonicalize
      _canonicalized = S(n)
      n

  /** Computes the canonical form of this type, by resolving type aliases to their target type, reclassifying unboxed
    * primitive symbols to [[Primitive]], and collapsing unions to their least upper bound (LUB).
    *
    * Each overriding implementation performs the ones that apply to it; alias resolution and primitive
    * reclassification both happen in [[CanonicalErasedValueType.apply]].
    *
    * Intersections are never decomposed and is erased to [[Unknown]].
    *
    * Call [[canonicalize]] rather than this, so that the result is memoized.
    */
  protected def computeCanonicalize(using Ctx, State): Canonical

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

/** Base class indicating that the [[ErasedType]] is a value type. */
sealed abstract class ErasedValueType extends ErasedType:
  type Canonical <: CanonicalErasedValueType

object ErasedFuncType:
  /** Enforces the invariant that `paramLists` must be non-empty.
    *
    * See the documentation of [[ErasedFuncType]] for the rationale.
    */
  def assertHasParamLists(paramLists: Ls[Ls[?]]): Unit =
    assert(paramLists.nonEmpty, "a function type must describe at least one parameter list")

/** Base class indicating that the [[ErasedType]] is a function type.
  *
  * `paramLists` mirrors the definition's parameter *lists*, so that curried functions can be represented - functions
  * that are partially applied yield a function type with fewer parameter lists.
  *
  * Note that `paramLists` should never be empty: a definition declaring no parameter list at all is either compiled
  * to a getter and erased to its result instead, or given an implicitly-added empty parameter list which the erased
  * type mirrors.
  */
sealed abstract class ErasedFuncType extends ErasedType:
  val rsc: Opt[Bool]
  val paramLists: Ls[Ls[Opt[ErasedValueType]]]
  val ret: Opt[ErasedValueType]
  final override def sym(using Ctx, State): TypeSymbol = ctx.builtins.Function

/** An [[ErasedType]] that is resolved into a canonical representation. */
sealed trait CanonicalErasedType extends ErasedType:
  type Canonical = this.type

  override protected def computeCanonicalize(using Ctx, State): this.type = this

type CanonicalErasedValueType = CanonicalErasedType & ErasedValueType

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

/** Trait representing a Block IR element that has an [[ErasedType]]. */
trait HasErasedType:
  /** The [[ErasedType]] of this element, or `N` if the erased type is not known. */
  def erasedType: Opt[ErasedType]

  /** Similar to `erasedType`, but coerces to the top type if the specific erased type is not known.
    *
    * Parameter and return types of [[ErasedFuncType]]s are recursively coerced.
    */
  lazy val erasedType_! : ErasedType = erasedType.fold(ErasedType.Unknown):
    case f @ ErasedType.FuncRef(rsc, paramLists, ret) => f.copy(
      paramLists = paramLists.map(_.map(p => S(p.getOrElse(ErasedType.Unknown)))),
      ret = S(ret.getOrElse(ErasedType.Unknown)),
    )
    case f @ ErasedType.CanonicalFuncRef(rsc, paramLists, ret) => f.copy(
      paramLists = paramLists.map(_.map(p => S(p.getOrElse(ErasedType.Unknown)))),
      ret = S(ret.getOrElse(ErasedType.Unknown)),
    )
    case vt: ErasedValueType => vt

  /** Returns the [[ErasedValueType]] of this element, or `N` if the erased type is not known.
    *
    * If this type is a [[ErasedFuncType]], the result is the [[ErasedType]] of a first-class function.
    */
  lazy val erasedValueType: Opt[ErasedValueType] = erasedType.collect:
    case ft: ErasedFuncType => ErasedType.Function(ft.rsc)
    case vt: ErasedValueType => vt

  /** Similar to `erasedValueType`, but coerces to the top type if the specific erased value type is not known. */
  lazy val erasedValueType_! : ErasedValueType = erasedValueType.getOrElse(ErasedType.Unknown)

/** A [[HasErasedType]] whose erased type can be populated exactly once post-construction. */
trait HasOnceMutableErasedType extends HasErasedType:
  // Implementation Note: Provided for overriding classes to implement `erasedType` directly as an `override var`
  def erasedType_=(newType: Opt[ErasedType]): Unit

  /** Populates the erased type, or raises a soft assertion if the type was already populated. */
  def populateErasedType(newType: ErasedType)(using Line, FileName, Raise): Unit =
    softAssert(erasedType.isEmpty, s"Cannot refine already-refined erased type $erasedType to $newType")
    if erasedType.isEmpty then erasedType = S(newType)

extension (s: ValueSymbol | DefinitionSymbol[?])
  /** Maps the symbol to its erased value type, if it has one.
    *
    * This is the type of the *value* a reference to the symbol denotes, so a symbol standing for a function
    * collapses to the first-class `Function` type instead of keeping its [[ErasedFuncType]] shape - the same
    * narrowing [[Result.coerceTo]] performs when it introduces a cast.
    */
  def mapErasedValueType(using Raise): Opt[ErasedValueType] = s match
    case v: VarSymbol => v.erasedType
    case t: TempSymbol => t.erasedValueType
    case c: (ClassSymbol | ModuleOrObjectSymbol) => c.erasedValueType
    case t: TermSymbol => t.erasedValueType
    // * A pattern is not a value and carries no erased type of its own, so a reference to one is
    // * left unknown rather than treated as an unexpected symbol.
    case _: PatternSymbol => N
    // * A builtin operator carries no erased type, as one symbol stands for its nullary, unary and binary forms.
    case _: BuiltinSymbol => N
    // * What a member reference denotes depends on the member: a function value has the `Function` type, but a
    // * class object has none, so this is left unknown rather than guessed from the disambiguating term symbol.
    case _: BlockMemberSymbol => N
    case s =>
      softAssert(false, s"Unexpected symbol type for symbol `$s`: ${s.getClass.getName}")
      N
