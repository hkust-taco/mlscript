package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** A flat substitution from source binders to canonical call-site instances.
  * The immutable map is construction data, hashed once here. Resolver keys keep
  * this value instead of repeatedly hashing a raw map. Equality across
  * compilation units remains a shallow comparison of binder/instance identities.
  */
final class TypeSubstitution private (private val bindings: Map[VarSymbol, TypeParameterInstance]) extends ValueKey:
  export bindings.{apply, get, getOrElse, isEmpty, nonEmpty, size, keySet, keysIterator, values, iterator, forall, map}
  override def toString: Str = bindings.iterator.map((binder, instance) => s"$binder -> $instance").mkString("TypeSubstitution(", ", ", ")")
  protected val valueHash: Int = ValueKey.hash(ValueKey.tag(this), ValueKey.mapHash(bindings)(System.identityHashCode, System.identityHashCode))
  protected def sameValue(other: ValueKey): Bool = other match
    case that: TypeSubstitution => bindings == that.bindings
    case _ => false

  // Composition is pure: cached tuple layouts may compose these values while
  // being read by an importer. Intern at activation/type construction boundaries,
  // never by mutating the state captured by an exported shape.
  def withOverrides(that: TypeSubstitution): TypeSubstitution =
    if that.isEmpty || (this eq that) then this
    else if isEmpty then that
    else if that.bindings.forall((binder, instance) => bindings.get(binder).contains(instance)) then this
    else TypeSubstitution.fromMap(bindings ++ that.bindings)
  def without(parameters: IterableOnce[VarSymbol]): TypeSubstitution =
    if isEmpty then this else TypeSubstitution.fromMap(bindings -- parameters)
  /** Project a view's support without changing any binder/instance pairing. */
  def restrictTo(parameters: Set[VarSymbol]): TypeSubstitution =
    if bindings.keysIterator.forall(parameters) then this
    else TypeSubstitution.fromMap(bindings.filter((binder, _) => parameters(binder)))

object TypeSubstitution:
  val empty: TypeSubstitution = new TypeSubstitution(Map.empty)
  private def fromMap(bindings: Map[VarSymbol, TypeParameterInstance]): TypeSubstitution =
    if bindings.isEmpty then empty else new TypeSubstitution(bindings)
  private[semantics] def canonical(value: TypeSubstitution)(using ResolutionContext): TypeSubstitution =
    if value.isEmpty then empty else rctx.state.substitutions.getOrElseUpdate(value, value)
  def apply(instances: IterableOnce[TypeParameterInstance])(using ResolutionContext): TypeSubstitution =
    canonical(fromMap(instances.iterator.map(instance => instance.origin -> instance).toMap))
