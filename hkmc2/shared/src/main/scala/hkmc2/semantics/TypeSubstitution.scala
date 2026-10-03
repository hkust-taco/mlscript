package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** A flat substitution from source binders to their canonical call-site instances.
  * Keys are derived from instance origins; callers cannot choose a different key.
  * Composition preserves existing instance identities, never instantiates an
  * instance, and uses the right operand when both views interpret the same binder.
  * The opaque map retains structural equality for inference-cache keys.
  */
opaque type TypeSubstitution <: Map[VarSymbol, TypeParameterInstance] = Map[VarSymbol, TypeParameterInstance]

object TypeSubstitution:
  val empty: TypeSubstitution = Map.empty
  def apply(instances: IterableOnce[TypeParameterInstance]): TypeSubstitution =
    instances.iterator.map(instance => instance.origin -> instance).toMap

  extension (self: TypeSubstitution)
    def withOverrides(that: TypeSubstitution): TypeSubstitution = self ++ that
    def without(parameters: IterableOnce[VarSymbol]): TypeSubstitution = self -- parameters
