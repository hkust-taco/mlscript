package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*


/** Classify an observed shape before a consumer uses it as a value or a namespace probe.
  * The refinements preserve the original object and its marks without allocating wrappers.
  * Only dispatch creates them; shared inference hosts keep the unfiltered TermShape flow,
  * since a value consumer and a namespace constraint can observe the same host.
  */
private[semantics] object ShapeObserver:
  opaque type Value <: TermShape = TermShape
  opaque type Probe <: TermShape = TermShape
  type ValueListener = ShapeListener[Value]
  type ProbeListener = ShapeListener[Probe]

  inline def dispatch(shape: TermShape)(inline value: ValueListener, inline probe: ProbeListener)
      (using ResolutionContext): Unit = shape match
    case Marked(_: NamespaceProbe, _) => probe(shape)
    case _ => value(shape)

  def apply(value: ValueListener, probe: ProbeListener): ResolutionContext.Listener =
    shape => dispatch(shape)(value, probe)

  def values(value: ValueListener): ResolutionContext.Listener = apply(value, _ => ())
  def probes(probe: ProbeListener): ResolutionContext.Listener = apply(_ => (), probe)

  def reference(probe: Probe): Term.UnresolvedRef = probe match
    case Marked(probe: NamespaceProbe, _) => probe.ref
    case _ => lastWords("A probe observation must contain a namespace probe")
