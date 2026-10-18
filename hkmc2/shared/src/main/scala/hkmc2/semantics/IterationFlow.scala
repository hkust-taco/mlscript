package hkmc2
package semantics

/** One pair of call sites per spread source. Incoming alternatives share these
  * observations and the element host, so their Cartesian product is never built.
  * Publisher storage and listeners remain owned by the consuming resolution graph.
  */
private[semantics] final class IterationFlow(
    val elements: TypeResolution, val iterator: Term.App, val next: Term.App,
    val iteratorMember: FlowSymbol, val nextMember: FlowSymbol, val doneMember: FlowSymbol, val valueMember: FlowSymbol)
