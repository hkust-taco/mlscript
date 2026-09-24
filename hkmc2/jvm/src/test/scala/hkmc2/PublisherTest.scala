package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable.ArrayBuffer

import hkmc2.utils.*
import hkmc2.semantics.{Elaborator, NewResolverState, Term, VarSymbol, DynShape, OpaqueTypeShape, TermShape}


class PublisherTest extends AnyFunSuite:
  private class IntHost extends Host[Int]:
    def showDbg(using DebugPrinter): String = "integer shapes"
    def publish(shape: Int)(using NewResolverState): Unit =
      if currentShapes.add(shape) then notifyShapeListeners(shape)

  test("subscribing during notification replays each shape exactly once"):
    given NewResolverState = new Elaborator.State().newResolverState
    val host = new IntHost
    val original = ArrayBuffer.empty[Int]
    val added = ArrayBuffer.empty[Int]
    val last = ArrayBuffer.empty[Int]
    host.subscribeToShapes: shape =>
      original += shape
      if shape == 1 then host.subscribeToShapes(added += _)
    host.subscribeToShapes(last += _)
    host.publish(1)
    host.publish(2)
    assert(original.toList == List(1, 2))
    assert(added.toList == List(1, 2))
    assert(last.toList == List(1, 2))

  test("publishing during replay does not replay the newly published shape again"):
    given NewResolverState = new Elaborator.State().newResolverState
    val host = new IntHost
    host.publish(1)
    host.publish(2)
    val received = ArrayBuffer.empty[Int]
    host.subscribeToShapes: shape =>
      received += shape
      if shape == 1 then host.publish(3)
    host.publish(4)
    assert(received.toList == List(1, 3, 2, 4))

  test("imported listeners route captured destinations through each consumer state"):
    val original = new Elaborator.State().newResolverState
    val first = new Elaborator.State().newResolverState
    val second = new Elaborator.State().newResolverState
    val source = new IntHost
    val target = new IntHost
    locally:
      given NewResolverState = original
      // Include a cycle: each consumer must install a host copy before invoking
      // listeners that can immediately return to that same host.
      source.subscribeToShapes(target.publish)
      target.subscribeToShapes(source.publish)
      source.publish(1)
    val sourceListeners = source.shapeListeners.size
    val targetListeners = target.shapeListeners.size
    source.publish(2)(using first)
    source.publish(3)(using second)
    assert(source.currentShapes(using original).toList == List(1))
    assert(target.currentShapes(using original).toList == List(1))
    assert(target.currentShapes(using first).toList == List(1, 2))
    assert(target.currentShapes(using second).toList == List(1, 3))
    assert(source.shapeListeners.size == sourceListeners)
    assert(target.shapeListeners.size == targetListeners)

  test("imports lazily retain exporter-private inference on third-party hosts"):
    val declaration = new Elaborator.State().newResolverState
    val exporter = new Elaborator.State().newResolverState
    val consumer = new Elaborator.State().newResolverState
    val source = new IntHost
    val target = new IntHost
    source.publish(1)(using declaration)
    source.subscribeToShapes(target.publish)(using exporter)
    source.publish(2)(using exporter)
    source.publish(3)(using consumer)
    // Unrelated exporter state must not be copied merely to import this host.
    (1 to 1000).foreach: n =>
      val unrelated = new IntHost
      unrelated.publish(n)(using exporter)
    val exported = source.inferenceHost(using exporter)
    assert(consumer.copiedHostCount == 1)
    exported.publish(4)(using consumer)
    assert(source.currentShapes(using declaration).toList == List(1))
    assert(source.currentShapes(using exporter).toList == List(1, 2))
    assert(source.currentShapes(using consumer).toSet == Set(1, 3))
    assert(consumer.local(exported).shapes.toSet == Set(1, 2, 4))
    assert(target.currentShapes(using consumer).toSet == Set(1, 2, 4))
    assert(consumer.copiedHostCount == 3)
    assert(target.currentShapes(using exporter).toList == List(1, 2))

  test("re-exported listeners retain intermediate exporters' private destinations"):
    val declaration = new Elaborator.State().newResolverState
    val exporter = new Elaborator.State().newResolverState
    val middle = new Elaborator.State().newResolverState
    val consumer = new Elaborator.State().newResolverState
    val source = new IntHost
    val target = new IntHost
    val referencedTarget = new IntHost
    val reference = referencedTarget.inferenceHost(using declaration)
    locally:
      given NewResolverState = declaration
      source.subscribeToShapes: shape =>
        target.publish(shape)
        reference.publish(shape)
    source.publish(1)(using declaration)
    source.publish(2)(using exporter)
    val exportedSource = source.inferenceHost(using exporter)
    val exportedTarget = target.inferenceHost(using exporter)
    val exportedReference = referencedTarget.inferenceHost(using exporter)
    exportedSource.publish(3)(using middle)
    val forwarded = middle.local(exportedSource)
    forwarded.publish(4)(using consumer)
    assert(source.currentShapes(using declaration).toList == List(1))
    assert(target.currentShapes(using exporter).toList == List(1, 2))
    assert(middle.local(exportedTarget).shapes.toList == List(1, 2, 3))
    assert(consumer.local(middle.local(exportedTarget)).shapes.toList == List(1, 2, 3, 4))
    assert(consumer.local(middle.local(exportedReference)).shapes.toList == List(1, 2, 3, 4))

  test("completing a block freezes its nodes while retaining symbol and elimination flow"):
    given owner: Elaborator.State = new Elaborator.State
    given state: NewResolverState = owner.newResolverState
    val variable = new VarSymbol(new syntax.Tree.Ident("x"))
    val use = Term.NewSel(Term.SimpleRef(variable)(new syntax.Tree.Ident("x")),
      new syntax.Tree.Ident("value"), None)(semantics.FlowSymbol.sel("value"))
    use.hasDynamicTarget = true
    variable.subscribeToShapes: shape =>
      if use.currentShapes.add(shape) then use.notifyShapeListeners(shape)
    def publish(shape: TermShape)(using NewResolverState): Unit =
      if variable.currentShapes.add(shape) then variable.notifyShapeListeners(shape)
    val before = DynShape()
    val after = OpaqueTypeShape(Term.UnitVal())
    publish(before)
    val originalListeners = use.shapeListeners.toVector
    state.completeBlock(use)
    publish(after)
    assert(variable.currentShapes.toSet == Set(before, after))
    assert(use.currentShapes.toSet == Set(before, after))
    assert(use.shapes.toSet == Set(before))
    assert(use.shapeListeners.toVector == originalListeners)
    intercept[AssertionError]:
      state.recordResolution(use, false)(use.tupleIndex = Some(0))
    assert(use.tupleIndex.isEmpty && use.hasDynamicTarget)
    // A new node in the same worksheet state is still open for resolution.
    val next = Term.UnitVal()
    next.inferenceHost
    assert(state.canResolve(next))
    state.recordResolution(use, true)(fail("An unchanged decision must not be written again"))

  test("temporary observers replay once, detach, and are not inherited by consumers"):
    given original: NewResolverState = new Elaborator.State().newResolverState
    val host = new IntHost
    val observed = ArrayBuffer.empty[Int]
    val routed = ArrayBuffer.empty[Int]
    host.publish(1)
    host.subscribeToShapes(routed += _)
    val detach = host.inferenceHost.observe(observed += _)
    host.publish(2)
    val consumer = new Elaborator.State().newResolverState
    host.publish(3)(using consumer)
    assert(observed.toList == List(1, 2))
    assert(routed.toList == List(1, 2, 3))
    detach()
    host.publish(4)
    assert(observed.toList == List(1, 2))
    assert(routed.toList == List(1, 2, 3, 4))

  test("unknown provenance is lazy and does not affect shape identity"):
    import semantics.{ShapeProvenance, UnknownValueShape, RecordShape}
    import Message.MessageContext
    var evaluated = 0
    def provenance = ShapeProvenance {
      evaluated += 1
      Nil
    }
    val source = Term.UnitVal()
    val first = UnknownValueShape(source)(provenance)
    val second = UnknownValueShape(source)(provenance)
    assert(Set(first, second).size == 1)
    assert(RecordShape.Unknown(source)(provenance) == RecordShape.Unknown(source)(provenance))
    assert(evaluated == 0)
    assert(first.provenance.diagnosticNotes.isEmpty)
    assert(first.provenance.diagnosticNotes.isEmpty)
    assert(evaluated == 1)
    var noteEvaluated = 0
    val extended = first.provenance.via {
      noteEvaluated += 1
      msg"A deferred provenance step" -> None
    }
    assert(noteEvaluated == 0)
    assert(extended.diagnosticNotes.size == 1)
    assert(extended.diagnosticNotes.size == 1)
    assert(noteEvaluated == 1)
    assert(evaluated == 1)
