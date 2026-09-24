package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable.ArrayBuffer

import hkmc2.utils.*


class PublisherTest extends AnyFunSuite:
  private class IntHost extends Host[Int]:
    def showDbg(using DebugPrinter): String = "integer shapes"
    def publish(shape: Int): Unit =
      if shapes.add(shape) then notifyShapeListeners(shape)

  test("subscribing during notification replays each shape exactly once"):
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
    val host = new IntHost
    host.publish(1)
    host.publish(2)
    val received = ArrayBuffer.empty[Int]
    host.subscribeToShapes: shape =>
      received += shape
      if shape == 1 then host.publish(3)
    host.publish(4)
    assert(received.toList == List(1, 3, 2, 4))
