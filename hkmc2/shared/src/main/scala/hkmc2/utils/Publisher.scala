package hkmc2
package utils

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet}

import hkmc2.utils.*, shorthands.*


trait Publisher[A]:
  // Listeners are append-only so callbacks may subscribe during notification.
  private[hkmc2] val shapeListeners: ArrayBuffer[A => Unit] = ArrayBuffer.empty

  private[hkmc2] def notifyShapeListeners(shape: A): Unit =
    // A new subscriber receives the current shape through replay. Only visit the
    // original listeners here, avoiding duplicate delivery and iterator invalidation.
    val count = shapeListeners.size
    var i = 0
    while i < count do
      shapeListeners(i)(shape)
      i += 1

trait Host[A] extends Publisher[A]:
  private[hkmc2] val shapes: LinkedHashSet[A] = LinkedHashSet.empty
  private[hkmc2] def subscribeToShapes(listener: A => Unit): Unit =
    shapeListeners += listener
    // Shapes are append-only and LinkedHashSet iteration preserves insertion order.
    // Shapes added by a replay callback are already delivered by notification.
    shapes.iterator.take(shapes.size).foreach(listener)
  def showDbg(using DebugPrinter): Str


