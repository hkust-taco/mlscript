package hkmc2
package utils

import scala.collection.mutable.{Buffer, Set as MutSet, LinkedHashSet}

import hkmc2.utils.*, shorthands.*


trait Publisher[A]:
  private[hkmc2] val shapeListeners: Buffer[A => Unit] = Buffer.empty

trait Host[A] extends Publisher[A]:
  private[hkmc2] val shapes: LinkedHashSet[A] = LinkedHashSet.empty
  def showDbg(using DebugPrinter): Str


