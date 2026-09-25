package hkmc2
package utils

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet}

import hkmc2.utils.*, shorthands.*
import hkmc2.semantics.{NewResolverState, Symbol}


type ShapeListener[-A] = A => NewResolverState ?=> Unit

object Publisher:
  private[hkmc2] final class Data[A]:
    private[hkmc2] var owner: NewResolverState | Null = null
    private[hkmc2] var completed = false
    val listeners: ArrayBuffer[ShapeListener[A]] = ArrayBuffer.empty
    val shapes: LinkedHashSet[A] = LinkedHashSet.empty
    // Pass-local observers never become part of a copied inference graph.
    private val observers: ArrayBuffer[ShapeListener[A]] = ArrayBuffer.empty
    def observe(listener: ShapeListener[A])(using state: NewResolverState): () => Unit =
      val data = state.local(this)
      data.observers += listener
      data.replay(listener)
      () => { data.observers -= listener; () }
    def copy(state: NewResolverState): Data[A] =
      val result = new Data[A]
      result.owner = state
      // Preserve intermediate exporters' private graph nodes as well as the
      // listener's original registration graph when this host is re-exported.
      val origin = owner
      listeners.foreach: listener =>
        result.listeners += (shape => (current: NewResolverState) ?=>
          listener(shape)(using if origin == null then current else current.inGraph(origin)))
      result.shapes ++= shapes
      result

    def publish(shape: A)(using state: NewResolverState): Unit =
      val data = state.local(this)
      if data.shapes.add(shape) then data.notify(shape)
    def notify(shape: A)(using NewResolverState): Unit =
      // Appended listeners receive this candidate through replay.
      val count = listeners.size
      val observerCount = observers.size
      var i = 0
      while i < count do
        listeners(i)(shape)
        i += 1
      i = 0
      while i < observerCount do
        observers(i)(shape)
        i += 1
    def addListener(listener: ShapeListener[A])(using origin: NewResolverState): Unit =
      origin.local(this).listeners +=
        (shape => (current: NewResolverState) ?=> listener(shape)(using current.inGraph(origin)))
    def replay(listener: ShapeListener[A])(using state: NewResolverState): Unit =
      val candidates = state.local(this).shapes
      // Apply the contextual listener, rather than discard a contextual thunk.
      candidates.iterator.take(candidates.size).foreach[Unit](shape => listener(shape))
    def subscribe(listener: ShapeListener[A])(using NewResolverState): Unit =
      addListener(listener)
      replay(listener)

trait Publisher[A]:
  private[hkmc2] val originalData = new Publisher.Data[A]
  // Syntax nodes do not all carry an elaborator owner. Bind their original host
  // on first use; subsequent consumers only mutate copies in their own state.
  private[hkmc2] def initialData(state: NewResolverState): Publisher.Data[A] =
    val foreignSymbol = this match
      case symbol: Symbol => !state.isOwnedSym(symbol)
      case _ => false
    if originalData.owner == null && !foreignSymbol then originalData.owner = state
    originalData

  private[hkmc2] def isOwnedBy(state: NewResolverState): Bool =
    originalData.owner eq state

  private[hkmc2] def shapeListeners: ArrayBuffer[ShapeListener[A]] = originalData.listeners
  private[hkmc2] def inferenceHost(using state: NewResolverState): Publisher.Data[A] = state.data(this)
  private[hkmc2] def addShapeListener(listener: ShapeListener[A])(using origin: NewResolverState): Unit =
    inferenceHost.addListener(listener)

  private[hkmc2] def currentShapes(using state: NewResolverState): LinkedHashSet[A] =
    state.data(this).shapes
  private[hkmc2] def shapes: LinkedHashSet[A] = originalData.shapes

  private[hkmc2] def notifyShapeListeners(shape: A)(using NewResolverState): Unit =
    inferenceHost.notify(shape)

trait Host[A] extends Publisher[A]:
  private[hkmc2] def subscribeToShapes(listener: ShapeListener[A])(using NewResolverState): Unit =
    addShapeListener(listener)
    replayShapes(listener)
  private[hkmc2] def replayShapes(listener: ShapeListener[A])(using NewResolverState): Unit =
    inferenceHost.replay(listener)
  def showDbg(using DebugPrinter): Str


