package hkmc2

import hkmc2.utils.*, shorthands.*

opaque type Uid[T] = Int

object Uid:
  class Handler[T]:
    class State:
      private var curUid = -1
      def nextUid: Uid[T] =
        curUid += 1
        curUid
      def reset = curUid = -1
  object Symbol extends Handler[semantics.Symbol]
  object Result extends Handler[codegen.Result]
  object StratVar extends Handler[codegen.flowAnalysis.StratVar]

extension [T] (x: Uid[T])
  def <=(rhs: Uid[T]) = x <= rhs
  def asInt: Int = x

private val ord = Ordering.Int
given [A]: Ordering[Uid[A]] = ord

