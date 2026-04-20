package hkmc2
package codegen
package flowAnalysis

import scala.collection.mutable.{Set as MutSet}

object FlowWebComputation:
  case class Result[P, C](markedProducers: collection.Set[P], markedConsumers: collection.Set[C])

  def apply[P, C](
    dests: P => IterableOnce[C],
    srcs: C => IterableOnce[P],
    producerRoots: IterableOnce[P],
    consumerRoots: IterableOnce[C],
  ): Result[P, C] =
    val markedProducers = MutSet.empty[P]
    val markedConsumers = MutSet.empty[C]
    def markProducer(p: P): Unit =
      if markedProducers.add(p) then dests(p).iterator.foreach(markConsumer)
    def markConsumer(c: C): Unit =
      if markedConsumers.add(c) then srcs(c).iterator.foreach(markProducer)
    producerRoots.iterator.foreach(markProducer)
    consumerRoots.iterator.foreach(markConsumer)
    Result(markedProducers, markedConsumers)
