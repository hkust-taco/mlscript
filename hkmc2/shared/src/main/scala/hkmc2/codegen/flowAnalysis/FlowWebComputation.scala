package hkmc2
package codegen
package flowAnalysis

import scala.collection.mutable.{Set as MutSet}

object FlowWebComputation:
  case class Result[P, C](markedProducers: collection.Set[P], markedConsumers: collection.Set[C])

  def apply[P, C](
    // marking a producer marks the consumers it flows to
    dests: P => IterableOnce[C],
    // marking a consumer marks the producers flowing into it
    srcs: C => IterableOnce[P],
    // marking a producer also marks these, which no consumer links to it
    impliedProducers: P => IterableOnce[P],
    producerRoots: IterableOnce[P],
    consumerRoots: IterableOnce[C],
  ): Result[P, C] =
    val markedProducers = MutSet.empty[P]
    val markedConsumers = MutSet.empty[C]
    def markProducer(p: P): Unit =
      if markedProducers.add(p) then
        dests(p).iterator.foreach(markConsumer)
        impliedProducers(p).iterator.foreach(markProducer)
    def markConsumer(c: C): Unit =
      if markedConsumers.add(c) then srcs(c).iterator.foreach(markProducer)
    producerRoots.iterator.foreach(markProducer)
    consumerRoots.iterator.foreach(markConsumer)
    Result(markedProducers, markedConsumers)
