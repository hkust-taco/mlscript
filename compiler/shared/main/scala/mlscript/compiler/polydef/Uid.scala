package mlscript
package compiler
package polydef

opaque type Uid[T] = Int

object Uid:
  class Handler[T]:
    class State:
      private val uidStore = scala.collection.mutable.Map.empty[String, Uid[T]]
      def nextUid: Uid[T] = nextUid("")
      def nextUid(key: String): Uid[T] =
        uidStore.updateWith(key) {
          case None => Some(0)
          case Some(v) => Some(v + 1)
        }.get
  object TypeVar extends Handler[TypeVar]
  object Ident extends Handler[Ident]
  object Expr extends Handler[Expr]