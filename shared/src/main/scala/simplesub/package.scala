package object simplesub {

  import scala.collection.mutable
  import scala.collection.immutable.SortedMap
  
  @SuppressWarnings(Array(
    "org.wartremover.warts.Equals",
    "org.wartremover.warts.AsInstanceOf"))
  implicit final class AnyOps[A](self: A) {
    def ===(other: A): Boolean = self == other
    def =/=(other: A): Boolean = self != other
    def is(other: AnyRef): Boolean = self.asInstanceOf[AnyRef] eq other
    /** An alternative to === when in ScalaTest, which shadows our === */
    def =:=(other: A): Boolean = self == other
  }
  
  implicit class IterableOps[A](private val self: IterableOnce[A]) extends AnyVal {
    def mkStringOr(
      sep: String = "", start: String = "", end: String = "", els: String = ""
    ): String =
      if (self.iterator.nonEmpty) self.iterator.mkString(start, sep, end) else els
  }
  
  def mergeOptions[A](lhs: Option[A], rhs: Option[A])(f: (A, A) => A): Option[A] = (lhs, rhs) match {
    case (Some(l), Some(r)) => Some(f(l, r))
    case (lhs @ Some(_), _) => lhs
    case (_, rhs @ Some(_)) => rhs
    case (None, None) => None
  }
  
  def mergeMap[A, B](lhs: Iterable[(A, B)], rhs: Iterable[(A, B)])(f: (B, B) => B): Map[A,B] =
    new mutable.ArrayBuffer(lhs.knownSize + rhs.knownSize max 8)
      .addAll(lhs).addAll(rhs).groupMapReduce(_._1)(_._2)(f)
  
  def mergeSortedMap[A: Ordering, B](lhs: Iterable[(A, B)], rhs: Iterable[(A, B)])(f: (B, B) => B): SortedMap[A,B] =
    SortedMap.from(mergeMap(lhs, rhs)(f))
  
}
