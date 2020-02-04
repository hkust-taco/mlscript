package object simplesub {
  
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
  
  def mergeMaps[A,B](lhs: Map[A,B], rhs: Map[A,B])(f: (B, B) => B): Map[A,B] = {
    (lhs.iterator ++ rhs.iterator).toList.groupBy(_._1).map {
      case (k,(_,a)::Nil) => k -> a
      case (k,(_,a)::(_,b)::Nil) => k -> f(a,b)
      case _ => throw new AssertionError
    }
  }
  
}
