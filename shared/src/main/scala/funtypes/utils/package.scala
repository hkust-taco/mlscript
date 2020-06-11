package funtypes

import utils.shorthands._
import scala.collection.mutable

package object utils {

  import scala.collection.mutable
  import scala.collection.immutable.SortedMap
  
  @SuppressWarnings(Array(
    "org.wartremover.warts.Equals",
    "org.wartremover.warts.AsInstanceOf"))
  implicit final class AnyOps[A](self: A) {
    def ===(other: A): Boolean = self == other
    def =/=(other: A): Boolean = self != other
    def is(other: AnyRef): Boolean = self.asInstanceOf[AnyRef] eq other
    def isnt(other: AnyRef): Boolean = !(self.asInstanceOf[AnyRef] eq other)
    /** An alternative to === when in ScalaTest, which shadows our === */
    def =:=(other: A): Boolean = self == other
  }
  
  implicit class StringOps(private val self: String) extends AnyVal {
    import collection.mutable
    def splitSane(sep: Char): mutable.ArrayBuffer[Str] = {
      val buf = mutable.ArrayBuffer(new StringBuilder)
      self.foreach { c => if (c === sep) buf += new StringBuilder else buf.last append c; () }
      buf.map(_.toString)
    }
    def mapLines(f: String => String): String = splitSane('\n') map f mkString "\n"
    def indent(pre: String): String = mapLines(pre + _)
    def indent: String = indent("\t")
    def truncate(maxChars: Int, replace: String): String = {
      val newStr = self.take(maxChars)
      if (newStr.length < self.length) newStr + replace
      else newStr
    }
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
  
  
  implicit final class PafHelper[A,B](private val self: Paf[A,B]) extends AnyVal {
    // def appOrElse[C](arg: A)(els: A => )
    def appOrElse[A1 <: A, B1 >: B](x: A1)(default: A1 => B1): B1 =
      self.applyOrElse(x, default)
  }
  implicit final class GenHelper[A](private val self: A) extends AnyVal {
    
    @inline def into [B] (rhs: A => B): B = rhs(self)
    
    @inline def |> [B] (rhs: A => B): B = rhs(self)
    @inline def |>? [B] (rhs: PartialFunction[A, B]): Option[B] =
      rhs.andThen(some).appOrElse(self)(_ => none)
    @inline def |>?? [B] (rhs: PartialFunction[A, Option[B]]): Option[B] =
      rhs.appOrElse(self)(_ => none)
    @inline def |>! [B] (rhs: PartialFunction[A, B]): B = rhs(self)
    
    /** Like |> but expects the function to return the same type */
    @inline def |>= (rhs: A => A): A = rhs(self)
    @inline def |>=? (rhs: PartialFunction[A, A]): A =
      rhs.appOrElse(self)(_ => self)
    
    /** A lesser precedence one! */
    @inline def /> [B] (rhs: A => B): B = rhs(self)
    
    /** 
     * A helper to write left-associative applications, mainly used to get rid of paren hell
     * Example:
     *   println(Id(Sym(f(chars))))
     *   println(Id <|: Sym.apply <|: f <|: chars)  // `Sym` needs `.apply` because it's overloaded
     */
    @inline def <|: [B] (lhs: A => B): B = lhs(self)
    
    def withTypeOf[T >: A](x: T): T = self: T
    
  }
  
  implicit final class LazyGenHelper[A](self: => A) {
    
    @inline def optionIf(cond: Bool): Option[A] = if (cond) Some(self) else None
    @inline def optionIf(cond: A => Bool): Option[A] = if (cond(self)) Some(self) else None
    
    @inline def optionUnless(cond: Bool): Option[A] = if (!cond) Some(self) else None
    @inline def optionUnless(cond: A => Bool): Option[A] = if (!cond(self)) Some(self) else None
    
  }
  
  def die: Nothing = lastWords("Program reached and unexpected state.")
  def lastWords(msg: String): Nothing = throw new Exception(s"Internal Error: $msg")
  
  /** To make Scala unexhaustivity warnings believed to be spurious go away,
   * while clearly indicating the intent. */
  def spuriousWarning: Nothing = lastWords("Case was reached that was thought to be unreachable.")
  
  def checkless[A, B](pf: Paf[A, B]): A => B = pf
  
}
