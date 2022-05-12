package mlscript

import utils.shorthands._
import scala.collection.mutable

package object utils {

  import scala.collection.mutable
  import scala.collection.immutable.{SortedSet, SortedMap}
  
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
    def isCapitalized: Bool = self.nonEmpty && self.head.isUpper
    def decapitalize: String =
      if (self.length === 0 || !self.charAt(0).isUpper) self
      else self.updated(0, self.charAt(0).toLower)
  }
  
  implicit class IterableOps[A](private val self: IterableOnce[A]) extends AnyVal {
    def mkStringOr(
      sep: String = "", start: String = "", end: String = "", els: String = ""
    ): String =
      if (self.iterator.nonEmpty) self.iterator.mkString(start, sep, end) else els
    def collectLast[B](f: Paf[A, B]): Opt[B] = self.iterator.collect(f).foldLeft[Opt[B]](N)((_, a) => S(a))
    def toSortedSet(implicit ord: Ordering[A]): SortedSet[A] =
      SortedSet.from(self)
  }
  implicit class OptIterableOps[A](private val self: IterableOnce[Opt[A]]) extends AnyVal {
    def firstSome: Opt[A] = self.iterator.collectFirst { case Some(v) => v }
  }
  implicit class PairIterableOps[A, B](private val self: IterableOnce[A -> B]) extends AnyVal {
    def mapValues[C](f: B => C): List[A -> C] = mapValuesIter(f).toList
    def mapValuesIter[C](f: B => C): Iterator[A -> C] = self.iterator.map(p => p._1 -> f(p._2))
  }
  
  implicit class MapOps[A, B](private val self: Map[A, B]) extends AnyVal {
    def +++(that: Map[A, B]): Map[A, B] = {
      require(!self.keysIterator.exists(that.keySet), (self.keySet, that.keySet))
      self ++ that
    }
    def +++(that: Iterable[A -> B]): Map[A, B] = {
      val thatKeySet = that.iterator.map(_._1).toSet
      require(!self.keysIterator.exists(thatKeySet), (self.keySet, thatKeySet))
      self ++ that
    }
  }
  
  def mergeOptionsFlat[A](lhs: Option[A], rhs: Option[A])(f: (A, A) => Opt[A]): Option[A] = (lhs, rhs) match {
    case (Some(l), Some(r)) => f(l, r)
    case (lhs @ Some(_), _) => lhs
    case (_, rhs @ Some(_)) => rhs
    case (None, None) => None
  }
  def mergeOptions[A](lhs: Option[A], rhs: Option[A])(f: (A, A) => A): Option[A] =
    mergeOptionsFlat(lhs, rhs)(f(_, _) |> some)
  
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
  
  implicit final class ListHelpers[A](ls: Ls[A]) {
    def filterOutConsecutive(f: (A, A) => Bool): Ls[A] =
      ls.foldRight[List[A]](Nil) { case (x, xs) => if (xs.isEmpty || !f(xs.head, x)) x :: xs else xs }
    def tailOption: Opt[Ls[A]] = if (ls.isEmpty) N else S(ls.tail)
    def headOr(els: => A): A = if (ls.isEmpty) els else ls.head
    def tailOr(els: => Ls[A]): Ls[A] = if (ls.isEmpty) els else ls.tail
    def mapHead(f: A => A): Ls[A] = ls match {
      case h :: t => f(h) :: t
      case Nil => Nil
    }
  }
  
  implicit final class OptionHelpers[A](opt: Opt[A]) {
    def dlof[B](f: A => B)(b: => B): B = opt.fold(b)(f)
  }
  
  implicit class MutSetHelpers[A](self: mutable.Set[A]) {
    def setAndIfUnset(x: A)(thunk: => Unit): Unit = {
      if (!self.contains(x)) {
        self += x
        thunk
      }
    }
    def setAnd[R](x: A)(ifSet: => R)(ifUnset: => R): R = {
      if (self.contains(x)) ifSet else {
        self += x
        ifUnset
      }
    }
  }
  
  implicit class SetObjectHelpers(self: Set.type) {
    def single[A](a: A): Set[A] = (Set.newBuilder[A] += a).result()
  }
  implicit class SortedSetObjectHelpers(self: SortedSet.type) {
    def single[A: Ordering](a: A): SortedSet[A] = (SortedSet.newBuilder[A] += a).result()
  }
  implicit class MapObjectHelpers(self: Map.type) {
    def single[A, B](ab: A -> B): Map[A, B] = (Map.newBuilder[A, B] += ab).result()
  }
  implicit class SortedMapObjectHelpers(self: SortedMap.type) {
    def single[A: Ordering, B](ab: A -> B): SortedMap[A, B] = (SortedMap.newBuilder[A, B] += ab).result()
  }
  
  def die: Nothing = lastWords("Program reached and unexpected state.")
  def lastWords(msg: String): Nothing = throw new Exception(s"Internal Error: $msg")
  
  /** To make Scala unexhaustivity warnings believed to be spurious go away,
   * while clearly indicating the intent. */
  def spuriousWarning: Nothing = lastWords("Case was reached that was thought to be unreachable.")
  
  def checkless[A, B](pf: Paf[A, B]): A => B = pf
  
  
  def closeOver[A](xs: Set[A])(f: A => Set[A]): Set[A] =
    closeOverCached(Set.empty, xs)(f)
  def closeOverCached[A](done: Set[A], todo: Set[A])(f: A => Set[A]): Set[A] =
    if (todo.isEmpty) done else {
      val newDone = done ++ todo
      closeOverCached(newDone, todo.flatMap(f) -- newDone)(f)
    }
  
  
  object empty {
    def unapply(it: Iterable[Any]): Bool = it.isEmpty
  }
  
}
