package mlscript.utils

import scala.annotation.showAsInfix
import scala.util.chaining._

object shorthands {
  
  /** We have Int instead of Integer; why not Bool instead of Boolean? */
  type Bool = Boolean
  
  /** Dotty syntax for intersection types */
  @showAsInfix
  type & [+A,+B] = A with B
  
  type Ls[+A] = List[A]
  val Ls: List.type = List
  
  type Str = String
  type FStr = fansi.Str
  // val FStr: fansi.Str.type = fansi.Str // do not include this in the JS!
  
  type Ite[+A] = Iterator[A]
  val Ite: Iterator.type = Iterator
  
  type Opt[+A] = Option[A]
  val Opt: Option.type = Option
  type S[+A] = Some[A]
  val S: Some.type = Some
  val N: None.type = None
  def some[A]: A => Option[A] = Some(_)
  def none[A]: Option[A] = None
  
  type Paf[-A,+B] = PartialFunction[A,B]
  
  type Exc = Exception
  type Err = Error
  
  type Ord[A] = Ordering[A]
  type Num[A] = Numeric[A]
  
  type \/[+A, +B] = Either[A, B]
  val \/ : Either.type = Either
  
  type L[+A] = Left[A, Nothing]
  val L: Left.type = Left
  
  type R[+B] = Right[Nothing, B]
  val R: Right.type = Right
  
  @showAsInfix
  type -> [+A,+B] = (A,B)
  object -> {
    def unapply[A, B](ab: (A, B)): Some[(A, B)] = Some(ab)
  }
  implicit class Tuple2Helper[A,B](private val self: (A,B)) extends AnyVal {
    @inline def mapFirst[C](f: A => C): (C,B) = (self._1 pipe f, self._2)
    @inline def mapSecond[C](f: B => C): (A,C) = (self._1, self._2 pipe f)
  }
  
}
