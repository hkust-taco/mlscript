package mlscript.utils

import shorthands.*

enum EitherOrBoth[+A, +B]:
  case First[+A](value: A) extends EitherOrBoth[A, Nothing]
  case Second[+B](value: B) extends EitherOrBoth[Nothing, B]
  case Both[+A, +B](firstValue: A, secondValue: B) extends EitherOrBoth[A, B]
  
  def first: Opt[A] = this `|>?` :
    case First(v) => v
    case Both(v, _) => v
  def second: Opt[B] = this `|>?` :
    case Second(v) => v
    case Both(_, v) => v
  def options: (Opt[A], Opt[B]) = (first, second)
  
  def fold[R](f: A => R)(g: B => R)(h: (A, B) => R): R = this match
    case First(v) => f(v)
    case Second(v) => g(v)
    case Both(a, b) => h(a, b)
  
  def reduce[R](f: A => R)(g: B => R)(h: (R, R) => R): R =
    fold(f)(g)((x, y) => h(f(x), g(y)))
  
  def merge[R](f: (A | B) => R)(h: (R, R) => R): R =
    reduce(f)(f)(h)
  
end EitherOrBoth
export EitherOrBoth.{ First, Second, Both }

