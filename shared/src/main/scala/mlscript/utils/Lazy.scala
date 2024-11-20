package mlscript.utils

import shorthands._

abstract class Box[+A] {
  def get: Opt[A]
  def get_! : A
  def isComputing: Bool
}

class Eager[+A](val value: A) extends Box[A] {
  def isComputing = false
  lazy val get = S(value)
  def get_! = value
}

class Lazy[A](thunk: => A) extends Box[A] {
  def isComputing = _isComputing
  private var _isComputing = false
  private var _value: Opt[A] = N
  def get = if (_isComputing) N else S(get_!)
  def get_! = {
    assert(!_isComputing)
    _compute
  }
  private def _compute = {
    _isComputing = true
    try {
      val v = thunk
      _value = S(v)
      v
    } finally {
      _isComputing = false
    }
  }
}
