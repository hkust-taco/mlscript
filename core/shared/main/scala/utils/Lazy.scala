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

object Lazy {
  def apply[A](thunk: => A): Lazy[A] = new Lazy[A] {
    def compute: A = thunk
  }
}

abstract class Lazy[A] extends Box[A] {
  protected def compute: A
  def isComputing = _isComputing
  def isEmpty: Bool = _value.isEmpty
  private var _isComputing = false
  private var _value: Opt[A] = N
  def get = if (_isComputing) N else S(get_!)
  def get_! = {
    assert(!_isComputing)
    _value.getOrElse(_compute)
  }
  private def _compute = {
    _isComputing = true
    try {
      val v = compute
      _value = S(v)
      v
    } finally {
      _isComputing = false
    }
  }
}
