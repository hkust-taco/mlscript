package hkmc2.utils

import shorthands.*

abstract class Box[+A]:
  def force: Opt[A]
  def force_! : A
  def isComputing: Bool

class Eager[+A](val value: A) extends Box[A]:
  def isComputing = false
  lazy val force = S(value)
  def force_! = value

object Lazy:
  def apply[A](thunk: => A): Lazy[A] = new Lazy[A]:
    def compute: A = thunk

abstract class Lazy[A] extends Box[A]:
  protected def compute: A
  def isComputing = _isComputing
  def isEmpty: Bool = _value.isEmpty
  private var _isComputing = false
  private var _value: Opt[A] = N
  def force = if _isComputing then N else S(force_!)
  def force_! =
    assert(!_isComputing)
    _value.getOrElse(_compute)
  private def _compute =
    _isComputing = true
    try
      val v = compute
      _value = S(v)
      v
    finally
      _isComputing = false
