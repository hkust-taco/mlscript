package hkmc2.codegen.llir

import collection.mutable.{HashMap => MutHMap}
import mlscript.utils.shorthands._

final class Fresh(div : Char = '$'):
  private val counter = MutHMap[Str, Int]()
  private def gensym(s: Str) = {
    val n = s.lastIndexOf(div)
    val (ts, suffix) = s.splitAt(if n == -1 then s.length() else n)
    var x = if suffix.stripPrefix(div.toString).forall(_.isDigit) then ts else s
    val count = counter.getOrElse(x, 0)
    val tmp = s"$x$div$count"
    counter.update(x, count + 1)
    Name(tmp)
  }

  def make(s: Str) = gensym(s)
  def make = gensym("x")

final class FreshInt:
  private var counter = 0
  def make: Int = {
    val tmp = counter
    counter += 1
    tmp
  }

