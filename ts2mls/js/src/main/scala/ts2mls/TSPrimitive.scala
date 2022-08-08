package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._

class TSAny(v: js.Dynamic) {
  lazy val isUndefined: Boolean = js.isUndefined(v)
}

abstract class TSArray[T <: TSAny](arr: js.Dynamic) extends TSAny(arr) {
  def get(index: Int): T = ???
  def empty(): Boolean = length() == 0
  def length(): Int = arr.length.asInstanceOf[Int]

  def foldLeft[U](init: U, index: Int = 0)(implicit f: (U, T) => U): U = {
    if (index < length) foldLeft(f(init, get(index)), index + 1)
    else init
  }
}

class TSNodeArray(arr: js.Dynamic) extends TSArray[TSNodeObject](arr) {

  override def get(index: Int) = TSNodeObject(arr.selectDynamic(index.toString))
}

object TSNodeArray {
  def apply(arr: js.Dynamic) = new TSNodeArray(arr)
}

class TSSymbolArray(arr: js.Dynamic) extends TSArray[TSSymbolObject](arr) {

  override def get(index: Int) = TSSymbolObject(arr.selectDynamic(index.toString))
}

object TSSymbolArray {
  def apply(arr: js.Dynamic) = new TSSymbolArray(arr)
}

class TSTokenArray(arr: js.Dynamic) extends TSArray[TSTokenObject](arr) {

  override def get(index: Int) = TSTokenObject(arr.selectDynamic(index.toString))
}

object TSTokenArray {
  def apply(arr: js.Dynamic) = new TSTokenArray(arr)
}

class TSTypeArray(arr: js.Dynamic) extends TSArray[TSTypeObject](arr) {

  override def get(index: Int) = TSTypeObject(arr.selectDynamic(index.toString))
}

object TSTypeArray {
  def apply(arr: js.Dynamic) = new TSTypeArray(arr)
}

abstract class TSIterator[T <: TSAny](it: js.Dynamic) extends TSAny(it) {
  protected var cur: js.Dynamic = it
  def next(): Unit = cur = it.next()
  def done(): Boolean = cur.done
  def value(): (String, T) = ???
}

class TSSymbolIter(it: js.Dynamic) extends TSIterator[TSSymbolObject](it) {
  override def value(): (String, TSSymbolObject) = {
    val data = cur.value
    (data.shift().toString, TSSymbolObject(data.shift()))
  }
}

object TSSymbolIter {
  def apply(it: js.Dynamic) = new TSSymbolIter(it)
}