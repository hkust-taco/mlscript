package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import js.JSConverters._

abstract class TSAny(v: js.Dynamic) {
  val isUndefined: Boolean = IsUndefined(v)
}

object IsUndefined {
  def apply(v: js.Dynamic): Boolean = js.isUndefined(v)
}

// array for information object in tsc
abstract class TSArray[T <: TSAny](arr: js.Dynamic) extends TSAny(arr) {
  def get(index: Int): T = ???
  lazy val length: Int = arr.length.asInstanceOf[Int]

  def foldLeft[U](init: U, index: Int = 0)(implicit f: (U, T) => U): U =
    if (!isUndefined && index < length) foldLeft(f(init, get(index)), index + 1)
    else init

  def foldLeftIndexed[U](init: U, index: Int = 0)(implicit f: (U, T, Int) => U): U =
    if (!isUndefined && index < length) foldLeftIndexed(f(init, get(index), index), index + 1)
    else init

  def foreach(f: T => Unit, index: Int = 0): Unit =
    if (!isUndefined && index < length) {
      f(get(index))
      foreach(f, index + 1)
    }
}

class TSNodeArray(arr: js.Dynamic)(implicit checker: TSTypeChecker) extends TSArray[TSNodeObject](arr) {
  override def get(index: Int) = TSNodeObject(arr.selectDynamic(index.toString))
}

object TSNodeArray {
  def apply(arr: js.Dynamic)(implicit checker: TSTypeChecker) = new TSNodeArray(arr)
}

class TSSymbolArray(arr: js.Dynamic)(implicit checker: TSTypeChecker) extends TSArray[TSSymbolObject](arr) {
  override def get(index: Int) = TSSymbolObject(arr.selectDynamic(index.toString))
}

object TSSymbolArray {
  def apply(arr: js.Dynamic)(implicit checker: TSTypeChecker) = new TSSymbolArray(arr)
}

class TSTokenArray(arr: js.Dynamic)(implicit checker: TSTypeChecker) extends TSArray[TSTokenObject](arr) {
  override def get(index: Int) = TSTokenObject(arr.selectDynamic(index.toString))
}

object TSTokenArray {
  def apply(arr: js.Dynamic)(implicit checker: TSTypeChecker) = new TSTokenArray(arr)
}

class TSTypeArray(arr: js.Dynamic)(implicit checker: TSTypeChecker) extends TSArray[TSTypeObject](arr) {
  override def get(index: Int) = TSTypeObject(arr.selectDynamic(index.toString))
}

object TSTypeArray {
  def apply(arr: js.Dynamic)(implicit checker: TSTypeChecker) = new TSTypeArray(arr)
}

class TSSymbolMap(map: js.Dynamic)(implicit checker: TSTypeChecker) extends TSAny(map) {
  def foreach(f: TSSymbolObject => Unit): Unit =
    if (!isUndefined)
      map.forEach({(s: js.Dynamic) => f(TSSymbolObject(s))})
}

object TSSymbolMap {
  def apply(map: js.Dynamic)(implicit checker: TSTypeChecker) = new TSSymbolMap(map)
}