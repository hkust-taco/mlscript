package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
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
    if (isUndefined) init
    else if (index < length) foldLeft(f(init, get(index)), index + 1)
    else init

  def foldLeftIndexed[U](init: U, index: Int = 0)(implicit f: (U, T, Int) => U): U =
    if (isUndefined) init
    else if (index < length) foldLeftIndexed(f(init, get(index), index), index + 1)
    else init

  def foreach(f: T => Unit, index: Int = 0): Unit =
    if (!isUndefined)
      if (index < length) {
        f(get(index))
        foreach(f, index + 1)
      }
}

class TSNodeArray(arr: js.Dynamic) extends TSArray[TSNodeObject](arr) {
  override def get(index: Int) = TSNodeObject(arr.selectDynamic(index.toString))
}

object TSNodeArray {
  def apply(arr: js.Dynamic) = new TSNodeArray(arr)
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

class TSSymbolMap(map: js.Dynamic) extends TSAny(map) {
  def foreach(f: TSSymbolObject => Unit): Unit =
    if (!isUndefined) {
      val jsf: js.Function1[js.Dynamic, js.Any] =
        { (s: js.Dynamic) => f(TSSymbolObject(s)) }
      map.forEach(jsf)
    }
}

object TSSymbolMap {
  def apply(map: js.Dynamic) = new TSSymbolMap(map)
}