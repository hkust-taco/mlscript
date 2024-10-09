package hkmc2
package document

import mlscript.utils.*, shorthands.*
import utils.*

import scala.annotation.implicitNotFound

/**
 * Describes how to lift objects using the `doc` string interpolation.
 */
@implicitNotFound("Cannot find document.Liftable implementation for type ${T}")
trait Liftable[-T] {
  def apply(value: T): Document
}

object Liftable {

  def apply[T](f: T => Document): Liftable[T] =
    new Liftable[T] { def apply(value: T): Document = f(value) }

}
