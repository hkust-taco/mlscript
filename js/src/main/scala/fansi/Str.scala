// Temporary shims since fansi doesn't seem to be released for this Scala version yet

package fansi

import scala.language.implicitConversions

class Str(underlying: CharSequence) {
  def plainText(): String = s"$underlying"
  override def toString(): String = s"$underlying"
}
object Str {
  implicit def implicitApply(x: CharSequence): Str = new Str(x)
  def join(args: Str*): Str = args.foldLeft("")(_ ++ _.plainText())
}
