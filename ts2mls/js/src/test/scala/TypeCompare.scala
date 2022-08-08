import ts2mls.types._

object TypeCompare {
  def apply(t: TSType, s: String): Boolean = t.toString.equals(s)
}
