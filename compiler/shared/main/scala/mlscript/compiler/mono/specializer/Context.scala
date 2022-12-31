package mlscript.compiler.mono.specializer

import mlscript.compiler.Expr
import mlscript.compiler.debug.{DebugOutput, Printable}
import mlscript.compiler.mono.specializer.BoundedExpr

class Context(private val entries: Map[String, BoundedExpr]) extends Printable:
  def this() = this(Map("true" -> BoundedExpr(LiteralValue(true)), "false" -> BoundedExpr(LiteralValue(false))))
  inline def get(name: String): BoundedExpr = entries.get(name).getOrElse(BoundedExpr(UnknownValue()))
  inline def +(entry: (String, BoundedExpr)): Context = Context(entries + entry)
  inline def ++(other: Context): Context = Context(entries ++ other.entries)
  inline def ++(other: IterableOnce[(String, BoundedExpr)]) = Context(entries ++ other)
  inline def isEmpty: Boolean = entries.isEmpty
  inline def contains(name: String): Boolean = entries.contains(name)
  def getDebugOutput: DebugOutput =
    DebugOutput.Map(entries.iterator.map {
      (key, value) => (key, value.toString)
    }.toList)
object Context{
  def toCtx(entries: IterableOnce[(String, BoundedExpr)]) = Context(Map.from(entries))
}