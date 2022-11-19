package mlscript.compiler.mono.specializer

import mlscript.compiler.Expr
import mlscript.compiler.debug.{DebugOutput, Printable}
import scala.collection.immutable.HashMap

class Context(private val entries: HashMap[String, Expr]) extends Printable:
  def this(entries: IterableOnce[(String, Expr)]) = this(HashMap.from(entries))
  inline def get(name: String): Option[Expr] = entries.get(name)
  inline def +(entry: (String, Expr)): Context = Context(entries + entry)
  inline def isEmpty: Boolean = entries.isEmpty
  def getDebugOutput: DebugOutput =
    DebugOutput.Map(entries.iterator.map {
      (key, value) => (key, value.toString)
    }.toList)
