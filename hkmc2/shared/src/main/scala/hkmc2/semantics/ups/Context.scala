package hkmc2
package semantics
package ups

import mlscript.utils.*, shorthands.*
import Pattern.{Instantiation, Never}
import Message.MessageContext, ucs.bug
import sourcecode.{FileName, Line, Name}

/** Before pattern compilation, we monomorphize higher-order patterns into
  * first-order patterns. `Context` records the correspondence between each
  * `Pattern.Instantiation` and the resulting `Pat` after monomorphization,
  * to avoid redundant work.
  */
class Context(val definitions: Map[Pattern.Instantiation, Pat]):
  def get(instantiation: Instantiation)(using Raise): Pat =
    definitions.get(instantiation) match
      case Some(pattern) => pattern
      case None =>
        bug(msg"The pattern is not instantiated." -> instantiation.toLoc)
        Never

object Context:
  extension (instantiation: Instantiation)
    /** Get the body of the instantiated pattern definition. */
    def body(using Context, Raise): Pat = summon[Context].get(instantiation)
