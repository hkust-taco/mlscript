package mlscript.ucs

import mlscript.{Diagnostic, Loc, Message, Typer}
import mlscript.utils.shorthands._

class DesugaringException(messages: Ls[Message -> Opt[Loc]]) extends Throwable {
  def this(message: Message, location: Opt[Loc]) = this(message -> location :: Nil)
  def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType = {
    typer.err(messages)
  }
}
