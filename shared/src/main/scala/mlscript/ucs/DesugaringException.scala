package mlscript.ucs

import mlscript.{Diagnostic, Loc, Message, Typer}
import mlscript.utils.shorthands._

abstract class DesugaringException extends Throwable {
  def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType
}

object DesugaringException {
  final case class Single(message: Message, location: Opt[Loc]) extends DesugaringException {
    override def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType = {
      typer.err(message, location)
    }
  }
  final case class Multiple(messages: Ls[Message -> Opt[Loc]]) extends DesugaringException {
    override def report(typer: Typer)(implicit raise: Diagnostic => Unit): typer.SimpleType = {
      typer.err(messages)
    }
  }
}