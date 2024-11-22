package mlscript
package pretyper

import scala.collection.mutable.Buffer
import Diagnostic.Source, Message.MessageContext
import mlscript.utils._, shorthands._

/**
  * A trait containing a mutable buffer of diagnostics.
  */
trait Diagnosable {
  private val diagnosticBuffer = Buffer.empty[Diagnostic]
  
  protected def raise(diagnostics: Diagnostic): Unit =
    diagnosticBuffer += diagnostics

  protected def raiseMany(diagnostics: IterableOnce[Diagnostic]): Unit =
    diagnosticBuffer ++= diagnostics

  protected def raiseError(source: Source, messages: (Message -> Opt[Loc])*): Unit =
    raise(ErrorReport(messages.toList, newDefs = true, source))

  protected def raiseWarning(source: Source, messages: (Message -> Opt[Loc])*): Unit =
    raise(WarningReport(messages.toList, newDefs = true, source))

  @inline final def filterDiagnostics(f: Diagnostic => Bool): Ls[Diagnostic] =
    diagnosticBuffer.iterator.filter(f).toList

  @inline final def getDiagnostics: Ls[Diagnostic] = diagnosticBuffer.toList
}
