package hkmc2
package semantics

import sourcecode.{FileName, Line, Name}

package object ucs:
  def error(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(WarningReport(msgs.toList))
  
  extension (symbol: BlockLocalSymbol)
    /** Create a `Ref` that does not have any implicit arguments. We need this
     *  function because we generate a lot of `Ref`s after implicit resolution.
     *  Writing `.withIArgs(Nil)` is too verbose.
     */
    def safeRef: Term.Ref = symbol.ref().withIArgs(Nil)
end ucs
