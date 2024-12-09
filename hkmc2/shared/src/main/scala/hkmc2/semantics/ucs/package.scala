package hkmc2
package semantics

package object ucs:
  private[ucs] def error(msgs: (Message, Option[Loc])*)(using Raise): Unit =
    raise(ErrorReport(msgs.toList))
  
  private[ucs] def warn(msgs: (Message, Option[Loc])*)(using Raise): Unit =
    raise(WarningReport(msgs.toList))
end ucs
