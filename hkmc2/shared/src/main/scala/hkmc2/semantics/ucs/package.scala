package hkmc2
package semantics

package object ucs:
  def error(msgs: (Message, Option[Loc])*)(using Raise): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(msgs: (Message, Option[Loc])*)(using Raise): Unit =
    raise(WarningReport(msgs.toList))
end ucs
