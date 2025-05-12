package hkmc2
package semantics

import sourcecode.{Name, Line, FileName}

package object ucs:
  def error(using Raise, Line, Name, FileName)(msgs: (Message, Option[Loc])*): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(using Raise, Line, Name, FileName)(msgs: (Message, Option[Loc])*): Unit =
    raise(WarningReport(msgs.toList))
end ucs
