package hkmc2
package semantics

import sourcecode.{FileName, Line, Name}

package object ucs:
  def error(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(WarningReport(msgs.toList))
end ucs
