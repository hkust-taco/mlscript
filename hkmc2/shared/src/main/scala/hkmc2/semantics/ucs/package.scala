package hkmc2
package semantics

import sourcecode.{Name, Line, FileName}

package object ucs:
  def error(using Line, FileName)(msgs: (Message, Option[Loc])*)(using Raise)(using Name): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(using Line, FileName)(msgs: (Message, Option[Loc])*)(using Raise)(using Name): Unit =
    raise(WarningReport(msgs.toList))
end ucs
