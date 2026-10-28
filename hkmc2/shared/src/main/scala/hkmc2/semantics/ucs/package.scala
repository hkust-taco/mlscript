package hkmc2
package semantics

import sourcecode.{FileName, Line, Name}
import syntax.{Keyword, Tree}, Tree.{Ident, InfixApp, Keywrd, Sel}
import hkmc2.utils.*, shorthands.*

package object ucs:
  def error(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(WarningReport(msgs.toList))
  
  def bug(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(InternalError(msgs.toList))
  
  extension (symbol: SimpleRefSymbol)
    def safeRef(using Elaborator.State): Term.SimpleRef = Term.SimpleRef(symbol)(N)
  
  extension (op: Keyword.Infix)
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case InfixApp(lhs, Keywrd(`op`), rhs) => S((lhs, rhs))
      case _ => N
  
  // TOOD: rm
  type Ctor = Sel | Ident
  
  /** A helper extractor for matching the tree of `x | y`. */  
  object extractors:
    import Tree.OpApp
    
    /** A helper extractor for matching the tree of `x ..= y` and `x ..< y`.
     *  The Boolean value indicates whether the range is inclusive.
     */
    object to:
      infix def unapply(tree: Tree): Opt[(Tree, (Bool, Tree))] = tree match
        case OpApp(lhs, Ident("..="), rhs :: Nil) => S(lhs, (true, rhs))
        case OpApp(lhs, Ident("..<"), rhs :: Nil) => S(lhs, (false, rhs))
        case _ => N
end ucs
