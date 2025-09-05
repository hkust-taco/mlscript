package hkmc2
package semantics

import sourcecode.{FileName, Line, Name}

package object ucs:
  def error(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(ErrorReport(msgs.toList))
  
  def warn(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(WarningReport(msgs.toList))
  
  def bug(using Line, FileName, Name, Raise)(msgs: (Message, Option[Loc])*): Unit =
    raise(InternalError(msgs.toList))
  
  extension (symbol: Symbol)
    /** Create a `Ref` that does not have any implicit arguments. We need this
     *  function because we generate a lot of `Ref`s after implicit resolution.
     *  Writing `.resolve` is too verbose.
     */
    def safeRef: Term.Ref = symbol.ref().resolve
  
  /** A helper extractor for matching the tree of `x | y`. */  
  object extractors:
    import syntax.Tree, Tree.*
    import mlscript.utils.*, shorthands.*

    object or:
      infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
        case OpApp(lhs, Ident("|"), rhs :: Nil) => S(lhs, rhs)
        case _ => N
    
    /** A helper extractor for matching the tree of `x a y`.*/
    object and:
      infix def unapply(tree: App): Opt[(Tree, Tree)] = tree match
        case App(Ident("&"), Tup(lhs :: rhs :: Nil)) => S(lhs, rhs)
        case _ => N

    /** A helper extractor for matching the tree of `x ..= y` and `x ..< y`.
     *  The Boolean value indicates whether the range is inclusive.
     */
    object to:
      infix def unapply(tree: Tree): Opt[(Tree, (Bool, Tree))] = tree match
        case OpApp(lhs, Ident("..="), rhs :: Nil) => S(lhs, (true, rhs))
        case OpApp(lhs, Ident("..<"), rhs :: Nil) => S(lhs, (false, rhs))
        case _ => N
        
    object `~`:
      infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
        case OpApp(lhs, Ident("~"), rhs :: Nil) => S(lhs, rhs)
        case _ => N
end ucs
