package hkmc2
package semantics

import mlscript.utils.*, shorthands.*, syntax.*

enum SimpleSplit extends AutoLocated with ProductWithTail:
  case Cons(branch: SimpleSplit.Head, tail: SimpleSplit)
  case Else(default: Term)
  case End
  
  inline def ~:(head: SimpleSplit.Head): Cons = Cons(head, this)
  
  def ~~:(front: SimpleSplit): SimpleSplit =
    front match
      case Cons(head, tail) => Cons(head, tail ~~: this)
      case Else(default) => Else(default)
      case End => this
  
  lazy val hasElse: Bool = this match
    case Cons(_, tail) => tail.hasElse
    case Else(_) => true
    case End => false
  
  protected def children: List[Located] = this match
    case Cons(branch, tail) => List(branch, tail)
    case Else(default) => List(default)
    case End => Nil
  
  def prettyPrint: Str = SimpleSplit.prettyPrint(this)

object SimpleSplit:
  /** Note: The order of the given `heads` must be reversed: later branches
    * should come earlier in the list. */
  def apply(heads: Ls[Head], default: Opt[Term]): SimpleSplit =
    heads.foldLeft(default.fold(End)(Else(_))):
      case (tail, head) => Cons(head, tail)
  
  /** Represents a single branch of a simple split. */
  enum Head extends AutoLocated:
    case Match(scrutinee: Term.Ref, pattern: Pattern, consequent: SimpleSplit)
    case Let(binding: BlockLocalSymbol, term: Term)
    
    protected def children: List[Located] = this match
      case Match(scrutinee, pattern, consequent) =>
        List(scrutinee, pattern, consequent)
      case Let(binding, term) => List(binding, term)
  
  private object prettyPrint:
    /** Represents lines with indentations. */
    type Lines = Ls[(Int, Str)]
    
    extension (lines: Lines)
      /** Increase the indentation of all lines by one. */
      def indent: Lines = lines.map:
        case (n, line) => (n + 1, line)
    
      /** Make a multi-line string. */
      def toIndentedString: Str = lines.iterator.map:
        case (n, line) => "  " * n + line
      .mkString("\n")
    
    extension (prefix: String)
      /**
        * If the first line does not have indentation and the remaining lines are
        * indented, prepend the given string to the first line. Otherwise, prepend
        * the given string to the first line and indent all remaining lines.
        *
        * When you want to amend the title of lines, you should use this function.
        */
      def #:(lines: Lines): Lines = lines match
        case all @ ((0, line) :: lines) if lines.forall(_._1 > 0) =>
          if prefix.isEmpty then all else (0, s"$prefix $line") :: lines
        case lines => (0, prefix) :: lines.indent
    
    inline def apply(s: SimpleSplit): Str = showSplit("if", s)
    
    private def showSplit(prefix: Str, s: SimpleSplit): Str =
      /** Show a split as a list of lines.
       *  @param isFirst whether this is the first and frontmost branch
       *  @param isTopLevel whether this is the top-level split
       */
      def split(s: SimpleSplit, isFirst: Bool, isTopLevel: Bool): Lines = s match
        case SimpleSplit.Cons(head: Head.Match, tail) => (branch(head, isTopLevel) match
          case (n, line) :: tail => (n, line) :: tail
          case Nil => Nil
        ) ::: split(tail, false, isTopLevel)
        case SimpleSplit.Cons(Head.Let(nme, rhs), tail) =>
          (0, s"let $nme = ${rhs.showDbg}") :: split(tail, false, true)
        case SimpleSplit.Else(t) =>
          (if isFirst && !isTopLevel then "" else "else") #: term(t)
        case SimpleSplit.End => Nil
      def term(t: Statement): Lines = t match
        // case Term.Blk(stmts, term) =>
        //   stmts.iterator.concat(Iterator.single(term)).flatMap:
        //     case DefineVar(sym, Term.IfLike(Keyword.`if`, splt)) =>
        //       s"$sym = if" #: split(splt, true, true)
        //     case stmt => (0, stmt.showDbg) :: Nil
        //   .toList
        case t: Statement => (0, t.showDbg) :: Nil
      def branch(b: Head.Match, isTopLevel: Bool): Lines =
        val Head.Match(scrutinee, pattern, consequent) = b
        val lines = split(consequent, true, false)
        val prefix = s"${scrutinee.sym} is ${pattern.showDbg}"
        consequent match
          case SimpleSplit.Else(_) => (prefix + " then") #: lines
          case _ => (prefix + " and") #: lines
      val lines = split(s, true, true)
      (if prefix.isEmpty then lines else prefix #: lines).toIndentedString
  
  end prettyPrint

