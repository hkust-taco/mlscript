package hkmc2
package semantics

import mlscript.utils.*, shorthands.*, syntax.*, Tree.{BoolLit, Keywrd}
import Keyword.{`do`, `else`, `then`}, utils.TL, Elaborator.{Ctx, State}

/**
  * Similar to `Split` but contains nested patterns (i.e., class `Pattern`).
  */
enum SimpleSplit extends AutoLocated with ProductWithTail:
  import SimpleSplit.Head
  
  case Cons(branch: SimpleSplit.Head, tail: SimpleSplit)
  /**
    * The end of splits with a default term.
    * 
    * @param default The default term.
    * @param kw The keyword of `then` or `else`. It is `None` if the split is
    *           the topmost one.
    */
  case Else(default: Term)(val kw: Opt[Keywrd[`else`.type | `then`.type | `do`.type]])
  case End
  
  inline def ~:(head: SimpleSplit.Head): Cons = Cons(head, this)
  
  def ~~:(front: SimpleSplit): SimpleSplit =
    front match
      case Cons(head, tail) => Cons(head, tail ~~: this)
      case els: Else => els
      case End => this
  
  protected def children: List[Located] = this match
    case Cons(branch, tail) => List(branch, tail)
    case els @ Else(default) => els.kw match
      case N => default :: Nil
      case S(kw) => kw :: default :: Nil
    case End => Nil
  
  def subTerms: Ls[Term] = this match
    case Cons(branch, tail) => branch.subTerms ::: tail.subTerms
    case Else(default) => default :: Nil
    case End => Nil
  
  def showDbg: Str = this match
    case Cons(branch, tail) => s"${branch.showDbg}; ${tail.showDbg}"
    case Else(default) => s"else ${default.showDbg}"
    case End => ""
  
  def prettyPrint: Str = SimpleSplit.prettyPrint(this)
  
  /** Get the results of all branches. */
  def results: Ls[Term] =
    def go(acc: Ls[Term], split: SimpleSplit): Ls[Term] = split match
      case Cons(_: Head.Let, tail) => go(acc, tail)
      case Cons(Head.Match(_, _, consequent), alternative) =>
        go(go(acc, consequent), alternative)
      case Else(default) => default :: acc
      case End => acc
    go(Nil, this).reverse
  
  /** This field is designed to be compatible with bbML. */
  private var _expandedSplit: Opt[Split] = N
  
  /**  */
  def getExpandedSplit(using TL, Ctx, State, Raise): Split = _expandedSplit.getOrElse:
    val split = Split.from(this)
    _expandedSplit = S(split)
    split

object SimpleSplit:
  object IfThenElse:
    def unapply(split: SimpleSplit): Opt[(Term, Term, Term)] = split match
      case Cons(
          Head.Let(binding, condition),
          Cons(Head.Match(
            scrutinee,
            Pattern.Literal(BoolLit(true)), Else(consequent)),
            Else(alternative))
      ) if scrutinee.sym === binding => S((condition, consequent, alternative))
      case _ => N
  
  /** Represents a single branch of a simple split. */
  enum Head extends AutoLocated:
    case Match(scrutinee: Term.Ref, pattern: Pattern, consequent: SimpleSplit)
    case Let(binding: BlockLocalSymbol, term: Term)
    
    def subTerms: Ls[Term] = this match
      case Match(scrutinee, pattern, consequent) =>
        scrutinee :: pattern.subTerms ::: consequent.subTerms
      case Let(_, term) => term :: Nil
    
    def showDbg: Str = this match
      case Match(scrutinee, pattern, consequent) =>
        val consequentStr = consequent match
          case Cons(_, _) => s"and ${consequent.showDbg}"
          case Else(default) => s"then ${default.showDbg}"
          case End => "then {}"
        s"${scrutinee.showDbg} is ${pattern.showDbg} ${consequentStr}"
      case Let(binding, term) => s"let ${binding.nme} = ${term.showDbg}"
    
    protected def children: List[Located] = this match
      case Match(scrutinee, pattern, consequent) =>
        List(scrutinee, pattern, consequent)
      case Let(binding, term) => List(binding, term)
  
  private[semantics] object prettyPrint:
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
    
    /** Show a split as a list of lines.
     *  @param isFirst whether this is the first and frontmost branch
     *  @param isTopLevel whether this is the top-level split
     */
    private[semantics] def split(s: SimpleSplit, isFirst: Bool, isTopLevel: Bool): Lines = s match
      case SimpleSplit.Cons(head: Head.Match, tail) => (branch(head, isTopLevel) match
        case (n, line) :: tail => (n, line) :: tail
        case Nil => Nil
      ) ::: split(tail, false, isTopLevel)
      case SimpleSplit.Cons(Head.Let(nme, rhs), tail) =>
        (0, s"let $nme = ${rhs.showDbg}") :: split(tail, false, true)
      case SimpleSplit.Else(t) =>
        (if isFirst && !isTopLevel then "" else "else") #: term(t)
      case SimpleSplit.End => Nil
    
    private def term(t: Statement): Lines = (0, t.showDbg) :: Nil
    
    private def branch(b: Head.Match, isTopLevel: Bool): Lines =
      val Head.Match(scrutinee, pattern, consequent) = b
      val lines = split(consequent, true, false)
      val prefix = s"${scrutinee.sym} is ${pattern.showDbg}"
      consequent match
        case SimpleSplit.Else(_) => (prefix + " then") #: lines
        case _ => (prefix + " and") #: lines
    
    private def showSplit(prefix: Str, s: SimpleSplit): Str =
      val lines = split(s, true, true)
      (if prefix.isEmpty then lines else prefix #: lines).toIndentedString
  
  end prettyPrint

