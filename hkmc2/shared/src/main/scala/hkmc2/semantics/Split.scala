package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*, ucs.FlatPattern

final case class Branch(scrutinee: Term.Ref, pattern: FlatPattern, continuation: Split) extends AutoLocated:
  override def children: List[Located] = scrutinee :: pattern :: continuation :: Nil
  def showDbg: String = s"${scrutinee.sym.nme} is ${pattern.showDbg} -> { ${continuation.showDbg} }"

object Branch:
  def apply(scrutinee: Term.Ref, continuation: Split): Branch =
    Branch(scrutinee, FlatPattern.Lit(Tree.BoolLit(true))(Nil), continuation)

enum Split extends AutoLocated with ProductWithTail:
  case Cons(head: Branch, tail: Split)
  case Let(sym: BlockLocalSymbol, term: Term, tail: Split)
  case Else(default: Term)
  case End
  
  inline def ~:(head: Branch): Split = Split.Cons(head, this)
  
  lazy val isFull: Bool = this match
    case Split.Cons(_, tail) => tail.isFull
    case Split.Let(_, _, tail) => tail.isFull
    case Split.Else(_) => true
    case Split.End => false
  
  lazy val isEmpty: Bool = this match
    case Split.Let(_, _, tail) => tail.isEmpty
    case Split.Else(_) | Split.Cons(_, _) => false
    case Split.End => true
  
  final override def children: Ls[Located] = this match
    case Split.Cons(head, tail) => List(head, tail)
    case Split.Let(name, term, tail) => List(name, term, tail)
    case Split.Else(default) => List(default)
    case Split.End => Nil
  
  def subTerms: Ls[Term] = this match
    case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => 
      scrutinee :: pattern.subTerms ++ continuation.subTerms ++ tail.subTerms
    case Split.Let(_, term, tail) => term :: tail.subTerms
    case Split.Else(term) => term :: Nil
    case Split.End => Nil
  
  final def showDbg: String = this match
    case Split.Cons(head, tail) => s"${head.showDbg}; ${tail.showDbg}"
    case Split.Let(name, term, tail) => s"let ${name} = ${term.showDbg}; ${tail.showDbg}"
    case Split.Else(default) => s"else ${default.showDbg}"
    case Split.End => ""
  
  final override def withLoc(loco: Option[Loc]): this.type =
    super.withLoc:
      this match
        // `Split.Nil` must not have a location. This prevents sharing locations,
        // which causes the assertion of distinctness of origins to fail.
        case Split.End => N
        case _: Split.Else => N // FIXME: @Luyu pls clean up this mess
        case _ => loco
  
  var isFallback: Bool = false
  
  def prettyPrint: Str = Split.prettyPrint(this)
end Split

extension (split: Split)
  def ~~:(fallback: Split): Split =
    if fallback == Split.End || split.isFull then
      split
    else (split match
      case Split.Cons(head, tail) => Split.Cons(head, tail ~~: fallback)
      case Split.Let(name, term, tail) => Split.Let(name, term, tail ~~: fallback)
      case Split.Else(_) /* impossible */ | Split.End => fallback)

object Split:
  def default(term: Term): Split = Split.Else(term)

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
    
    inline def apply(s: Split): Str = showSplit("if", s)
    
    private def showSplit(prefix: Str, s: Split): Str =
      /** Show a split as a list of lines.
       *  @param isFirst whether this is the first and frontmost branch
       *  @param isTopLevel whether this is the top-level split
       */
      def split(s: Split, isFirst: Bool, isTopLevel: Bool): Lines = s match
        case Split.Cons(head, tail) => (branch(head, isTopLevel) match
          case (n, line) :: tail => (n, line) :: tail
          case Nil => Nil
        ) ::: split(tail, false, isTopLevel)
        case Split.Let(nme, rhs, tail) =>
          (0, s"let $nme = ${rhs.showDbg}") :: split(tail, false, true)
        case Split.Else(t) =>
          (if isFirst && !isTopLevel then "" else "else") #: term(t)
        case Split.End => Nil
      def term(t: Statement): Lines = t match
        case Term.Blk(stmts, term) =>
          stmts.iterator.concat(Iterator.single(term)).flatMap:
            case DefineVar(sym, Term.IfLike(Keyword.`if`, splt)) =>
              s"$sym = if" #: split(splt, true, true)
            case stmt => (0, stmt.showDbg) :: Nil
          .toList
        case t: Statement => (0, t.showDbg) :: Nil
      def branch(b: Branch, isTopLevel: Bool): Lines =
        val Branch(scrutinee, pattern, consequent) = b
        val lines = split(consequent, true, false)
        val prefix = s"${scrutinee.sym} is ${pattern.showDbg}"
        consequent match
          case Split.Else(_) => (prefix + " then") #: lines
          case _ => (prefix + " and") #: lines
      val lines = split(s, true, true)
      (if prefix.isEmpty then lines else prefix #: lines).toIndentedString
  
  end prettyPrint
