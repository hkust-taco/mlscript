package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*

final case class Branch(scrutinee: Term.Ref, pattern: Pattern, continuation: Split) extends AutoLocated:
  override def children: List[Located] = scrutinee :: pattern :: continuation :: Nil
  def showDbg: String = s"${scrutinee.sym.nme} is ${pattern.showDbg} -> { ${continuation.showDbg} }"

object Branch:
  def apply(scrutinee: Term.Ref, continuation: Split): Branch =
    Branch(scrutinee, Pattern.LitPat(Tree.BoolLit(true)), continuation)

enum Split extends AutoLocated:
  case Cons(head: Branch, tail: Split)
  case Let(name: VarSymbol, term: Term, tail: Split)
  case Else(default: Term)
  case Nil

  inline def ::(head: Branch): Split = Split.Cons(head, this)
  
  lazy val isFull: Bool = this match
    case Split.Cons(_, tail) => tail.isFull
    case Split.Let(_, _, tail) => tail.isFull
    case Split.Else(_) => true
    case Split.Nil => false

  lazy val isEmpty: Bool = this match
    case Split.Let(_, _, tail) => tail.isEmpty
    case Split.Else(_) | Split.Cons(_, _) => false
    case Split.Nil => true

  final override def children: Ls[Located] = this match
    case Split.Cons(head, tail) => List(head, tail)
    case Split.Let(name, term, tail) => List(name, term, tail)
    case Split.Else(default) => List(default)
    case Split.Nil => List()

  final def showDbg: String = this match
    case Split.Cons(head, tail) => s"${head.showDbg}; ${tail.showDbg}"
    case Split.Let(name, term, tail) => s"let ${name.name} = ${term.showDbg}; ${tail.showDbg}"
    case Split.Else(default) => s"else ${default.showDbg}"
    case Split.Nil => ""

  var isFallback: Bool = false
end Split

object Split:
  def default(term: Term): Split = Split.Else(term)

  object display:
    /** Represents lines with indentations. */
    type Lines = Ls[(Int, Str)]

    import scala.Nil as LNil

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
        case (0, line) :: lines if lines.forall(_._1 > 0) => (0, s"$prefix $line") :: lines
        case lines => (0, prefix) :: lines.indent
    
    inline def apply(s: Split): Str = showSplit("if", s)

    private def showSplit(prefix: Str, s: Split): Str =
      def split(s: Split, isFirst: Bool, isTopLevel: Bool): Lines = s match
        case Split.Cons(head, tail) => (branch(head, isTopLevel) match
          case (n, line) :: tail => (n, (if isTopLevel then "" else "and ") + line) :: tail
          case LNil => LNil
        ) ::: split(tail, false, isTopLevel)
        case Split.Let(nme, rhs, tail) =>
          (0, s"let $nme = ${rhs.showDbg}") :: split(tail, false, true)
        case Split.Else(term) =>
          (if isFirst then (0, s"then ${term.showDbg}") else (0, s"else ${term.showDbg}")) :: LNil
        case Split.Nil => LNil
      def branch(b: Branch, isTopLevel: Bool): Lines =
        val Branch(scrutinee, pattern, continuation) = b
        val rest = split(continuation, true, isTopLevel)
        (s"${scrutinee.sym} is ${pattern.showDbg}" + 
          (if rest.length > 1 then " and" else s"")) #: rest
      val lines = split(s, true, true)
      (if prefix.isEmpty then lines else prefix #: lines).toIndentedString
