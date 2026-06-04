package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*, Elaborator.State, ucs.FlatPattern

final case class Branch(scrutinee: Term.Ref, pattern: FlatPattern, continuation: Split) extends AutoLocated:
  def mkClone(using State): Branch =
    val scrutineeClone = new Term.Ref(scrutinee.sym)
        (Tree.Ident(scrutinee.tree.name), scrutinee.refNum, scrutinee.typ)
    Branch(scrutineeClone, pattern.mkClone, continuation.mkClone)
  
  override def children: Vector[Located] = Vector.triple(scrutinee, pattern, continuation)
  
  def showDbg(using DebugPrinter): String = s"${scrutinee.sym.nme} is ${pattern.showDbg} -> { ${continuation.showDbg} }"

object Branch:
  def apply(scrutinee: Term.Ref, continuation: Split): Branch =
    Branch(scrutinee, FlatPattern.Lit(Tree.BoolLit(true)), continuation)

enum Split extends AutoLocated with ProductWithTail:
  case Cons(head: Branch, tail: Split)
  case Let(sym: LocalVarSymbol, term: Term, tail: Split)
  case Else(default: Term)
  case End
  /** Declares a named split (join point). The symbol's `body` holds the shared
    * split; `tail` is the continuation where the symbol is in scope. */
  case LetSplit(sym: SplitSymbol, tail: Split)
  /** References a previously declared split (join point). */
  case UseSplit(sym: SplitSymbol)
  
  inline def ~:(head: Branch): Split = Split.Cons(head, this)
  
  def mkClone(using State): Split = this match
    case Cons(head, tail) => Cons(head.mkClone, tail.mkClone)
    case Let(sym, term, tail) => Let(sym, term.mkClone, tail.mkClone)
    case Else(default) => Else(default.mkClone)
    case End => End
    case LetSplit(sym, tail) => LetSplit(sym, tail.mkClone)
    case UseSplit(sym) => UseSplit(sym)
  
  /** Used to indicate whether the `Split` was duplicated during desugaring or
    * normalization. */
  def duplicated: Bool = false
  
  private var _duplicated: Bool = false
  
  def setDuplicated: this.type =
    if this != End then _duplicated = true
    this
  
  def duplicate: Split =
    (this match
      case Cons(head, tail) => Cons(head, tail.duplicate)
      case Let(name, term, tail) => Let(name, term, tail.duplicate)
      case Else(default) => Else(default)
      case End => End
      case LetSplit(sym, tail) => LetSplit(sym, tail.duplicate)
      case UseSplit(sym) => UseSplit(sym)).setDuplicated
  
  lazy val isFull: Bool = this match
    case Split.Cons(_, tail) => tail.isFull
    case Split.Let(_, _, tail) => tail.isFull
    case Split.Else(_) => true
    case Split.End => false
    case Split.LetSplit(_, tail) => tail.isFull
    case Split.UseSplit(sym) => sym.body.isFull
  
  lazy val isEmpty: Bool = this match
    case Split.Let(_, _, tail) => tail.isEmpty
    case Split.Else(_) | Split.Cons(_, _) => false
    case Split.End => true
    case Split.LetSplit(_, tail) => tail.isEmpty
    case Split.UseSplit(sym) => sym.body.isEmpty
  
  /** Approximate tree size, used to decide whether sharing via `LetSplit` is
    * worthwhile compared to inlining (see `patMatConsequentSharingThreshold`). */
  lazy val size: Int = this match
    case Split.Cons(Branch(scrutinee, _, continuation), tail) =>
      scrutinee.size + continuation.size + tail.size + 1
    case Split.Let(_, term, tail) => term.size + tail.size + 1
    case Split.Else(term) => term.size
    case Split.End => 0
    case Split.LetSplit(_, tail) => tail.size
    case Split.UseSplit(_) => 0
  
  final override def children: Vector[Located] = this match
    case Split.Cons(head, tail) => Vector.double(head, tail)
    case Split.Let(name, term, tail) => Vector.triple(name, term, tail)
    case Split.Else(default) => Vector.single(default)
    case Split.End => Vector.empty
    case Split.LetSplit(sym, tail) => Vector.double(sym, tail)
    case Split.UseSplit(sym) => Vector.single(sym)
  
  def subTerms: Vector[Term] = this match
    case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => 
      scrutinee +: (pattern.subTerms ++ continuation.subTerms ++ tail.subTerms)
    case Split.Let(_, term, tail) => term +: tail.subTerms
    case Split.Else(term) => Vector.single(term)
    case Split.End => Vector.empty
    case Split.LetSplit(sym, tail) => sym.body.subTerms ++ tail.subTerms
    case Split.UseSplit(_) => Vector.empty
  
  /** Free variable names, accounting for let bindings. */
  lazy val freeVars: Set[Str] = this match
    case Split.Cons(Branch(scrutinee, pattern, continuation), tail) =>
      scrutinee.freeVars ++ pattern.subTerms.iterator.flatMap(_.freeVars) ++
        continuation.freeVars ++ tail.freeVars
    case Split.Let(sym, term, tail) =>
      term.freeVars ++ (tail.freeVars - sym.nme)
    case Split.Else(term) => term.freeVars
    case Split.End => Set.empty
    case Split.LetSplit(sym, tail) => sym.body.freeVars ++ tail.freeVars
    case Split.UseSplit(sym) => sym.body.freeVars
  
  infix def uses(sym: SplitSymbol): Bool = freeSplitSyms.contains(sym)
  
  /** Free split symbols: those appearing in `UseSplit` references that no
    * enclosing `LetSplit` binds. */
  lazy val freeSplitSyms: Set[SplitSymbol] = this match
    case Split.Cons(Branch(_, _, continuation), tail) =>
      continuation.freeSplitSyms ++ tail.freeSplitSyms
    case Split.Let(_, _, tail) => tail.freeSplitSyms
    case Split.Else(_) | Split.End => Set.empty
    case Split.LetSplit(sym, tail) =>
      (sym.body.freeSplitSyms ++ tail.freeSplitSyms) - sym
    case Split.UseSplit(sym) => sym.body.freeSplitSyms + sym
  
  final def showDbg(using DebugPrinter): String = this match
    case Split.Cons(head, tail) => s"${head.showDbg}; ${tail.showDbg}"
    case Split.Let(name, term, tail) => s"let ${name} = ${term.showDbg}; ${tail.showDbg}"
    case Split.Else(default) => s"else ${default.showDbg}"
    case Split.End => ""
    case Split.LetSplit(sym, tail) => s"let-split ${sym.nme} = { ${sym.body.showDbg} }; ${tail.showDbg}"
    case Split.UseSplit(sym) => s"$$${sym.nme}"
  
  final override def withLoc(loco: Option[Loc]): this.type =
    super.withLoc:
      this match
        // `Split.Nil` must not have a location. This prevents sharing locations,
        // which causes the assertion of distinctness of origins to fail.
        case Split.End => N
        case _: Split.Else => N // FIXME: @Luyu pls clean up this mess
        case _: Split.UseSplit => N
        case _ => loco

  def prettyPrint(using DebugPrinter): Str = Split.prettyPrint(this)
end Split

extension (split: Split)
  def ~~:(fallback: Split)(using Raise): Split =
    if fallback == Split.End || split.isFull
    then split
    else split match
      case Split.Cons(head, tail) => Split.Cons(head, tail ~~: fallback)
      case Split.Let(name, term, tail) => Split.Let(name, term, tail ~~: fallback)
      case Split.Else(_) => lastWords("impossible since split is not full")
      case Split.End => fallback
      case Split.LetSplit(sym, tail) => Split.LetSplit(sym, tail ~~: fallback)
      case Split.UseSplit(sym) =>
        // We always append a default else branch to splits, and normalization
        // propagates that default into inner splits, so every LetSplit body
        // ends up full. The dropped `fallback` here would have been dropped anyway.
        softAssert(sym.body.isFull, "UseSplit body should be full")
        split

object Split:
  def default(term: Term): Split = Split.Else(term)
  
  import SimpleSplit as SS
  import Elaborator.{Ctx, State}
  import utils.{tl, TL}
  import collection.mutable.{Map as MutMap}
  import ups.SplitCompiler, SplitCompiler.{MakeConsequent, Scrut, SymbolScrut}
  import Term.Ref
  
  /** Desugar a `SimpleSplit` into a `Split`. */
  def from(rootSplit: SS)(using tl: TL)(using Ctx, Raise, State): Split =
    val compiler = new SplitCompiler()
    val scrutCache = MutMap.empty[Ref, Scrut]
    def go(split: SS): Split = split match
      case SS.Cons(branch, tail) => branch match
        case SS.Head.Match(ref, pattern, consequent) =>
          lazy val alternative = go(tail)
          val makeConsequent: MakeConsequent = (output, bindings) =>
            bindings.iterator.foldLeft(go(consequent)):
              case (innerSplit, (symbol, mkTerm)) => Let(symbol, mkTerm(), innerSplit)
          compiler.makeMatchSplit
            (scrutCache.getOrElseUpdate(ref, Scrut.from(ref)), pattern, false)
            (makeConsequent, alternative)
        case SS.Head.Let(binding, term) => Let(binding, term, go(tail))
      case SS.Else(default) => Else(default)
      case SS.End => End
    go(rootSplit)

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
    
    inline def apply(s: Split)(using DebugPrinter): Str = showSplit("‹if|while›", s)
    
    private def showSplit(prefix: Str, s: Split)(using DebugPrinter): Str =
      /** Show a split as a list of lines.
       *  @param isFirst whether this is the first and frontmost branch
       *  @param isTopLevel whether this is the top-level split
       */
      def split(s: Split, isFirst: Bool, isTopLevel: Bool): Lines =
        val lines = s match
          case Split.Cons(head, tail) => (branch(head, isTopLevel) match
            case (n, line) :: tail => (n, line) :: tail
            case Nil => Nil
          ) ::: split(tail, false, isTopLevel)
          case Split.Let(nme, rhs, tail) =>
            (0, s"let $nme = ${rhs.showDbg}") :: split(tail, false, true)
          case Split.Else(t) =>
            (if isFirst && !isTopLevel then "" else "else") #: term(t)
          case Split.End => Nil
          case Split.LetSplit(sym, tail) =>
            val bodyLines = split(sym.body, true, true)
            (s"let-split ${sym.nme} =" #: bodyLines) ::: split(tail, false, isTopLevel)
          case Split.UseSplit(sym) =>
            (0, s"$$${sym.nme}") :: Nil
        if s.duplicated then lines.map:
          case (n, line) if !line.endsWith("// duplicated") => (n, s"$line // duplicated")
          case other => other
        else
          lines
      def term(t: Statement): Lines = t match
        case Term.Blk(stmts, term) =>
          stmts.iterator.concat(Iterator.single(term)).flatMap:
            case DefineVar(sym, Term.IfLike(kw, IfLikeForm.ReturningIf, splt)) =>
              s"$sym = ${kw.name}" #: SimpleSplit.prettyPrint.split(splt, true, true)
            case DefineVar(sym, Term.SynthIf(splt)) =>
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
