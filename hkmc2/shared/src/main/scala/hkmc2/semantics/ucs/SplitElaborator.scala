package hkmc2
package semantics
package ucs

import hkmc2.utils.*, shorthands.*
import syntax.{Keyword, Tree}, Tree.*
import Keyword.{`and`, `do`, `else`, `if`, `case`, `while`, `is`, `let`, `or`, `then`}
import Elaborator.{Ctx, Ctxl, UnderCtx, ctx}, SimpleSplit.*
import Message.MessageContext
import collection.mutable.SortedSet
import utils.TL
import scala.annotation.tailrec

object SplitElaborator:
  /** A scrutinee is a function that returns a reference to the symbol. */
  type Reference = () => Term.Ref
  
  type Connective = `do`.type | `then`.type
import SplitElaborator.*

trait SplitElaborator:
  self: Elaborator =>
  
  import tl.*
  
  private given TL = tl
  
  private given Ordering[Loc] = Ordering.by(l => (l.spanStart, l.spanEnd))
  
  /** Keep track of the locations where `do` and `then` are used as connectives. */
  private var kwLocSets = (SortedSet.empty[Loc], SortedSet.empty[Loc])
  
  private def reportInconsistentConnectives(kw: Keywrd[Keyword.SplitLike]): Unit =
    (kwLocSets._1.headOption, kwLocSets._2.headOption) match
      case (Some(doLoc), Some(thenLoc)) =>
        raise(ErrorReport(
          msg"Mixed use of `do` and `then` in the `${kw.kw.name}` expression." -> kw.toLoc
            :: msg"Keyword `then` is used here." -> S(thenLoc)
            :: msg"Keyword `do` is used here." -> S(doLoc) :: Nil
        ))
      case _ => ()
  
  private def topmostDefault: SimpleSplit =
    if kwLocSets._1.nonEmpty then Else(Term.UnitVal())(N) else End
  
  private object `~>`:
    infix def unapply(tree: Tree): Opt[(Tree, Tree \/ (Keywrd[Connective], Tree))] = tree match
      case InfixApp(lhs, Keywrd(`and`), rhs) => S((lhs, L(rhs)))
      case InfixApp(lhs, kwTree @ Keywrd(kw: `then`.type), rhs) =>
        kwLocSets._2 ++= kwTree.toLoc
        S((lhs, R((new Keywrd(kw).withLocOf(kwTree), rhs))))
      case InfixApp(lhs, kwTree @ Keywrd(kw: `do`.type), rhs) =>
        kwLocSets._1 ++= kwTree.toLoc
        S((lhs, R((new Keywrd(kw).withLocOf(kwTree), rhs))))
      case _ => N
  
  private def withScopedConnectives
      (kw: Keywrd[Keyword.SplitLike])(evaluate: => SimpleSplit): (IfLikeForm, SimpleSplit) =
    val savedKwLocSets = kwLocSets
    kwLocSets = (SortedSet.empty, SortedSet.empty)
    val split = evaluate
    val (result, form) = kw.kw match
      case `if` | `case` =>
        (split ~~: topmostDefault,
          if kwLocSets._1.nonEmpty then IfLikeForm.ImperativeIf else IfLikeForm.ReturningIf)
      case `while` => (split, IfLikeForm.While)
    reportInconsistentConnectives(kw)
    kwLocSets = savedKwLocSets
    (form, result)
  
  /** Transform trees into a UCS split. */
  protected def split(t: IfLike): Ctxl[Term.IfLike] =
    val (form, split) = withScopedConnectives(t.kw):
      t.split match
      case block: Block => termSplit(block.desugStmts, identity)
      case other: Tree => termSplit(Ls(other), identity)
    new Term.IfLike(t.kw.kw, form, split).withLocOf(t)
  
  /** Elaborate `case` expressions */
  protected def caseSplit(scrut: VarSymbol, tree: Case): Ctxl[Term.IfLike] =
    val (form, split) = withScopedConnectives(tree.kw):
      patternBranch(() => scrut.ref(), tree.branches, identity)
    new Term.IfLike(tree.kw.kw, form, split).withLocOf(tree)
  
  /** Elaborate shorthand expressions. */
  protected def shorthandSplit(tree: Tree)(using UnderCtx): Ctxl[SimpleSplit] =
    val affirmative = Else(Term.Lit(BoolLit(true)))(N)
    val negative = Else(Term.Lit(BoolLit(false)))(N)
    val (scrutinee, pattern) :: matches = disaggregate(tree)
    subterm(scrutinee).reference: scrutinee =>
      lazy val innerSplit: Ctxl[SimpleSplit] = expandMatches(matches)(affirmative)
      pattern match
        case Block(Nil) =>
          val recordPattern = Pattern.Record(Nil).withLocOf(pattern)
          Head.Match(scrutinee(), recordPattern, innerSplit) ~: negative
        case Block(trees) => trees.foldRight(negative):
          case (pattern, alternative) =>
            Head.Match(scrutinee(), self.pattern(pattern), innerSplit) ~: alternative
        case _ =>
          val firstPattern = self.pattern(pattern)
          firstPattern.variables.report
          (ctx ++ firstPattern.variables.allocate).givenIn:
            Head.Match(scrutinee(), firstPattern, innerSplit) ~: negative
  
  /** Desugar a list of trees as a term split. The returned function takes a
    * function, which takes a `Ctx` and returns a `SimpleSplit` representing
    * the _alternative_ split, and returns a `SimpleSplit` representing the
    * split of the given trees. */
  private def termSplit(ts: Ls[Tree], mk: Term => Term): Ctxl[SimpleSplit] =
    val (_, splits) = ts.foldLeft((ctx, Ls[SimpleSplit]())):
      case ((curCtx, splits), t) =>
        termBranch(t, mk)(using curCtx).mapSecond(_ :: splits)
    concatenate(splits)
  
  /** Concatenate a sequence of splits and report warning for splits that come
    * after a split which ends with an `else` branch. */
  private def concatenate(splits: Ls[SimpleSplit]): SimpleSplit =
    // The first element is a list of branches. The second element is
    // - `N` if no `else` branch has been found; or
    // - `S((default, unreachables))` if `default` is the first `else` branch
    //   in the split and all splits thereafter will be added to `unreachables`.
    val z: (Ls[Head], Opt[(Else, Ls[SimpleSplit])]) = (Nil, N)
    val (reachables, elseRest) = splits.reverseIterator.foldLeft(z):
      // This is the case when we haven't found an `else` branch yet.
      case ((branches, N), split) =>
        @tailrec
        def go(acc: Ls[Head], split: SimpleSplit): (Ls[Head], Opt[Else]) =
          split match
            case Cons(branch, tail) => go(branch :: acc, tail)
            case els: Else => (acc, S(els))
            case End => (acc, N)
        go(branches, split).mapSecond(_.map(_ -> (Nil: Ls[SimpleSplit])))
      case ((branches, S((default, unreachables))), split) =>
        (branches, S((default, split :: unreachables)))
    // Report unreachables splits.
    elseRest match
      case S((default, unreachables)) =>
        val messages = unreachables.reverseIterator.map: split =>
          msg"This branch is unreachable." -> split.toLoc
        .toList
        if messages.nonEmpty then
          raise(WarningReport((msg"This catch-all clause makes the following branches unreachable." -> default.toLoc :: messages)))
      case N => ()
    // Reconstruct the split from the reachable `heads`.
    reachables.foldLeft(elseRest.fold(SimpleSplit.End)(_._1)):
      case (innerSplit, branch) => branch ~: innerSplit
  
  /** Handle the common cases of branches in splits. */
  private def branch(using Ctx): Cfg[PartialFunction[Tree, (Ctx, SimpleSplit)]] =
    // Interleaved-`let` bindings like `{ x is A then 0; let x = 1; ... }`.
    case LetLike(Keywrd(`let`), ident: Ident, S(rhsTree), N) =>
      val symbol = VarSymbol(ident)
      val head = Head.Let(symbol, term(rhsTree)) 
      ((ctx + (ident.name -> symbol)), head ~: End)
    // Interleaved-`do` statements like `{ x is A then 0; do log(1); ... }`.
    case PrefixApp(Keywrd(`do`), rhsTree) =>
      (ctx, Head.Let(TempSymbol(N, "unused"), term(rhsTree)) ~: End)
    // Although the `else`-clause marks the end of the split, we cannot
    // stop and still have to elaborate the remaining trees.
    case PrefixApp(kwTree @ Keywrd(`else`), elseTree) =>
      (ctx, Else(term(elseTree))(S(new Keywrd(`else`).withLocOf(kwTree))))
  
  private def expandMatches(matchesTree: Ls[TT])(consequent: Ctxl[SimpleSplit]): Ctxl[SimpleSplit] =
    val z = (ctx, Ls[(Term, Pattern)]())
    // Elaborate the term and the pattern in each match.
    val (innerCtx, matches) = matchesTree.foldLeft(z):
      case ((curCtx, matches), (scrutineeTree, patternTree)) =>
        val scrutinee = term(scrutineeTree)(using curCtx)
        val pattern = self.pattern(patternTree)(using curCtx)
        pattern.variables.report
        val resCtx = curCtx ++ pattern.variables.allocate
        (resCtx, (scrutinee, pattern) :: matches)
    // As `matches` is reversed, we should process it from the left.
    val split = matches.foldLeft(consequent(using innerCtx)):
      case (innerSplit, (scrutinee, pattern)) =>
        scrutinee.reference: scrutineeRef =>
          Head.Match(scrutineeRef(), pattern, innerSplit) ~: End
    split
  
  private def termBranch(t: Tree, mk: Term => Term): Ctxl[(Ctx, SimpleSplit)] = branch.appOrElse(t):
    case block: Block => (ctx, termSplit(block.desugStmts, mk))
    case lhs is rhs => (ctx, mk(term(lhs)).reference(patternBranch(_, rhs, identity)))
    // Several matches followed by `and`, `do`, or `then`.
    case matchesTree ~> consequent =>
      val (coda, patternTree) :: matches = disaggregate(matchesTree)
      def innerSplit(using ctx: Ctx) = expandMatches(matches):
        consequent match
          case L(tree) => termSplit(Ls(tree), identity)
          case R((kw, tree)) => Else(term(tree))(S(kw))
      val split = coda match
        case Under() => innerSplit
        case coda => mk(term(coda)).reference: scrutinee =>
          val pattern = self.pattern(patternTree)
          val innerCtx = ctx ++ pattern.variables.allocate
          Head.Match(scrutinee(), pattern, innerSplit(using innerCtx)) ~: End
      (ctx, split)
    // Handle splits on binary operators.
    case OpApp(lhs, ident: Ident, rhss) =>
      val op = term(ident)
      val split = term(lhs).reference: lhs =>
        val mk2 = (rhs: Term) =>
          val args = Term.Tup(PlainFld(lhs()) :: PlainFld(rhs) :: Nil)(DummyTup)
          Term.App(op, args)(Tree.DummyApp, N, FlowSymbol("‹operator-split›"))
        termSplit(rhss, mk2 andThen mk)
      (ctx, split)
    case OpSplit(lhs, rhss) =>
      val split = mk(term(lhs)).reference: lhs =>
        val (_, splits) = rhss.foldLeft((ctx, Ls[SimpleSplit]())):
          case ((curCtx, splits), t) =>
            operatorBranch(lhs, t)(using curCtx).mapSecond(_ :: splits)
        concatenate(splits)
      (ctx, split)
    // Unrecognized term split.
    case _ =>
      error(msg"Unrecognized term split (${t.describe})" -> t.toLoc)
      (ctx, End)
  
  private def operatorBranch(scrutinee: Reference, rhs: Tree): Ctxl[(Ctx, SimpleSplit)] =
    branch.appOrElse(rhs): rhsTree => 
      termBranch(rhsTree.splitOn(Trm(scrutinee())), identity)
  
  private def patternBranch(scrutinee: Reference, t: Tree, mk: Tree => Tree): Ctxl[SimpleSplit] = t match
    case block: Block =>
      val (_, splits) = block.desugStmts.foldLeft((ctx, Ls[SimpleSplit]())):
        case ((curCtx, splits), t) =>
          branch(using curCtx).lift(t).getOrElse:
            (curCtx, patternBranch(scrutinee, t, mk)(using curCtx))
          .mapSecond(_ :: splits)
      concatenate(splits)
    case App(ctor: Ctor, Tup(rhss)) =>
      val nl = (t: Tree) => mk(App(ctor, Tup(t :: Nil)))
      patternBranch(scrutinee, Block(rhss), nl)
    case Annotated(annotation, target) =>
      patternBranch(scrutinee, target, Annotated(annotation, _) |> mk)
    case patternAndMatches ~> consequentTree =>
      val (firstPatternTree, _) :: matches = disaggregate(patternAndMatches)
      val firstPattern = self.pattern(mk(firstPatternTree))
      firstPattern.variables.report
      (ctx ++ firstPattern.variables.allocate).givenIn:
        val split = expandMatches(matches):
          consequentTree match
            case L(tree) =>
              termSplit(Ls(tree), identity)
            case R((kw, tree)) => Else(term(tree))(S(kw))
        Head.Match(scrutinee(), firstPattern, split) ~: End
    case _ =>
      error(msg"Unrecognized pattern split (${t.describe})." -> t.toLoc)
      Else(Term.Error)(N).withLocOf(t) // To inspect the source of errors.
  
  extension (term: Term)
    private inline def reference(continuation: Reference => SimpleSplit): SimpleSplit =
      term match
        // If the term is already a reference, we can re-reference its symbol.
        case Term.Ref(symbol) => continuation(() => symbol.ref())
        // Otherwise, we need to create a temporary symbol holding the term.
        case term: Term =>
          val symbol = TempSymbol(N, "scrut")
          Head.Let(symbol, term) ~: continuation(() => symbol.ref())
  
  private type TT = (Tree, Tree)
  
  /** Decompose a `Tree` of conjunct matches. The tree is from the same line in
   *  the source code and followed by a `then`, or `and` with a continued line.
   *  A formal definition of the conjunction is:
   *  
   *  ```bnf
   *  conjunction ::= conjunction `and` conjunction  # conjunction
   *                | term `is` pattern              # pattern matching
   *                | term                           # Boolean condition
   *  ```
   * 
   *  Each match is represented by a pair of a _coda_ and a _pattern_ that is
   *  yet to be elaborated. For boolean conditions, the pattern is a `BoolLit`.
   * 
   *  This function does not invoke elaboration and the implementation utilizes
   *  functional lists to avoid calling the `reverse` method on the output,
   *  which returns type `List[T]` instead of `::[T]`. See paper _A Novel
   *  Representation of Lists and Its Application to the Function_ for details.
   * 
   *  @param tree the tree to desugar
   *  @return a non-empty list of scrutinee and pattern pairs represented in
   *          type `::[T]` (instead of `List[T]`) so that the head element
   *          can be retrieved in a type-safe manner
   */
  private def disaggregate(tree: Tree): ::[TT] =
    def go(tree: Tree, acc: TT => ::[TT]): () => ::[TT] = tree match
      case lhs `and` rhs  => go(lhs, ::(_, go(rhs, acc)()))
      case lhs `or` rhs   =>
        error(msg"Logical `or` is not yet supported." -> tree.toLoc)
        go(lhs, ::(_, go(rhs, acc)())) // FIXME: this is currently copy-pasted from the `and` case
      case scrut `is` pat => () => acc((scrut, pat))
      case test           => () => acc((test, Tree.BoolLit(true)))
    go(tree, ::(_, Nil))()

