package hkmc2
package semantics
package ucs

import syntax.{BracketKind, Keyword, Literal, Tree}, Tree.*
import mlscript.utils.*, shorthands.*
import Message.MessageContext
import utils.TraceLogger
import Keyword.{`as`, `and`, `or`, `do`, `else`, is, let, `then`, where}
import collection.mutable.{Buffer, HashMap, SortedSet}
import Elaborator.{Ctx, Ctxl, State, UnderCtx, ctx}
import scala.annotation.targetName
import FlatPattern.{Argument, MatchMode}

object Desugarer:
  extension (op: Keyword.Infix)
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case InfixApp(lhs, `op`, rhs) => S((lhs, rhs))
      case _ => N
  
  type Ctor = SynthSel | Sel | Ident
  
  class ScrutineeData:
    val subScrutinees: Buffer[BlockLocalSymbol] = Buffer.empty
    val fields: HashMap[Ident, BlockLocalSymbol] = HashMap.empty
    val tupleLead: HashMap[Int, BlockLocalSymbol] = HashMap.empty
    val tupleLast: HashMap[Int, BlockLocalSymbol] = HashMap.empty
end Desugarer

class Desugarer(elaborator: Elaborator)(using Ctx, Raise, State, Config, UnderCtx):
  import Desugarer.*, elaborator.term, elaborator.subterm, elaborator.tl, tl.*
  
  // A few helper methods to select useful functions from the runtime.
  private def selectTuple: Term.SynthSel =
    Term.SynthSel(State.runtimeSymbol.ref(), Ident("Tuple"))(N)
  private def tupleSlice = Term.SynthSel(selectTuple, Ident("slice"))(N)
  private def tupleLazySlice = Term.SynthSel(selectTuple, Ident("lazySlice"))(N)
  private def tupleGet = Term.SynthSel(selectTuple, Ident("get"))(N)
  private def callTupleGet(t: Term, i: Int, s: FlowSymbol): Term =
    val args = PlainFld(t) :: PlainFld(Term.Lit(IntLit(BigInt(i)))) :: Nil
    Term.App(tupleGet, Term.Tup(args)(DummyTup))(DummyApp, N, s)
  
  given Ordering[Loc] = Ordering.by: loc =>
    (loc.spanStart, loc.spanEnd)
  
  /** Keep track of the locations where `do` and `then` are used as connectives. */
  private val kwLocSets = (SortedSet.empty[Loc], SortedSet.empty[Loc])
  
  private def reportInconsistentConnectives(kw: Keywrd[?]): Unit =
    log(kwLocSets)
    (kwLocSets._1.headOption, kwLocSets._2.headOption) match
      case (Some(doLoc), Some(thenLoc)) =>
        raise(ErrorReport(
          msg"Mixed use of `do` and `then` in the `${kw.kw.name}` expression." -> kw.toLoc
            :: msg"Keyword `then` is used here." -> S(thenLoc)
            :: msg"Keyword `do` is used here." -> S(doLoc) :: Nil
        ))
      case _ => ()
  
  private def topmostDefault: Split =
    if kwLocSets._1.nonEmpty then Split.Else(Term.UnitVal()) else Split.End
  
  /** An extractor that accepts either `A and B`, `A then B`, and `A do B`. It
   *  also keeps track of the usage of `then` and `do`.
   */
  object `~>`:
    infix def unapply(tree: Tree): Opt[(Tree, Tree \/ Tree)] = tree match
      case lhs `and` rhs => S((lhs, L(rhs)))
      case lhs `then` rhs => kwLocSets._2 ++= tree.toLoc; S((lhs, R(rhs)))
      case lhs `do` rhs => kwLocSets._1 ++= tree.toLoc; S((lhs, R(rhs)))
      case _ => N

  // We're working on composing continuations in the UCS translation.
  // The type of continuation is `Split => Ctx => Split`.
  // The first parameter represents the "backup" split, which does not have
  // access to the bindings in the current match. The second parameter
  // represents the context with bindings in the current match.

  type Sequel = Ctx => Split
  

  extension (sequel: Sequel)
    @targetName("traceSequel")
    def traced(pre: Str, post: Split => Str): Sequel =
      if doTrace then ctx => trace(pre, post)(sequel(ctx)) else sequel
  
  extension (desugar: Split => Sequel)
    @targetName("traceDesugar")
    def traced(pre: Str, post: Split => Str): Split => Sequel =
      if doTrace then
        fallback => ctx => trace(pre, post)(desugar(fallback)(ctx))
      else
        desugar
  
  extension (split: Split)
    /** Concatenate two splits. */
    def ++(fallback: Split): Split =
      if fallback == Split.End then
        split
      else if split.isFull then
        split
      else split match
        case Split.Cons(head, tail) => Split.Cons(head, tail ++ fallback)
        case Split.Let(name, term, tail) => Split.Let(name, term, tail ++ fallback)
        case Split.Else(_) => split // Shouldn't actually happen because of the `split.isFull` check above
        case Split.End => fallback

  private val subScrutineeMap = HashMap.empty[BlockLocalSymbol, ScrutineeData]
  private val fieldScrutineeMap = HashMap.empty[BlockLocalSymbol, ScrutineeData]

  extension (symbol: BlockLocalSymbol)
    def getSubScrutinees(count: Int): List[BlockLocalSymbol] =
      val sd = subScrutineeMap.getOrElseUpdate(symbol, new ScrutineeData)
      subScrutineeMap.sizeHint(count)
      while sd.subScrutinees.size < count do
        val scrutinee = TempSymbol(N, s"param${sd.subScrutinees.size}")
        sd.subScrutinees += scrutinee
      sd.subScrutinees.iterator.take(count).toList
    def getTupleLeadSubScrutinee(index: Int): BlockLocalSymbol =
      val data = subScrutineeMap.getOrElseUpdate(symbol, new ScrutineeData)
      data.tupleLead.getOrElseUpdate(index, TempSymbol(N, s"first$index"))
    def getTupleLastSubScrutinee(index: Int): BlockLocalSymbol =
      val data = subScrutineeMap.getOrElseUpdate(symbol, new ScrutineeData)
      data.tupleLast.getOrElseUpdate(index, TempSymbol(N, s"last$index"))
    def getFieldScrutinee(fieldName: Ident): BlockLocalSymbol =
      subScrutineeMap
        .getOrElseUpdate(symbol, new ScrutineeData)
        .fields
        .getOrElseUpdate(fieldName, TempSymbol(N, s"field${fieldName.name}"))
      

  def default: Split => Sequel = split => _ => split

  private def termSplitShorthands(tree: Tree, finish: Term => Term): Split => Sequel = tree match
    case blk: Block => blk.desugStmts match
      case Nil => lastWords("encountered empty block")
      case branch :: rest => fallback => ctx =>
        if rest.nonEmpty then
          raise(ErrorReport(msg"only one branch is supported in shorthands" -> tree.toLoc :: Nil))
        termSplitShorthands(branch, finish)(fallback)(ctx)
    case coda is rhs => fallback => ctx =>
      nominate(ctx, finish(subterm(coda)(using ctx))):
        patternSplitShorthands(rhs, _)(fallback)
    case matches => fallback =>
      // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
      // Each match is represented by a pair of a _coda_ and a _pattern_
      // that is yet to be elaborated.
      val (headCoda, headPattern) :: tail = disaggregate(matches)
      // The `consequent` serves as the innermost split, based on which we
      // expand from the N-th to the second match.
      lazy val tailSplit =
        val innermostSplit = Function.const(Split.default(Term.Lit(Tree.BoolLit(true)))): Sequel
        tail.foldRight(innermostSplit):
          case ((coda, pat), sequel) => ctx => trace(
            pre = s"conjunct matches <<< $tail",
            post = (res: Split) => s"conjunct matches >>> $res"
          ):
            nominate(ctx, term(coda)(using ctx)):
              expandMatch(_, pat, sequel, Nil)(fallback)
      // We apply `finish` to the first coda and expand the first match.
      // Note that the scrutinee might be not an identifier.
      headCoda match
        case Under() => tailSplit
        case _ => ctx => trace(
          pre = s"shorthands <<< $matches",
          post = (res: Split) => s"shorthands >>> $res"
        ):
          nominate(ctx, finish(term(headCoda)(using ctx))):
            expandMatch(_, headPattern, tailSplit, Nil)(fallback)

  private def patternSplitShorthands(tree: Tree, scrutSymbol: BlockLocalSymbol): Split => Sequel = tree match
    case blk: Block => blk.desugStmts match
      case Nil => lastWords("encountered empty block")
      case branch :: rest => fallback => ctx =>
        if rest.nonEmpty then
          raise(ErrorReport(msg"only one pattern is supported in shorthands" -> tree.toLoc :: Nil))
        patternSplitShorthands(branch, scrutSymbol)(fallback)(ctx)
    case patternAndMatches => fallback =>
      // TODO: Deduplicate with `patternSplit`.
      // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
      // Each match is represented by a pair of a _coda_ and a _pattern_
      // that is yet to be elaborated.
      val (headPattern, _) :: tail = disaggregate(patternAndMatches)
      // The `consequent` serves as the innermost split, based on which we
      // expand from the N-th to the second match.
      val tailSplit = trace(s"conjunct matches <<< $tail"):
        val innermostSplit = Function.const(Split.default(Term.Lit(Tree.BoolLit(true)))): Sequel
        tail.foldRight(innermostSplit):
          case ((coda, pat), sequel) => ctx =>
            nominate(ctx, term(coda)(using ctx)):
              expandMatch(_, pat, sequel, Nil)(fallback)
      expandMatch(scrutSymbol, headPattern, tailSplit, Nil)(fallback)
  
  def termSplit(trees: Ls[Tree], finish: Term => Term): Split => Sequel =
    trees.foldRight(default): (t, elabFallback) =>
      t match
      case LetLike(Keywrd(`let`), ident @ Ident(_), S(termTree), N) => fallback => ctx => trace(
        pre = s"termSplit: let ${ident.name} = $termTree",
        post = (res: Split) => s"termSplit: let >>> $res"
      ):
        val sym = VarSymbol(ident)
        val fallbackCtx = ctx + (ident.name -> sym)
        Split.Let(sym, term(termTree)(using ctx), elabFallback(fallback)(fallbackCtx)).withLocOf(t)
      case PrefixApp(Keywrd(Keyword.`do`), computation) => fallback => ctx => trace(
        pre = s"termSplit: do $computation",
        post = (res: Split) => s"termSplit: else >>> $res"
      ):
        val sym = TempSymbol(N, "doTemp")
        Split.Let(sym, term(computation)(using ctx), elabFallback(fallback)(ctx)).withLocOf(t)
      case PrefixApp(Keywrd(Keyword.`else`), default) => fallback => ctx => trace(
        pre = s"termSplit: else $default",
        post = (res: Split) => s"termSplit: else >>> $res"
      ):
        // TODO: report `rest` as unreachable
        Split.default(term(default)(using ctx)).withLocOf(t)
      case branch => fallback => ctx => trace(
        pre = s"termSplit: $branch",
        post = (res: Split) => s"termSplit >>> $res"
      ):
        termSplit(branch, finish)(elabFallback(fallback)(ctx))(ctx)

  /** Desugar a _term split_ (TS) into a _split_ of core abstract syntax.
   *  @param tree the tree representing the term split.
   *  @param finish the accumulated partial term to be the LHS or the scrutinee
   *  @return a continuation that takes subsequent splits as fallbacks and then
   *          accepts a context with additional bindings from the enclosing
   *          matches and splits
   */
  def termSplit(tree: Tree, finish: Term => Term): Split => Sequel =
    log(s"termSplit: $tree")
    tree match
    case blk: Block => termSplit(blk.desugStmts, finish)
    case coda is rhs => fallback => ctx =>
      nominate(ctx, finish(term(coda)(using ctx))):
        patternSplit(rhs, _)(fallback)
    case matches ~> consequent => fallback =>
      // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
      // Each match is represented by a pair of a _coda_ and a _pattern_
      // that is yet to be elaborated.
      val (headCoda, headPattern) :: tail = disaggregate(matches)
      // The `consequent` serves as the innermost split, based on which we
      // expand from the N-th to the second match.
      lazy val tailSplit =
        val innermostSplit = consequent match
          case L(tree) => termSplit(tree, identity)(Split.End)
          case R(tree) => (ctx: Ctx) => Split.default(term(tree)(using ctx))
        tail.foldRight(innermostSplit):
          case ((coda, pat), sequel) => ctx => trace(
            pre = s"conjunct matches <<< $tail",
            post = (res: Split) => s"conjunct matches >>> $res"
          ):
            nominate(ctx, term(coda)(using ctx)):
              expandMatch(_, pat, sequel, Nil)(Split.End)
      // We apply `finish` to the first coda and expand the first match.
      // Note that the scrutinee might be not an identifier.
      headCoda match
        case Under() => tailSplit
        case _ => ctx => trace(
          pre = s"termBranch <<< $matches then $consequent",
          post = (res: Split) => s"termBranch >>> $res"
        ):
          nominate(ctx, finish(term(headCoda)(using ctx))):
            expandMatch(_, headPattern, tailSplit, Nil)(fallback)
    // Handle binary operators.
    case tree @ OpApp(lhs, opIdent @ Ident(opName), rhss) => fallback => ctx => trace(
      pre = s"termSplit: after op <<< $opName",
      post = (res: Split) => s"termSplit: after op >>> $res"
    ):
      // Resolve the operator.
      val opRef = term(opIdent)
      // Elaborate and finish the LHS. Nominate the LHS if necessary.
      nominate(ctx, finish(term(lhs)(using ctx))): lhsSymbol =>
        // Compose a function that takes the RHS and finishes the application.
        val finishInner = (rhsTerm: Term) =>
          val first = Fld(FldFlags.empty, lhsSymbol.ref(/* FIXME ident? */), N)
          val second = Fld(FldFlags.empty, rhsTerm, N)
          val arguments = Term.Tup(first :: second :: Nil)(Tree.DummyTup)
          val joint = FlowSymbol("‹applied-result›")
          Term.App(opRef, arguments)(Tree.DummyApp, N, joint)
        termSplit(rhss, finishInner)(fallback)
    // Handle operator splits.
    case tree @ OpSplit(lhs, rhss) => fallback => ctx =>
      nominate(ctx, finish(term(lhs)(using ctx))): vs =>
        rhss.foldRight(Function.const(fallback): Sequel): (branch, elabFallback) =>
          branch match
          case LetLike(Keywrd(`let`), pat, termTree, N) => ctx =>
            val ident = pat match // TODO handle patterns and rm special cases
              case ident: Ident => ident
              case und: Under => new Ident("_").withLocOf(und)
            termTree match
            case S(termTree) =>
              val sym = VarSymbol(ident)
              val fallbackCtx = ctx + (ident.name -> sym)
              Split.Let(sym, term(termTree)(using ctx), elabFallback(fallbackCtx))
          case PrefixApp(Keywrd(Keyword.`do`), computation) => ctx => trace(
            pre = s"termSplit: do $computation",
            post = (res: Split) => s"termSplit: do >>> $res"
          ):
            val sym = TempSymbol(N, "doTemp")
            Split.Let(sym, term(computation)(using ctx), elabFallback(ctx))
          case PrefixApp(Keywrd(Keyword.`else`), default) => ctx =>
            // TODO: report `rest` as unreachable
            Split.default(term(default)(using ctx))
          case rawRhs => ctx =>
            log(s"rawRhs: $rawRhs")
            val rhs = rawRhs.splitOn(Trm(vs.ref(/* FIXME ident? */)))
            log(s"rhs: $rhs")
            termSplit(rhs, identity)(elabFallback(ctx))(ctx)
    case _ => fallback => _ =>
      raise(ErrorReport(msg"Unrecognized term split (${tree.describe})." -> tree.toLoc :: Nil,
        extraInfo = S(tree)))
      fallback.withoutLoc // Hacky... a loc is always added for the result
  
  /** Given a elaborated scrutinee, give it a name and add it to the context.
   *  @param baseCtx the context to be extended with the new symbol
   *  @param scrutinee the elaborated scrutinee
   *  @param cont the continuation that needs the symbol and the context
   */
  def nominate(baseCtx: Ctx, scrutinee: Term, nameHint: Str = "scrut")
              (cont: BlockLocalSymbol => Sequel): Split = scrutinee match
    case ref @ Term.Ref(symbol: VarSymbol) =>
      val innerCtx = baseCtx + (ref.tree.name -> symbol)
      cont(symbol)(innerCtx)
    case _ =>
      val symbol = TempSymbol(N, nameHint)
      val innerCtx = baseCtx + (nameHint -> symbol)
      Split.Let(symbol, scrutinee, cont(symbol)(innerCtx))

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
  def disaggregate(tree: Tree): ::[(Tree, Tree)] = trace(
    pre = s"disaggregate <<< $tree", 
    post = (ms: ::[(Tree, Tree)]) =>
      s"disaggregate >>> ${ms.mkString(", ")}"
  ):
    type TT = (Tree, Tree)
    def go(tree: Tree, acc: TT => ::[TT]): () => ::[TT] = tree match
      case lhs `and` rhs  => go(lhs, ::(_, go(rhs, acc)()))
      case lhs `or` rhs   =>
        raise(ErrorReport(
          msg"Logical `or` is not yet supported." -> tree.toLoc :: Nil))
        go(lhs, ::(_, go(rhs, acc)())) // FIXME: this is currently copy-pasted from the `and` case
      case scrut `is` pat => () => acc((scrut, pat))
      case test           => () => acc((test, Tree.BoolLit(true)))
    go(tree, ::(_, Nil))()
  
  /** Desugar a _pattern split_ (PS) into a _split_ of core abstract syntax.
   *  The scrutinee has been already elaborated when this method is called.
   *  @param tree the `Tree` representing the pattern split
   *  @param scrutSymbol the symbol representing the elaborated scrutinee
   */
  def patternSplit(tree: Tree, scrutSymbol: BlockLocalSymbol): Split => Sequel =
    patternSplit(N, tree, scrutSymbol)
  
  /** Similar to `patternSplit`, but allows a transformation on the pattern head.
   *  @param transform the partial pattern before enter this pattern split
   */
  def patternSplit(
      finish: Opt[Tree => Tree],
      tree: Tree,
      scrutSymbol: BlockLocalSymbol
  ): Split => Sequel = tree match
    case blk: Block => blk.desugStmts.foldRight(default): (branch, elabFallback) =>
      // Terminology: _fallback_ refers to subsequent branches, _backup_ refers
      // to the backup plan passed from the parent split.
      branch.deparenthesized match
      case LetLike(Keywrd(`let`), ident @ Ident(_), termTree, N) => backup => ctx =>
        termTree match
        case S(termTree) =>
          val sym = VarSymbol(ident)
          val fallbackCtx = ctx + (ident.name -> sym)
          Split.Let(sym, term(termTree)(using ctx), elabFallback(backup)(fallbackCtx))
        case N =>
          raise(ErrorReport(msg"Pattern matching with `let` must have a term." -> branch.toLoc :: Nil))
          backup
      case PrefixApp(Keywrd(Keyword.`do`), computation) => fallback => ctx => trace(
        pre = s"patternSplit (do) <<< $computation",
        post = (res: Split) => s"patternSplit: else >>> $res"
      ):
        val sym = TempSymbol(N, "doTemp")
        Split.Let(sym, term(computation)(using ctx), elabFallback(fallback)(ctx))
      case PrefixApp(Keywrd(Keyword.`else`), body) => backup => ctx => trace(
        pre = s"patternSplit (else) <<< $tree",
        post = (res: Split) => s"patternSplit (else) >>> ${res.showDbg}"
      ):
        elabFallback(backup)(ctx) match
          case Split.End => ()
          case _ => raise(ErrorReport(msg"Any following branches are unreachable." -> branch.toLoc :: Nil))
        Split.default(term(body)(using ctx))
      case branch => backup => ctx => trace(
        pre = "patternSplit (alternative)",
        post = (res: Split) => s"patternSplit (alternative) >>> ${res.showDbg}"
      ):
        patternSplit(finish, branch, scrutSymbol)(elabFallback(backup)(ctx))(ctx)
    // For example, `Some of "A" then 0`, and
    // ```
    // Some of
    //   "A" then 0
    //   "B" then 1
    // ```
    // The precedence of `of` is higher than `then`.
    case app @ App(_: (Ident | Sel | SynthSel), Tup(branches)) =>
      patternSplit(S(tree => app.copy(rhs = Tup(tree :: Nil))), Block(branches), scrutSymbol)
        .traced(pre = s"patternSplit <<< partial pattern", post = (_) => s"patternSplit >>>")
    case patternAndMatches ~> consequent => fallback =>
      // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
      // Each match is represented by a pair of a _coda_ and a _pattern_
      // that is yet to be elaborated.
      val (headPattern, _) :: tail = disaggregate(patternAndMatches)
      val realPattern = finish match
        case N => headPattern
        case S(f) => f(headPattern)
      log(s"realPattern: $realPattern")
      // The `consequent` serves as the innermost split, based on which we
      // expand from the N-th to the second match.
      val tailSplit =
        val innermostSplit = consequent match
          case L(tree) => termSplit(tree, identity)(Split.End)
          case R(tree) => (ctx: Ctx) => Split.default(term(tree)(using ctx))
        tail.foldRight(innermostSplit):
          case ((coda, pat), sequel) => ctx =>
            nominate(ctx, term(coda)(using ctx)):
              expandMatch(_, pat, sequel, Nil)(Split.End)
        .traced(
          pre = s"conjunct matches <<< $tail",
          post = (res: Split) => s"conjunct matches >>> $res")
      expandMatch(scrutSymbol, realPattern, tailSplit, Nil)(fallback).traced(
        pre = s"patternBranch <<< $patternAndMatches -> ${consequent.fold(_.showDbg, _.showDbg)}",
        post = (res: Split) => s"patternBranch >>> ${res.showDbg}")
    case _ =>
      raise(ErrorReport(msg"Unrecognized pattern split (${tree.describe})." -> tree.toLoc :: Nil))
      _ => _ => Split.default(Term.Error)

  /** Elaborate a single match (a scrutinee and a pattern) and forms a split
   *  with an innermost split as the sequel of the match.
   *  @param scrutSymbol the symbol representing the scrutinee
   *  @param pattern the un-elaborated pattern
   *  @param sequel the innermost split
   *  @return a function that takes the tail of the split and a context
   */
  def expandMatch(scrutSymbol: BlockLocalSymbol, pattern: Tree, sequel: Sequel, output: Ls[VarSymbol]): Split => Sequel =
    def ref = scrutSymbol.ref(/* FIXME ident? */)
    def dealWithCtorCase(ctor: Ctor, mode: MatchMode)(fallback: Split): Sequel = ctx =>
      Branch(ref, FlatPattern.ClassLike(term(ctor), N, mode, false)(ctor, output), sequel(ctx)) ~: fallback
    def dealWithAppCtorCase(
        app: Tree, ctor: Ctor, args: Ls[Tree], mode: MatchMode
    )(fallback: Split): Sequel = ctx =>
      val scrutinees = scrutSymbol.getSubScrutinees(args.size)
      val matches = scrutinees.iterator.zip(args).map:
        case (symbol, tree) => tree match
          // We only elaborate arguments marked with `pattern` keyword. This is
          // due to a technical limitation that the desugarer generates flat
          // patterns on the fly and we don't know whether the argument should
          // be interpreted as a sub-pattern or a pattern argument. This can be
          // solved after we rewrite the desugarer using `Pattern`.
          case TypeDef(syntax.Pat, body, _) => Argument(symbol, elaborator.pattern(body))
          case _: Tree => Argument(symbol, tree)
      .toList
      Branch(
        ref,
        FlatPattern.ClassLike(term(ctor), S(matches), mode, false)(app, output), // TODO: refined?
        subMatches(matches, sequel)(Split.End)(ctx)
      ) ~: fallback
    pattern.deparenthesized.desugared match
      // A single wildcard pattern.
      case Under() => fallback => ctx => sequel(ctx) ++ fallback
      // Alias pattern
      case pat as (id: Ident) => fallback =>
        val aliasSymbol = VarSymbol(id)
        val inner = (ctx: Ctx) =>
          val ctxWithAlias = ctx + (id.name -> aliasSymbol)
          sequel(ctxWithAlias)
          // Split.Let(aliasSymbol, ref, sequel(ctxWithAlias))
        expandMatch(scrutSymbol, pat, inner, aliasSymbol :: output)(fallback)
      case id @ Ident(nme) if nme.headOption.forall(_.isLower) => fallback => ctx =>
        val aliasSymbol = VarSymbol(id)
        val ctxWithAlias = ctx + (nme -> aliasSymbol)
        // Not only bind the variable, but also bind the output symbols.
        Split.Let(aliasSymbol, ref, output.foldRight(sequel(ctxWithAlias) ++ fallback):
          case (symbol, innerSplit) => Split.Let(symbol, ref, innerSplit))
      case ctor: Ctor => dealWithCtorCase(ctor, MatchMode.Default)
      case Annotated(annotation, ctor: Ctor) =>
        dealWithCtorCase(ctor, MatchMode.Annotated(term(annotation)))
      case Tree.Tup(args) => fallback => ctx => trace(
        pre = s"expandMatch <<< ${args.mkString(", ")}",
        post = (r: Split) => s"expandMatch >>> ${r.showDbg}"
      ):
        // Break tuple into three parts:
        // 1. A fixed number of leading patterns.
        // 2. A variable number of middle patterns indicated by `..`.
        // 3. A fixed number of trailing patterns.
        val (lead, rest) = args.foldLeft[(Ls[Tree], Opt[(Keyword.Ellipsis, Opt[Tree], Ls[Tree])])]((Nil, N)):
          case ((lead, N), Spread(kw, patOpt)) => (lead, S((kw.kw, patOpt, Nil)))
          case ((lead, N), pat) => (lead :+ pat, N)
          case ((lead, S((kw: Keyword.Ellipsis, rest, last))), pat) => (lead, S((kw, rest, last :+ pat)))
        // `wrap`: add let bindings for tuple elements
        // `matches`: pairs of patterns and symbols to be elaborated
        val (wrapRest, restMatches) = rest match
          case S((kw, rest, last)) =>
            val (wrapLast, reversedLastMatches) = last.reverseIterator.zipWithIndex
              .foldLeft[(Split => Split, Ls[Argument.Term])]((identity, Nil)):
                case ((wrapInner, matches), (pat, lastIndex)) =>
                  val sym = scrutSymbol.getTupleLastSubScrutinee(lastIndex)
                  val wrap = (split: Split) =>
                    Split.Let(sym, callTupleGet(ref, -1 - lastIndex, sym), wrapInner(split))
                  (wrap, Argument(sym, pat) :: matches)
            val lastMatches = reversedLastMatches.reverse
            rest match
              case N => (wrapLast, lastMatches)
              case S(pat) =>
                val sym = TempSymbol(N, "rest")
                val wrap = (split: Split) =>
                  val arg0 = PlainFld(ref)
                  val arg1 = PlainFld(Term.Lit(IntLit(lead.length)))
                  val arg2 = PlainFld(Term.Lit(IntLit(BigInt(last.length))))
                  val args = Term.Tup(arg0 :: arg1 :: arg2 :: Nil)(DummyTup)
                  val func = kw match
                    case Keyword.`..` => tupleLazySlice
                    case Keyword.`...` => tupleSlice
                  val call = Term.App(func, args)(DummyApp, N, TempSymbol(N, "slice"))
                  Split.Let(sym, call, wrapLast(split))
                (wrap, Argument(sym, pat) :: lastMatches)
          case N => (identity: Split => Split, Nil)
        val (wrap, arguments) = lead.zipWithIndex.foldRight((wrapRest, restMatches)):
          case ((pat, i), (wrapInner, arguments)) =>
            val sym = scrutSymbol.getTupleLeadSubScrutinee(i)
            val wrap = (split: Split) =>
              // TODO: Changing from the following line in #318 breaks some LLIR difftests (marked :todo)
              // Split.Let(sym, Term.SynthSel(ref, Ident(s"$i"))(N), wrapInner(split))
              Split.Let(sym, callTupleGet(ref, i, sym), wrapInner(split))
            (wrap, Argument(sym, pat) :: arguments)
        Branch(
          ref,
          FlatPattern.Tuple(lead.length + rest.fold(0)(_._3.length), rest.isDefined)(output),
          // The outermost is a tuple, so pattern arguments are not possible.
          wrap(subMatches(arguments, sequel)(Split.End)(ctx))
        ) ~: fallback
      // Negative numeric literals
      case App(Ident("-"), Tup(IntLit(value) :: Nil)) => fallback => ctx =>
        Branch(ref, FlatPattern.Lit(IntLit(-value))(output), sequel(ctx)) ~: fallback
      case App(Ident("-"), Tup(DecLit(value) :: Nil)) => fallback => ctx =>
        Branch(ref, FlatPattern.Lit(DecLit(-value))(output), sequel(ctx)) ~: fallback
      case OpApp(lhs, Ident("&"), rhs :: Nil) => fallback => ctx =>
        val newSequel = expandMatch(scrutSymbol, rhs, sequel, output)(fallback)
        expandMatch(scrutSymbol, lhs, newSequel, output)(fallback)(ctx)
      case OpApp(lhs, Ident("|"), rhs :: Nil) => fallback => ctx =>
        val newFallback = expandMatch(scrutSymbol, rhs, sequel, output)(fallback)(ctx)
        expandMatch(scrutSymbol, lhs, sequel, output)(newFallback)(ctx)
      // A single constructor pattern.
      case Annotated(annotation, app @ App(ctor: Ctor, Tup(args))) =>
        dealWithAppCtorCase(app, ctor, args, MatchMode.Annotated(term(annotation)))
      case app @ App(ctor: Ctor, Tup(args)) =>
        dealWithAppCtorCase(app, ctor, args, MatchMode.Default)
      case app @ OpApp(lhs, ctor: Ctor, rhss) =>
        // TODO improve (eventually remove DummyApp)
        dealWithAppCtorCase(app, ctor, lhs :: rhss, MatchMode.Default)
      // A single literal pattern
      case literal: Literal => fallback => ctx => trace(
        pre = s"expandMatch: literal <<< $literal",
        post = (r: Split) => s"expandMatch: literal >>> ${r.showDbg}"
      ):
        Branch(ref, FlatPattern.Lit(literal)(output), sequel(ctx)) ~: fallback
      // A single pattern in conjunction with more conditions
      case pattern and consequent => fallback => ctx =>
        val innerSplit = termSplit(consequent, identity)(Split.End)
        expandMatch(scrutSymbol, pattern, innerSplit, output)(fallback)(ctx)
      case pattern where condition => fallback => ctx =>
        val sym = TempSymbol(N, "conditionTemp")
        val newSequel = expandMatch(sym, Tree.BoolLit(true), sequel, output)(fallback)
        val newNewSequel = (ctx: Ctx) => Split.Let(sym, term(condition)(using ctx), newSequel(ctx))
        expandMatch(scrutSymbol, pattern, newNewSequel, output)(fallback)(ctx)
      case Jux(Ident(".."), Ident(_)) => fallback => _ =>
        raise(ErrorReport(msg"Illegal rest pattern." -> pattern.toLoc :: Nil))
        fallback
      case InfixApp(StrLit(fieldName), Keyword.`:`, pat) => fallback => ctx =>
        val fieldIdent = (Ident(fieldName): Ident).withLocOf(pattern)
        val symbol = scrutSymbol.getFieldScrutinee(fieldIdent)
        Branch(
          ref,
          FlatPattern.Record((fieldIdent, symbol) :: Nil)(output),
          subMatches(Argument(symbol, pat) :: Nil, sequel)(Split.End)(ctx)
        ) ~: fallback
      case InfixApp(fieldName: Ident, Keyword.`:`, pat) => fallback => ctx =>
        val symbol = scrutSymbol.getFieldScrutinee(fieldName)
        Branch(
          ref,
          FlatPattern.Record((fieldName, symbol) :: Nil)(output),
          subMatches(Argument(symbol, pat) :: Nil, sequel)(Split.End)(ctx)
        ) ~: fallback
      case Pun(false, fieldName) => fallback => ctx =>
        val symbol = scrutSymbol.getFieldScrutinee(fieldName)
        Branch(
          ref,
          FlatPattern.Record((fieldName, symbol) :: Nil)(output),
          subMatches(Argument(symbol, fieldName) :: Nil, sequel)(Split.End)(ctx)
        ) ~: fallback
      case Block(st :: Nil) => fallback => ctx =>
        expandMatch(scrutSymbol, st, sequel, output)(fallback)(ctx)
      case Block(sts) => fallback => ctx => // we assume this is a record
        sts.foldRight[Option[List[(Tree.Ident, BlockLocalSymbol, Tree)]]](S(Nil)){
          // this collects the record parts, or fails if some statement does not correspond
          // to a record field
          case (_, N) => N // we only need to fail once to return N
          case (p, S(tl)) => p match
            case InfixApp(StrLit(fieldName), Keyword.`:`, pat) =>
              val fieldIdent = (Ident(fieldName): Ident).withLocOf(p)
              S((fieldIdent, scrutSymbol.getFieldScrutinee(fieldIdent), pat) :: tl)
            case InfixApp(fieldName: Ident, Keyword.`:`, pat) =>
              S((fieldName, scrutSymbol.getFieldScrutinee(fieldName), pat) :: tl)
            case Pun(false, fieldName) =>
              S((fieldName, scrutSymbol.getFieldScrutinee(fieldName), fieldName) :: tl)
            case p =>
              raise(ErrorReport(msg"invalid record field pattern" -> p.toLoc :: Nil))
              None
        }.fold(fallback)(recordContent =>
          Branch(
            ref,
            FlatPattern.Record(recordContent.map((fieldName, symbol, _) => (fieldName, symbol)))(output),
            subMatches(recordContent.map((_, symbol, pat) => Argument(symbol, pat)), sequel)(Split.End)(ctx)
          ) ~: fallback
        )
      case Bra(BracketKind.Curly | BracketKind.Round, inner) => fallback => ctx =>
        expandMatch(scrutSymbol, inner, sequel, output)(fallback)(ctx)
      case pattern => fallback => _ =>
        // Raise an error and discard `sequel`. Use `fallback` instead.
        raise(ErrorReport(msg"Unrecognized pattern (${pattern.describe})" -> pattern.toLoc :: Nil))
        fallback
  
  /** Desugar a list of sub-patterns (with their corresponding scrutinees).
   *  This is called when handling nested patterns. The caller is responsible
   *  for providing the symbols of scrutinees.
   * 
   *  @param matches a list of pairs consisting of a scrutinee and a pattern
   *  @param sequel the innermost split
   */
  def subMatches(matches: Ls[Argument],
                 sequel: Sequel): Split => Sequel = matches match
    case Nil => _ => ctx => trace(
      pre = s"subMatches (done) <<< Nil",
      post = (r: Split) => s"subMatches >>> ${r.showDbg}"
    ):
      sequel(ctx)
    case (Argument.Term(_, Under()) | Argument.Pattern(_, _)) :: rest =>
      subMatches(rest, sequel) // Skip pattern arguments and wildcards
    case Argument.Term(scrutinee, tree) :: rest => fallback => trace(
      pre = s"subMatches (nested) <<< $scrutinee is $tree",
      post = (r: Sequel) => s"subMatches (nested) >>>"
    ):
      val innermostSplit = subMatches(rest, sequel)(fallback)
      expandMatch(scrutinee, tree, innermostSplit, Nil)(fallback)
  
  /** Desugar `case` expressions. */
  def apply(tree: Case, scrut: VarSymbol)(using Ctx): Split =
    val topmost = patternSplit(tree.branches, scrut)(Split.End)(ctx)
    reportInconsistentConnectives(tree.kw)
    topmost ++ topmostDefault
  
  /** Desugar `if` and `while` expressions. */
  def apply(tree: IfLike)(using Ctx): Split =
    val topmost = termSplit(tree.split, identity)(Split.End)(ctx)
    reportInconsistentConnectives(tree.kw)
    topmost ++ topmostDefault
  
  /** Desugar `is` and `and` shorthands. */
  def apply(tree: InfixApp)(using Ctx): Split =
    termSplitShorthands(tree, identity)(Split.default(Term.Lit(Tree.BoolLit(false))))(ctx)
end Desugarer
