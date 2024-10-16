package hkmc2
package semantics

import syntax.{Keyword, Tree}, Tree.*
import mlscript.utils.*, shorthands.*
import Message.MessageContext
import utils.TraceLogger
import hkmc2.syntax.Literal

object Desugarer:
  object and:
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case InfixApp(lhs, Keyword.and, rhs) => S((lhs, rhs))
      case _ => N

  object is:
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case InfixApp(lhs, Keyword.is, rhs) => S((lhs, rhs))
      case _ => N

  object `then`:
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case InfixApp(lhs, Keyword.`then`, rhs) => S((lhs, rhs))
      case _ => N

  object `->`:
    infix def unapply(tree: Tree): Opt[(Tree, Tree \/ Tree)] = tree match
      case InfixApp(lhs, Keyword.and, rhs) => S((lhs, L(rhs)))
      case InfixApp(lhs, Keyword.`then`, rhs) => S((lhs, R(rhs)))
      case _ => N

  object `else`:
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case InfixApp(lhs, Keyword.`else`, rhs) => S((lhs, rhs))
      case _ => N
end Desugarer

class Desugarer(tl: TraceLogger, elaborator: Elaborator)(using raise: Raise, state: Elaborator.State):
  import Desugarer.*
  import Elaborator.Ctx
  import elaborator.term
  import state.nextUid
  import tl.*

  // We're working on composing continuations in the UCS translation.
  // The type of continuation is `Split => Ctx => Split`.
  // The first parameter represents the fallback split, which does not have
  // access to the bindings in the current match. The second parameter
  // represents the context with bindings in the current match.

  type Sequel = Ctx => Split

  extension (sequel: Sequel)
    def traced(pre: Str, post: Split => Str): Sequel =
      if doTrace then ctx => trace(pre, post)(sequel(ctx)) else sequel

  extension (split: Split)
    /** Concatenate two splits. */
    def ++(fallback: Split): Split =
      if fallback == Split.Nil then
        split
      else if split.isFull then
        raise:
          ErrorReport:
            msg"The following branches are unreachable." -> fallback.toLoc ::
            msg"Because the previous split is full." -> split.toLoc :: Nil
        split
      else (split match
        case Split.Cons(head, tail) => Split.Cons(head, tail ++ fallback)
        case Split.Let(name, term, tail) => Split.Let(name, term, tail ++ fallback)
        case Split.Else(_) /* impossible */ | Split.Nil => fallback)

  import collection.mutable.HashMap

  private val subScrutineeMap = HashMap.empty[BlockLocalSymbol, HashMap[ClassSymbol, List[BlockLocalSymbol]]]

  extension (symbol: BlockLocalSymbol)
    def getSubScrutinees(cls: ClassSymbol): List[BlockLocalSymbol] =
      subScrutineeMap.getOrElseUpdate(symbol, HashMap.empty).getOrElseUpdate(cls, {
        val arity = cls.defn.flatMap(_.paramsOpt.map(_.length)).getOrElse(0)
        (0 until arity).map(i => TempSymbol(nextUid, N, s"param$i")).toList
      })

  def default: Split => Sequel = split => _ => split

  /** Desugar UCS shorthands. */
  def shorthands(tree: Tree): Sequel = termSplitShorthands(tree, identity):
    Split.default(Term.Lit(Tree.BoolLit(false)))

  private def termSplitShorthands(tree: Tree, finish: Term => Term): Split => Sequel = tree match
    case Block(branches) => branches match
      case Nil => lastWords("encountered empty block")
      case branch :: rest => fallback => ctx =>
        if rest.nonEmpty then
          raise(ErrorReport(msg"only one branch is supported in shorthands" -> tree.toLoc :: Nil))
        termSplitShorthands(branch, finish)(fallback)(ctx)
    case coda is rhs => fallback => ctx =>
      nominate(ctx, finish(term(coda)(using ctx))):
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
              expandMatch(_, pat, sequel)(fallback)
      // We apply `finish` to the first coda and expand the first match.
      // Note that the scrutinee might be not an identifier.
      headCoda match
        case Ident("_") => tailSplit
        case _ => ctx => trace(
          pre = s"shorthands <<< $matches",
          post = (res: Split) => s"shorthands >>> $res"
        ):
          nominate(ctx, finish(term(headCoda)(using ctx))):
            expandMatch(_, headPattern, tailSplit)(fallback)

  private def patternSplitShorthands(tree: Tree, scrutSymbol: BlockLocalSymbol): Split => Sequel = tree match
    case Block(branches) => branches match
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
              expandMatch(_, pat, sequel)(fallback)
      expandMatch(scrutSymbol, headPattern, tailSplit)(fallback)

  /** Desugar a _term split_ (TS) into a _split_ of core abstract syntax.
   *  @param tree the tree representing the term split.
   *  @param finish the accumulated partial term to be the LHS or the scrutinee
   *  @return a continuation that takes subsequent splits as fallbacks and then
   *          accepts a context with additional bindings from the enclosing
   *          matches and splits
   */
  def termSplit(tree: Tree, finish: Term => Term): Split => Sequel = tree match
    case Block(branches) =>
      branches.foldRight(default): (t, elabFallback) =>
        t match
        case Let(ident @ Ident(_), termTree, N) => fallback => ctx => trace(
          pre = s"termSplit: let ${ident.name} = $termTree",
          post = (res: Split) => s"termSplit: let >>> $res"
        ):
          val sym = VarSymbol(ident, nextUid)
          val fallbackCtx = ctx + (ident.name -> sym)
          Split.Let(sym, term(termTree)(using ctx), elabFallback(fallback)(fallbackCtx)).withLocOf(t)
        case Modified(Keyword.`else`, elsLoc, default) => fallback => ctx => trace(
          pre = s"termSplit: else $default",
          post = (res: Split) => s"termSplit: else >>> $res"
        ):
          // TODO: report `rest` as unreachable
          Split.default(term(default)(using ctx)).withLocOf(t)
        case branch => fallback => ctx => trace(
          pre = s"termSplit: $branch",
          post = (res: Split) => s"termSplit >>> $res"
        ):
          termSplit(branch, finish)(elabFallback(fallback)(ctx))(ctx).withLocOf(t)
    case coda is rhs => fallback => ctx =>
      nominate(ctx, finish(term(coda)(using ctx))):
        patternSplit(rhs, _)(fallback)
    case matches -> consequent => fallback =>
      // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
      // Each match is represented by a pair of a _coda_ and a _pattern_
      // that is yet to be elaborated.
      val (headCoda, headPattern) :: tail = disaggregate(matches)
      // The `consequent` serves as the innermost split, based on which we
      // expand from the N-th to the second match.
      lazy val tailSplit =
        val innermostSplit = consequent match
          case L(tree) => termSplit(tree, identity)(Split.Nil)
          case R(tree) => (ctx: Ctx) => Split.default(term(tree)(using ctx))
        tail.foldRight(innermostSplit):
          case ((coda, pat), sequel) => ctx => trace(
            pre = s"conjunct matches <<< $tail",
            post = (res: Split) => s"conjunct matches >>> $res"
          ):
            nominate(ctx, term(coda)(using ctx)):
              expandMatch(_, pat, sequel)(Split.Nil)
      // We apply `finish` to the first coda and expand the first match.
      // Note that the scrutinee might be not an identifier.
      headCoda match
        case Ident("_") => tailSplit
        case _ => ctx => trace(
          pre = s"termBranch <<< $matches then $consequent",
          post = (res: Split) => s"termBranch >>> $res"
        ):
          nominate(ctx, finish(term(headCoda)(using ctx))):
            expandMatch(_, headPattern, tailSplit)(fallback)
    case tree @ App(opIdent @ Ident(opName), rawTup @ Tup(lhs :: rhs :: Nil)) => fallback => ctx => trace(
      pre = s"termSplit: after op <<< $opName",
      post = (res: Split) => s"termSplit: after op >>> $res"
    ):
      // Resolve the operator.
      val opRef =
        ctx.locals.get(opName).orElse(ctx.members.get(opName)) match
        case S(sym) => sym.ref(opIdent)
        case N =>
          raise(ErrorReport(msg"Name not found: $opName" -> tree.toLoc :: Nil))
          Term.Error
      .withLocOf(opIdent)
      // Elaborate and finish the LHS. Nominate the LHS if necessary.
      nominate(ctx, finish(term(lhs)(using ctx))): lhsSymbol =>
        // Compose a function that takes the RHS and finishes the application.
        val finishInner = (rhsTerm: Term) =>
          val first = Fld(FldFlags.empty, lhsSymbol.ref(/* FIXME ident? */), N)
          val second = Fld(FldFlags.empty, rhsTerm, N)
          val arguments = Term.Tup(first :: second :: Nil)(rawTup)
          val joint = FlowSymbol("‹applied-result›", nextUid)
          Term.App(opRef, arguments)(tree, joint)
        termSplit(rhs, finishInner)(fallback)
    case tree @ App(lhs, blk @ OpBlock(opRhsApps)) => fallback => ctx =>
      nominate(ctx, finish(term(lhs)(using ctx))): vs =>
        val mkInnerFinish = (op: Term) => (rhsTerm: Term) =>
          val first = Fld(FldFlags.empty, vs.ref(/* FIXME ident? */), N)
          val second = Fld(FldFlags.empty, rhsTerm, N)
          val rawTup = Tup(lhs :: Nil): Tup // <-- loc might be wrong
          val arguments = Term.Tup(first :: second :: Nil)(rawTup)
          val joint = FlowSymbol("‹applied-result›", nextUid)
          Term.App(op, arguments)(tree, joint)
        opRhsApps.foldRight(Function.const(fallback): Sequel): (tt, elabFallback) =>
          tt match
          case (Tree.Empty(), Let(ident @ Ident(_), termTree, N)) => ctx =>
            val sym = VarSymbol(ident, nextUid)
            val fallbackCtx = ctx + (ident.name -> sym)
            Split.Let(sym, term(termTree)(using ctx), elabFallback(fallbackCtx))
          case (Tree.Empty(), Modified(Keyword.`else`, elsLoc, default)) => ctx =>
            // TODO: report `rest` as unreachable
            Split.default(term(default)(using ctx))
          case ((rawOp @ Ident(_)), rhs) => ctx =>
            val op = term(rawOp)(using ctx)
            val innerFinish = mkInnerFinish(op)
            termSplit(rhs, innerFinish)(elabFallback(ctx))(ctx)
          case (op, rhs) => ctx =>
            raise(ErrorReport(msg"Unrecognized operator branch." -> op.toLoc :: Nil))
            elabFallback(ctx)
    case _ => fallback => _ =>
      raise(ErrorReport(msg"Unrecognized term split." -> tree.toLoc :: Nil))
      fallback

  /** Given a elaborated scrutinee, give it a name and add it to the context.
   *  @param baseCtx the context to be extended with the new symbol
   *  @param scrutinee the elaborated scrutinee
   *  @param cont the continuation that needs the symbol and the context
   */
  def nominate(baseCtx: Ctx, scrutinee: Term)
              (cont: BlockLocalSymbol => Sequel): Split = scrutinee match
    case ref @ Term.Ref(symbol: VarSymbol) =>
      val innerCtx = baseCtx + (ref.tree.name -> symbol)
      cont(symbol)(innerCtx)
    case _ =>
      val name = "scrut"
      val symbol = TempSymbol(nextUid, N, name)
      val innerCtx = baseCtx + (name -> symbol)
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
      case lhs and rhs  => go(lhs, ::(_, go(rhs, acc)()))
      case scrut is pat => () => acc((scrut, pat))
      case test         => () => acc((test, Tree.BoolLit(true)))
    go(tree, ::(_, Nil))()

  /** Desugar a _pattern split_ (PS) into a _split_ of core abstract syntax.
   *  The scrutinee has been already elaborated when this method is called.
   *  @param tree the `Tree` representing the pattern split
   *  @param scrutSymbol the symbol representing the elaborated scrutinee
   */
  def patternSplit(tree: Tree, scrutSymbol: BlockLocalSymbol): Split => Sequel = tree match
    case Block(branches) => branches.foldRight(default): (branch, elabFallback) =>
      // Terminology: _fallback_ refers to subsequent branches, _backup_ refers
      // to the backup plan passed from the parent split.
      branch match
      case Let(ident @ Ident(_), termTree, N) => backup => ctx =>
        val sym = VarSymbol(ident, nextUid)
        val fallbackCtx = ctx + (ident.name -> sym)
        Split.Let(sym, term(termTree)(using ctx), elabFallback(backup)(fallbackCtx))
      case Modified(Keyword.`else`, elsLoc, body) => backup => ctx => trace(
        pre = s"patternSplit (else) <<< $tree",
        post = (res: Split) => s"patternSplit (else) >>> ${res.showDbg}"
      ):
        elabFallback(backup)(ctx) match
          case Split.Nil => ()
          case _ => raise(ErrorReport(msg"Any following branches are unreachable." -> branch.toLoc :: Nil))
        Split.default(term(body)(using ctx))
      case branch => backup => ctx => trace(
        pre = "patternSplit (alternative)",
        post = (res: Split) => s"patternSplit (alternative) >>> ${res.showDbg}"
      ):
        patternSplit(branch, scrutSymbol)(elabFallback(backup)(ctx))(ctx)
    case patternAndMatches -> consequent => fallback =>
      // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
      // Each match is represented by a pair of a _coda_ and a _pattern_
      // that is yet to be elaborated.
      val (headPattern, _) :: tail = disaggregate(patternAndMatches)
      // The `consequent` serves as the innermost split, based on which we
      // expand from the N-th to the second match.
      val tailSplit =
        val innermostSplit = consequent match
          case L(tree) => termSplit(tree, identity)(Split.Nil)
          case R(tree) => (ctx: Ctx) => Split.default(term(tree)(using ctx))
        tail.foldRight(innermostSplit):
          case ((coda, pat), sequel) => ctx =>
            nominate(ctx, term(coda)(using ctx)):
              expandMatch(_, pat, sequel)(Split.Nil)
        .traced(
          pre = s"conjunct matches <<< $tail",
          post = (res: Split) => s"conjunct matches >>> $res")
      expandMatch(scrutSymbol, headPattern, tailSplit)(fallback).traced(
        pre = s"patternBranch <<< $patternAndMatches -> ${consequent.fold(_.showDbg, _.showDbg)}",
        post = (res: Split) => s"patternBranch >>> ${res.showDbg}")
    case _ =>
      raise(ErrorReport(msg"Unrecognized pattern split." -> tree.toLoc :: Nil))
      _ => _ => Split.default(Term.Error)

  /** Elaborate a single match (a scrutinee and a pattern) and forms a split
   *  with an innermost split as the sequel of the match.
   *  @param scrutSymbol the symbol representing the scrutinee
   *  @param pattern the un-elaborated pattern
   *  @param sequel the innermost split
   *  @return a function that takes the tail of the split and a context
   */
  def expandMatch(scrutSymbol: BlockLocalSymbol, pattern: Tree, sequel: Sequel): Split => Sequel =
    val ref = () => scrutSymbol.ref(/* FIXME ident? */)
    pattern match
      // A single wildcard pattern.
      case Ident("_") => _ => ctx => sequel(ctx)
      // A single variable pattern or constructor pattern without parameters.
      case ctor: Ident => fallback => ctx => ctx.members.get(ctor.name) match
        case S(sym: ClassSymbol) => // TODO: refined
          Branch(ref(), Pattern.Class(sym, N, false)(ctor), sequel(ctx)) :: fallback
        case S(_: VarSymbol) | N =>
          // If the identifier refers to a variable or nothing, we interpret it
          // as a variable pattern. If `fallback` is not used when `sequel`
          // is full, then we raise an error.
          val aliasSymbol = VarSymbol(ctor, nextUid)
          val ctxWithAlias = ctx + (ctor.name -> aliasSymbol)
          Split.Let(aliasSymbol, ref(), sequel(ctxWithAlias) ++ fallback)
        case S(_) =>
          // Raise an error and discard `sequel`. Use `fallback` instead.
          raise(ErrorReport(msg"Unknown symbol `${ctor.name}`." -> ctor.toLoc :: Nil))
          fallback
      // A single constructor pattern.
      case pat @ App(ctor: Ident, Tup(args)) => fallback => ctx => trace(
        pre = s"expandMatch <<< ${ctor.name}(${args.iterator.map(_.showDbg).mkString(", ")})",
        post = (r: Split) => s"expandMatch >>> ${r.showDbg}"
      ):
        ctx.members.get(ctor.name) match
          case S(cls: ClassSymbol) =>
            val arity = cls.defn.flatMap(_.paramsOpt.map(_.length)).getOrElse(0)
            if args.length =/= arity then
              val n = arity.toString
              val m = args.length.toString
              raise(ErrorReport(msg"mismatched arity: expect $n, found $m" -> pat.toLoc :: Nil))
            val params = scrutSymbol.getSubScrutinees(cls)
            val clsRef = cls.ref(ctor)
            Branch(
              ref(),
              Pattern.Class(cls, S(params), false)(ctor), // TODO: refined?
              subMatches(params zip args, sequel)(Split.Nil)(ctx)
            ) :: fallback
          case _ =>
            // Raise an error and discard `sequel`. Use `fallback` instead.
            raise(ErrorReport(msg"Unknown constructor `${ctor.name}`." -> ctor.toLoc :: Nil))
            fallback
      // A single literal pattern
      case literal: Literal => fallback => ctx => trace(
        pre = s"expandMatch: literal <<< $literal",
        post = (r: Split) => s"expandMatch: literal >>> ${r.showDbg}"
      ):
        Branch(ref(), Pattern.LitPat(literal), sequel(ctx)) :: fallback
      // A single pattern in conjunction with more conditions
      case pattern and consequent => fallback => ctx => 
        val innerSplit = termSplit(consequent, identity)(Split.Nil)
        expandMatch(scrutSymbol, pattern, innerSplit)(fallback)(ctx)
      case _ => fallback => _ =>
        // Raise an error and discard `sequel`. Use `fallback` instead.
        raise(ErrorReport(msg"Unrecognized pattern." -> pattern.toLoc :: Nil))
        fallback

  /** Desugar a list of sub-patterns (with their corresponding scrutinees).
   *  This is called when handling nested patterns. The caller is responsible
   *  for providing the symbols of scrutinees.
   */
  def subMatches(matches: Ls[(BlockLocalSymbol, Tree)],
                 sequel: Sequel): Split => Sequel = matches match
    case Nil => _ => ctx => trace(
      pre = s"subMatches (done) <<< Nil",
      post = (r: Split) => s"subMatches >>> ${r.showDbg}"
    ):
      sequel(ctx)
    case (_, Ident("_")) :: rest => subMatches(rest, sequel)
    case (scrutinee, pattern) :: rest => fallback => trace(
      pre = s"subMatches (nested) <<< $scrutinee is $pattern",
      post = (r: Sequel) => s"subMatches (nested) >>>"
    ):
      val innermostSplit = subMatches(rest, sequel)(fallback)
      expandMatch(scrutinee, pattern, innermostSplit)(fallback)
end Desugarer
