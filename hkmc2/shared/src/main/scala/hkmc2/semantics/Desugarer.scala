package hkmc2
package semantics

import syntax.{Keyword, Tree}, Tree.*
import mlscript.utils.*, shorthands.*
import Message.MessageContext
import utils.TraceLogger

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

  private def patternSplitShorthands(tree: Tree, scrutSymbol: VarSymbol): Split => Sequel = tree match
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
      branches.foldRight(default):
        case (Let(ident @ Ident(_), termTree, N), rest) => fallback => ctx => trace(
          pre = s"termSplit: let ${ident.name} = $termTree",
          post = (res: Split) => s"termSplit: let >>> $res"
        ):
          val sym = VarSymbol(ident, nextUid)
          val restCtx = ctx + (ident.name -> sym)
          Split.Let(sym, term(termTree)(using ctx), rest(fallback)(restCtx))
        case (Modified(Keyword.`else`, default), rest) => fallback => ctx => trace(
          pre = s"termSplit: else $default",
          post = (res: Split) => s"termSplit: else >>> $res"
        ):
          // TODO: report `rest` as unreachable
          Split.default(term(default)(using ctx))
        case (branch, rest) => fallback => ctx => trace(
          pre = s"termSplit: $branch",
          post = (res: Split) => s"termSplit >>> $res"
        ):
          termSplit(branch, finish)(rest(fallback)(ctx))(ctx)
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
          case L(tree) => termSplit(tree, identity)(fallback)
          case R(tree) => (ctx: Ctx) => Split.default(term(tree)(using ctx))
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
      val opRef = ctx.locals.get(opName).orElse(ctx.members.get(opName)) match
        case S(sym) => sym.ref(opIdent)
        case N =>
          raise(ErrorReport(msg"Name not found: $opName" -> tree.toLoc :: Nil))
          Term.Error
      // Elaborate and finish the LHS. Nominate the LHS if necessary.
      nominate(ctx, finish(term(lhs)(using ctx))): lhsSymbol =>
        // Compose a function that takes the RHS and finishes the application.
        val finishInner = (rhsTerm: Term) =>
          val first = Fld(FldFlags.empty, lhsSymbol.ref(lhsSymbol.id), N)
          val second = Fld(FldFlags.empty, rhsTerm, N)
          val arguments = Term.Tup(first :: second :: Nil)(rawTup)
          val joint = FlowSymbol("‹applied-result›", nextUid)
          Term.App(opRef, arguments)(tree, joint)
        termSplit(rhs, finishInner)(fallback)
    case tree @ App(lhs, blk @ OpBlock(opRhsApps)) => fallback => ctx =>
      nominate(ctx, finish(term(lhs)(using ctx))): vs =>
        val mkInnerFinish = (op: Term) => (rhsTerm: Term) =>
          val first = Fld(FldFlags.empty, vs.ref(vs.id), N)
          val second = Fld(FldFlags.empty, rhsTerm, N)
          val rawTup = Tup(lhs :: Nil): Tup // <-- loc might be wrong
          val arguments = Term.Tup(first :: second :: Nil)(rawTup)
          val joint = FlowSymbol("‹applied-result›", nextUid)
          Term.App(op, arguments)(tree, joint)
        opRhsApps.foldRight(Function.const(fallback): Sequel):
          case ((Tree.Empty(), Let(ident @ Ident(_), termTree, N)), rest) => ctx =>
            val sym = VarSymbol(ident, nextUid)
            val restCtx = ctx + (ident.name -> sym)
            Split.Let(sym, term(termTree)(using ctx), rest(restCtx))
          case ((Tree.Empty(), Modified(Keyword.`else`, default)), rest) => ctx =>
            // TODO: report `rest` as unreachable
            Split.default(term(default)(using ctx))
          case (((rawOp @ Ident(_)), rhs), rest) => ctx =>
            val op = term(rawOp)(using ctx)
            val innerFinish = mkInnerFinish(op)
            termSplit(rhs, innerFinish)(rest(ctx))(ctx)
          case ((op, rhs), rest) => ctx =>
            raise(ErrorReport(msg"Unrecognized operator branch." -> op.toLoc :: Nil))
            rest(ctx)
    case _ => _ => _ =>
      raise(ErrorReport(msg"Unrecognized term split." -> tree.toLoc :: Nil))
      Split.default(Term.Error)

  /** Given a elaborated scrutinee, give it a name and add it to the context.
   *  @param baseCtx the context to be extended with the new symbol
   *  @param scrutinee the elaborated scrutinee
   *  @param cont the continuation that needs the symbol and the context
   */
  def nominate(baseCtx: Ctx, scrutinee: Term)
              (cont: VarSymbol => Sequel): Split = scrutinee match
    case ref @ Term.Ref(symbol: VarSymbol) =>
      val innerCtx = baseCtx + (ref.tree.name -> symbol)
      cont(symbol)(innerCtx)
    case _ =>
      val ident = Ident("scrut"): Ident
      val symbol = VarSymbol(ident, nextUid)
      val innerCtx = baseCtx + (ident.name -> symbol)
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
  def patternSplit(tree: Tree, scrutSymbol: VarSymbol): Split => Sequel = tree match
    case Block(branches) =>
      branches.foldRight(default):
        case (Let(ident @ Ident(_), termTree, N), rest) => fallback => ctx =>
          val sym = VarSymbol(ident, nextUid)
          val restCtx = ctx + (ident.name -> sym)
          Split.Let(sym, term(termTree)(using ctx), rest(fallback)(restCtx))
        case (Modified(Keyword.`else`, default), rest) => fallback => ctx =>
          // TODO: report `rest` as unreachable
          Split.default(term(default)(using ctx))
        case (branch, rest) => fallback => ctx => trace(
          pre = "patternSplit (nested)",
          post = (res: Split) => s"patternSplit (nested) >>> ${res.showDbg}"
        ):
          patternSplit(branch, scrutSymbol)(rest(fallback)(ctx))(ctx)
    case patternAndMatches -> consequent => fallback =>
      trace(s"patternSplit: $patternAndMatches -> $consequent"):
        // There are N > 0 conjunct matches. We use `::[T]` instead of `List[T]`.
        // Each match is represented by a pair of a _coda_ and a _pattern_
        // that is yet to be elaborated.
        val (headPattern, _) :: tail = disaggregate(patternAndMatches)
        // The `consequent` serves as the innermost split, based on which we
        // expand from the N-th to the second match.
        lazy val tailSplit = trace(s"conjunct matches <<< $tail"):
          val innermostSplit = consequent match
            case L(tree) => termSplit(tree, identity)(fallback)
            case R(tree) => (ctx: Ctx) => Split.default(term(tree)(using ctx))
          tail.foldRight(innermostSplit):
            case ((coda, pat), sequel) => ctx =>
              nominate(ctx, term(coda)(using ctx)):
                expandMatch(_, pat, sequel)(fallback)
        expandMatch(scrutSymbol, headPattern, tailSplit)(fallback)
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
  def expandMatch(scrutSymbol: VarSymbol, pattern: Tree, sequel: Sequel): Split => Sequel =
    val ref = () => scrutSymbol.ref(scrutSymbol.id)
    pattern match
      case Ident("_") => _ => ctx => sequel(ctx)
      case ctor: Ident => fallback => ctx => ctx.members.get(ctor.name) match
        case S(sym: ClassSymbol) => // TODO: refined
          Branch(ref(), Pattern.Class(sym, N, false), sequel(ctx)) :: fallback
        case S(_: VarSymbol) | N =>
          // If the identifier refers to a variable or nothing, we interpret it
          // as a variable pattern.
          val aliasSymbol = VarSymbol(ctor, nextUid)
          val ctxWithAlias = ctx + (ctor.name -> aliasSymbol)
          Split.Let(aliasSymbol, ref(), sequel(ctxWithAlias))
        case S(_) =>
          // The user might try to match a symbol that is not matchable.
          raise(ErrorReport(msg"Unrecognized pattern." -> pattern.toLoc :: Nil))
          Split.default(Term.Error)
      case pat @ App(ctor: Ident, Tup(args)) => fallback => ctx => trace(
        pre = s"expandMatch <<< ${ctor.name}(${args.iterator.map(_.showDbg).mkString(", ")})",
        post = (r: Split) => s"expandMatch >>> ${r.showDbg}"
      ):
        ctx.members.get(ctor.name) match
          case S(sym: ClassSymbol) =>
            val params = args.zipWithIndex.map:
              (t, i) => VarSymbol(Ident(s"param$i"), nextUid)
            if params.length != args.length then
              val n = params.length.toString
              val m = args.length.toString
              raise(ErrorReport(msg"mismatched arity: expect $n, found $m" -> pat.toLoc :: Nil))
            Branch(
              ref(),
              Pattern.Class(sym, S(params), false), // TODO: refined?
              subMatches(params zip args, sequel)(Split.Nil)(ctx)
            ) :: fallback
          case _ =>
            raise(ErrorReport(msg"Unknown constructor `${ctor.name}`." -> ctor.toLoc :: Nil))
            Split.default(Term.Error)
      case pattern and consequent => fallback =>
        val innermostSplit: Sequel = ctx => termSplit(consequent, identity)(fallback)(ctx)
        ctx => expandMatch(scrutSymbol, pattern, innermostSplit)(fallback)(ctx)
      case test => fallback => ctx => trace(
        pre = s"expandMatch: test <<< $test",
        post = (r: Split) => s"expandMatch: test >>> ${r.showDbg}"
      ):
        Branch(
          scrutSymbol.ref(scrutSymbol.id),
          Pattern.LitPat(Tree.BoolLit(true)),
          sequel(ctx)
        ) :: fallback

  /** Desugar a list of sub-patterns (with their corresponding scrutinees).
   *  This is called when handling nested patterns. The caller is responsible
   *  for providing the symbols of scrutinees.
   */
  def subMatches(matches: Ls[(VarSymbol, Tree)],
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
