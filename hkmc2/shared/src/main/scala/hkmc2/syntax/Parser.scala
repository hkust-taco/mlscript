package hkmc2
package syntax

import scala.util.boundary
import sourcecode.{Name, Line}
import hkmc2.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._

import Tree.*
import Parser.*
import scala.annotation.tailrec

import Keyword.`let`
import hkmc2.syntax.Keyword.Ellipsis

import semantics.Elaborator.State


val charPrecList: List[Str] = List(
    "", // `of` rhs
    ",",
    // ^ for keywords
    ";",
    // "=", // higher than || means `a == 1 || b` parses surprisingly
    "@",
    ":",
    "|",
    "&",
    "=",
    // "/ \\",
    "^",
    // "= !",
    "!",
    "< >",
    "+ -",
    "* / %",
    "~",
    "", // Precedence of prefix operators
    "", // Precedence of application
    "", // Precedence of `new`
    // ".",
    ". \\",
  )


object Parser:
  
  type TokLoc = (Stroken, Loc)
  
  type LTL = Ls[TokLoc]
  
  private val MinPrec = 0
  private val NoElsePrec = MinPrec + 1
  
  def verbose =
    // true
    false
  
  private val precOf: Map[Char,Int] =
    charPrecList.zipWithIndex.flatMap {
      case (cs, i) => cs.filterNot(_ === ' ').map(_ -> (i + Keyword.maxPrec.get))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  // * Note: keywords without a specified right precedence are now assumed to have right precedence `CommaPrecNext`
  
  // private val CommaPrec = prec(',')
  private val CommaPrec = 0
  private val CommaPrecNext = CommaPrec + 1
  private val CommaPrecNext2 = CommaPrecNext + 1
  private val SelPrec = precOf('.')
  private val AppPrec = SelPrec - 1
  private val PrefixOpsPrec = AppPrec - 1
  // * Annotation body precedence: above all keyword infix ops (like `as`, `is`)
  // * but below character-based operators (like `+`, `;`).
  private val AnnotBodyPrec = Keyword.maxPrec.get + 1
  
  final def opCharPrec(opChar: Char): Int = precOf(opChar)
  final def opPrec(opStr: Str): (Int, Int) = opStr match
    case "+." | "-." | "*." =>
      (precOf(opStr.head), precOf(opStr.head))
    case _ if opStr.exists(_.isLetter) =>
      (Keyword.maxPrec.get, Keyword.maxPrec.get)
    case _ =>
      val r = opStr.last
      (precOf(opStr.head), precOf(r) - (if r === ',' || r === ':' then 1 else 0))
  val prefixOps: Set[Str] = Set("!", "+", "-", "~", "@", "|", "&")
  
  type Indent_Curly = Curly.type | Indent.type
  
  type NEWLINE_COMMA = NEWLINE.type | COMMA.type
  
  object KEYWORD:
    def unapply(t: IDENT): Opt[Keyword] = t match
      case IDENT(nme, sym) => Keyword.all.get(nme)
      // case IDENT(nme, sym) => Keyword.all.get(nme).map(_.name)
      // case IDENT(nme, sym) if Keyword.all.contains(nme) => S(nme)
  
  object OP:
    def unapply(t: IDENT): Opt[Str] = t match
      case IDENT(nme, true) if !Keyword.all.contains(nme) => S(nme)
      case _ => N
  
  object ALPHA:
    def unapply(t: Token): Opt[Str] = t match
      case IDENT(nme, false) if !Keyword.all.contains(nme) => S(nme)
      case _ => N
  
  object NOISE:
    def get(ts: Ls[TokLoc]): Ls[TokLoc] = ts match
      case (SPACE, _) :: rest => get(rest)
      case (COMMENT(_), _) :: rest => get(rest)
      case (NEWLINE, _) :: (COMMENT(_), _) :: rest => get(rest)
      case (BRACKETS(Indent, NOISE(Nil)), _) :: rest => get(rest)
      case _ => ts
    def unapply(ts: Ls[TokLoc]): S[Ls[TokLoc]] =
      S(get(ts))
  
  extension (loc: Loc)
    def showStart: String =
      loc.origin.fph.getLineColAt(loc.spanStart) match
        case (ln, _, col) => s"Ln $ln Col $col"
    def showEnd: String =
      loc.origin.fph.getLineColAt(loc.spanStart) match
        case (ln, _, col) => s"Ln $ln Col $col"
  
  extension (trees: Ls[Tree])
    /** Note that the innermost annotation is the leftmost. */
    def annotate(tree: Tree): Tree = trees.foldLeft(tree):
      case (target, annotation) => Annotated(annotation, target)
  
end Parser
import Parser._

abstract class Parser(
  origin: Origin,
  tokens: Ls[TokLoc],
  rules: ParseRules,
  raiseFun: Diagnostic => Unit,
  val dbg: Bool,
  // fallbackLoc: Opt[Loc], description: Str = "input",
)(using State):
  outer =>
  
  import rules.*
  
  object PrefixRule:
    def unapply(t: IDENT): Opt[(Keyword, ParseRule[Tree])] = t match
      // * the Loc of this Keywrd is added at the call site
      case KEYWORD(kw) => prefixRules.getKwAlt(kw, N).map: subRule =>
        kw -> subRule
      case _ => N
  
  protected def doPrintDbg(msg: => Str): Unit
  protected def printDbg(msg: => Any): Unit =
    doPrintDbg("│ " * this.indent + msg)
  
  protected var indent = 0
  private var _cur: Ls[TokLoc] = preprocessTokens(tokens)
  
  private def preprocessTokens(tokens: Ls[TokLoc]): Ls[TokLoc] = tokens match
    case (IDENT("new", false), l1) :: (IDENT("!", true), l2) :: rest =>
      (IDENT("new!", false), l1 ++ l2) :: preprocessTokens(rest)
    case (IDENT("yield", false), l1) :: (IDENT("*", true), l2) :: rest =>
      (IDENT("yield*", false), l1 ++ l2) :: preprocessTokens(rest)
    // * Remove empty indented sections
    case (BRACKETS(Indent, toks), _) :: rest
    if toks.forall:
      case (NEWLINE | SPACE, _) => true
      case _ => false
    =>
      preprocessTokens(rest)
    // * Expands end-of-line suspensions that introduce implied indentation,
    // * skipping NOISE tokens between `...` and NEWLINE (eg `... // hello\n body`)
    // * Note: using `NEWLINE_COMMA` instead of `NEWLINE` causes misparsing of things like `fun foo(..., ...)`
    case (SUSPENSION(true), l0) :: NOISE((NEWLINE, l1) :: rest) =>
      val outerLoc = l0.left ++ rest.lastOption.map(_._2.right)
      val innerLoc = l1.right ++ rest.lastOption.map(_._2.left)
      BRACKETS(Indent, preprocessTokens(rest))(innerLoc) -> outerLoc :: Nil
    case tl :: rest =>
      val rest2 = preprocessTokens(rest)
      if rest2 is rest then tokens
      else tl :: rest2
    case Nil => tokens
  
  private def wrap[R](args: => Any)(using l: Line, n: Name)(mkRes: => R): R =
    printDbg(s"@ ${n.value}${args match {
      case it: Iterable[_] => it.mkString("(", ",", ")")
      case _: Product => args
      case _ => s"($args)"
    }}    [at syntax/Parser.scala:${l.value}]")
    val res = try
      indent += 1
      mkRes
    finally indent -= 1
    printDbg(s"= $res")
    res
  
  final def rec(tokens: Ls[Stroken -> Loc], fallbackLoc: Opt[Loc], description: Str): Parser =
    new Parser(origin, tokens, rules, raiseFun, dbg
        // , fallbackLoc, description
    ):
      def doPrintDbg(msg: => Str): Unit = outer.printDbg("> " + msg)
  
  def resetCur(newCur: Ls[TokLoc]): Unit =
    _cur = newCur
    // _modifiersCache = ModifierSet.empty
  
  private lazy val lastLoc =
    tokens.lastOption.map(_._2.right)//.orElse(fallbackLoc)
  
  private def summarizeCur =
    Lexer.printTokens(_cur.take(5)) + (if _cur.sizeIs > 5 then "..." else "")
  
  
  private def cur(implicit l: Line, n: Name) =
    if dbg then printDbg(s"? ${n.value}\t\tinspects ${summarizeCur}    [at syntax/Parser.scala:${l.value}]")
    while !_cur.isEmpty && (_cur.head._1 match {
      case COMMENT(_) => true
      case _ => false
    }) do consume
    _cur
  
  private def cur_=(using l: Line, n: Name)(newCur: Ls[TokLoc]) =
    if dbg then printDbg(s"! ${n.value}\t\tresets ${Lexer.printTokens(newCur)}    [at syntax/Parser.scala:${l.value}]")
    _cur = newCur
  
  final def consume(implicit l: Line, n: Name): Unit =
    if dbg then printDbg(s"! ${n.value}\t\tconsumes ${Lexer.printTokens(_cur.take(1))}    [at syntax/Parser.scala:${l.value}]")
    resetCur(_cur.tailOption.getOrElse(Nil)) // FIXME throw error if empty?
  
  private def yeetSpaces(using Line, Name): Ls[TokLoc] =
    _cur = NOISE.get(_cur)
    _cur
  
  
  // final def raise(mkDiag: => Diagnostic)(implicit fe: FoundErr = false): Unit =
  //   if (!foundErr) raiseFun(mkDiag)
  final def raise(mkDiag: => Diagnostic): Unit =
    raiseFun(mkDiag)
  
  private def errExpr =
    Tree.Error().withLoc(cur.headOption.fold(lastLoc)(_._2 |> some))
  private def empty =
    Tree.Empty().withLoc(cur.headOption.fold(lastLoc)(_._2.left |> some))
  
  final def err(msgs: Ls[Message -> Opt[Loc]])(implicit l: Line, n: Name): Unit =
    printDbg(s"Error    [at syntax/Parser.scala:${l.value}]")
    raise(ErrorReport(msgs, source = Diagnostic.Source.Parsing))
  
  
  final def parseAll[R](parser: => R): R =
    val res = parser
    cur match
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        err(msg"Expected end of input; found ${relevantToken.describe} instead" -> S(rl) :: Nil)
      case Nil => ()
    res
  
  
  final def concludeWith[R](using l: Line)(f: this.type => R): R =
    wrap(())(concludeWithImpl(f))
  
  final def concludeWithImpl[R](f: this.type => R): R =
    val res = f(this)
    cur.dropWhile(tk => (tk._1 === SPACE || tk._1 === NEWLINE) && { consume; true }) match
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        err(msg"Unexpected ${relevantToken.describe} here" -> S(rl) :: Nil)
      case Nil => ()
    printDbg(s"Concluded with $res")
    res
  
  final def continueWith[R](f: this.type => R): (R, Ls[TokLoc]) =
    val res = f(this)
    val rest = cur.dropWhile(tk => (tk._1 === SPACE || tk._1 === NEWLINE) && { consume; true })
    printDbg(s"Continued with $res, $rest")
    (res, rest)
  
  
  final def maybeIndented[R](f: (Parser, Bool) => R): R =
    yeetSpaces match
      case (_: NEWLINE_COMMA, l0) :: _ =>
        consume
        while yeetSpaces.headOption.exists(_._1 === NEWLINE) do consume
        cur match
        case Nil =>
        case (tok, loc) :: _ =>
          raise(WarningReport(
            msg"This ${tok.describe} should be indented" -> S(loc) :: 
            msg"since it is a continuation of the new line here" -> S(l0) :: 
            Nil))
        maybeIndented(f)
      // case (br @ BRACKETS(Indent | Curly, toks), _) :: _ =>
      // * Note: not accepting Curly braces here, so as to allow things like `foo({X}, Y)` to parse
      case (br @ BRACKETS(Indent, toks), _) :: _ =>
        consume
        rec(toks, S(br.innerLoc), br.describe).concludeWith(f(_, true))
      case _ => f(this, false)
  
  final def blockMaybeIndented: Ls[Tree] =
    maybeIndented((p, i) => p.block(allowNewlines = i))
  
  
  /* Note on annotation parsing:
      There is currently an inconsistency when parsing annotations that start blocks,
      where the annotatee is parsed with no precedence (because this is done by `block`),
      so that `@Test 2 as Int` at the top level parses as `@Test (2 as Int)`;
      but within a subexpression, it is parsed with precendence AnnotBodyPrec,
      so that, eg, `x is @compile P() as y` parses correctly...
  */
  def annot(id: Ident): Tree =
    val pre = exprCont(id, SelPrec, allowNewlines = false, gobbleSpaces = false)
    cur match
    case (br @ BRACKETS(Round, toks), loc) :: _ =>
      consume
      val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
      App(pre, Tup(as).withLoc(S(loc)))
    case _ => pre
  
  
  def block(allowNewlines: Bool)(using Line): Ls[Tree] = blockOf(prefixRules, Nil, allowNewlines)
  
  def blockOf(rule: ParseRule[Tree], annotations: Ls[Tree], allowNewlines: Bool)(using Line): Ls[Tree] =
    wrap(rule.name, s"allowNewlines = $allowNewlines")(blockOfImpl(rule, annotations, allowNewlines))
  def blockOfImpl(rule: ParseRule[Tree], annotations: Ls[Tree], allowNewlines: Bool): Ls[Tree] =
    def blockContOf(rule: ParseRule[Tree], annotations: Ls[Tree] = Nil): Ls[Tree] =
      yeetSpaces match
        case (COMMA, _) :: _ => consume; blockOf(rule, annotations, allowNewlines)
        case (NEWLINE, _) :: _ if allowNewlines => consume; blockOf(rule, annotations, allowNewlines)
        case _ => Nil
    cur match
    case Nil => Nil
    case (NEWLINE, _) :: _ if allowNewlines => consume; blockOf(rule, annotations, allowNewlines)
    case (COMMA, _) :: _ => consume; blockOf(rule, annotations, allowNewlines)
    case (SPACE, _) :: _ => consume; blockOf(rule, annotations, allowNewlines)
    case (br @ BRACKETS(Indent, toks), _) :: _ =>
      // * Handle indented blocks appearing after comma continuations
      // * (e.g., in multi-line function calls like `tuple(1,\n  2)`)
      consume
      rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockOf(rule, annotations, true)) ++ blockContOf(rule)
    case (IDENT("@", _), l0) :: (IDENT(id, false), l1) :: _ =>
      consume
      consume
      val a = annot(new Ident(id).withLoc(S(l0 ++ l1)))
      yeetSpaces match
      case Nil =>
        err(
          msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}" -> a.toLoc.map(_.right)
          :: msg"found a lone annotation instead" -> a.toLoc
          :: Nil
        )
        errExpr :: Nil
      case _ =>
        blockOf(rule, a :: annotations, allowNewlines = allowNewlines)
    case (tok @ (id: IDENT), loc) :: _ if id.name =/= ":" =>
      Keyword.all.get(id.name) match
      case S(kw) =>
        consume
        rule.getKwAlt(kw, S(loc)) match
        case S(subRule) =>
          yeetSpaces match
          case (tok @ BRACKETS(_: Indent_Curly, toks), loc) :: _ if subRule.blkAlt.isEmpty =>
            consume
            val blk = rec(toks, S(tok.innerLoc), tok.describe).concludeWith(_.blockOf(subRule, Nil, allowNewlines)) // FIXME allowNewlines?
            if blk.isEmpty then
              err(msg"Expected ${subRule.whatComesAfter} ${subRule.mkAfterStr}; found end of block instead" -> S(loc) :: Nil)
              errExpr
            blk.map(annotations.annotate) ::: blockContOf(rule)
          case _ =>
            val p = kw.rightPrec.getOrElse(CommaPrecNext)
            val res = parseRule(p, subRule, allowNewlines = allowNewlines).getOrElse(errExpr)
            annotations.annotate(exprCont(res, CommaPrecNext, allowNewlines = allowNewlines)) :: blockContOf(rule)
        case N =>
          
          // TODO dedup this common-looking logic:
          
          rule.exprAlt match
          case S(exprAlt) =>
            yeetSpaces match
            case (tok @ BRACKETS(_: Indent_Curly, toks), loc) :: _ =>
              consume
              prefixRules.getKwAlt(kw, S(loc)) match
              case S(subRule) if subRule.blkAlt.isEmpty =>
                rec(toks, S(tok.innerLoc), tok.describe).concludeWith { p =>
                  p.blockOf(subRule.map(e => parseRule(CommaPrecNext, exprAlt.rest, allowNewlines = allowNewlines).map(res => exprAlt.k(e, res)).getOrElse(errExpr)), annotations, allowNewlines)
                } ++ blockContOf(rule)
              case _ =>
                TODO(cur)
            case _ =>
              prefixRules.getKwAlt(kw, S(loc)) match
              case S(subRule) =>
                val e = exprCont(parseRule(CommaPrecNext, subRule, allowNewlines = allowNewlines)
                  .getOrElse(errExpr), CommaPrecNext, allowNewlines = allowNewlines)
                annotations.annotate(parseRule(CommaPrecNext, exprAlt.rest, allowNewlines = allowNewlines).map(res => exprAlt.k(e, res)).getOrElse(errExpr)) :: blockContOf(rule)
              case N =>
                // TODO dedup?
                err(msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> S(loc) :: Nil)
                annotations.annotate(errExpr) :: blockContOf(rule)
          case N =>
            err(msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> S(loc) :: Nil)
            annotations.annotate(errExpr) :: blockContOf(rule)
      case N =>
        val lhs = tryParseExp(CommaPrecNext, tok, loc, rule, allowNewlines = allowNewlines).getOrElse(errExpr)
        cur match
        case (KEYWORD(kw @ (Keyword.`=`)), l0) :: _ /* if kw.leftPrecOrMin > prec */ =>
          consume
          val rhs = expr(CommaPrecNext, allowNewlines = allowNewlines)
          Def(lhs, rhs) :: blockContOf(rule)
        case _ =>
          annotations.annotate(lhs) :: blockContOf(rule)
    case (tok, loc) :: _ =>
      annotations.annotate(
        tryParseExp(CommaPrecNext, tok, loc, rule, allowNewlines = allowNewlines).getOrElse(errExpr)
      ) :: blockContOf(rule)
  
  
  private def tryParseExp[A](prec: Int, tok: Token, loc: Loc, rule: ParseRule[A], allowNewlines: Bool): Opt[A] =
    rule.exprAlt match
      case S(exprAlt) =>
        val e = simpleExpr(prec, allowNewlines = allowNewlines)
        if verbose then printDbg("$ proceed with rule: " + exprAlt)
        parseRule(prec, exprAlt.rest, allowNewlines = allowNewlines).map(res => exprAlt.k(e, res))
      case N =>
        rule.emptyAlt match
        case S(res) =>
          S(res())
        case N =>
          err(msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> S(loc) :: Nil)
          N
  
  
  /** A result of None means there was an error (already reported) and nothing could be parsed. */
  def parseRule[A](prec: Int, rule: ParseRule[A], allowNewlines: Bool)(using Line): Opt[A] =
    wrap(prec, rule, s"allowNewlines = $allowNewlines")(parseRuleImpl(prec, rule, allowNewlines = allowNewlines))
  def parseRuleImpl[A](prec: Int, rule: ParseRule[A], allowNewlines: Bool): Opt[A] =
    def tryEmpty(tok: Token, loc: Loc) = rule.emptyAlt match
      case S(res) => S(res())
      case N =>
        consume
        err(msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> S(loc) :: Nil)
        N
    yeetSpaces match
    // case (tok @ (id: IDENT), loc) :: _ if Keyword.all.get(id.name).exists(_.leftPrecOrMin < prec) =>
    //   printDbg(s"Precedence of $id < $prec")
    //   // TODO dedup with "nil" case below?
    //   rule.emptyAlt match
    //     case S(res) =>
    //       S(res)
    //     case N =>
    //      err((msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found end of phrase instead" -> S(loc.left) :: Nil)
    //       N
    case (tok @ (id: IDENT), loc) :: _ =>
      Keyword.all.get(id.name) match
      case S(Keyword.`:`) | N =>
        // encountering `:` should lead to parsing an expr (likely a pun)
        tryParseExp(prec, tok, loc, rule, allowNewlines = allowNewlines)
      case S(kw) =>
        rule.getKwAlt(kw, S(loc)) match
        case S(subRule) =>
          if verbose then printDbg(s"$$ proceed with rule: ${subRule.name}")
          consume
          yeetSpaces match
          case (tok @ BRACKETS(_: Indent_Curly, toks), loc) :: _ if subRule.blkAlt.isEmpty =>
            consume
            rec(toks, S(tok.innerLoc), tok.describe)
              .concludeWith(_.parseRule(kw.rightPrec.getOrElse(CommaPrecNext), subRule, allowNewlines = true))
          case _ =>
            parseRule(kw.rightPrec.getOrElse(CommaPrecNext), subRule, allowNewlines = allowNewlines)
        case N =>
          if verbose then printDbg(s"$$ cannot find a rule starting with: ${id.name}")
          rule.exprAlt match
          case S(exprAlt) =>
            consume
            prefixRules.getKwAlt(kw, S(loc)) match
            case S(subRule) =>
              val e = yeetSpaces match
                case (br @ BRACKETS(_: Indent_Curly, toks), _brLoc) :: _
                if subRule.blkAlt.isEmpty && (subRule.kwAlts.nonEmpty || subRule.exprAlt.isDefined) =>
                  // * Enter this indented block to parse the continuation of a prefix keyword,
                  // * but only when the subrule doesn't already have its own block handler (`blkAlt.isEmpty`)
                  // * and has keyword or expression alternatives to parse (`kwAlts.nonEmpty || exprAlt.isDefined`).
                  // * This skips block entry for keywords registered via `singleKw` (e.g., `true`, `false`,
                  // * `undefined`, `null`, `this`) whose continuation rule is end-only — they produce a
                  // * `ParseRule(end(v))` with no `kwAlts`, no `exprAlt`, and no `blkAlt`.
                  // * Without this guard, `if true` followed by an indented `then`/`else` would consume the
                  // * block trying to parse `true`'s empty continuation, losing the `then`/`else` tokens.
                  consume
                  val blk = rec(toks, S(br.innerLoc), br.describe)
                    .concludeWith(_.blockOf(subRule, Nil, allowNewlines = true))
                  val tree = blk match
                    case Nil =>
                      err(msg"Expected ${subRule.whatComesAfter} ${subRule.mkAfterStr}; found empty block instead"
                        -> S(_brLoc) :: Nil)
                      errExpr
                    case single :: Nil => single
                    case multiple => Block(multiple)
                  exprCont(tree, prec, allowNewlines = allowNewlines)
                case _ =>
                  exprCont(
                    parseRule(kw.rightPrecOrMin, subRule, allowNewlines = allowNewlines)
                      .getOrElse(errExpr), prec, allowNewlines = allowNewlines)
              parseRule(prec, exprAlt.rest, allowNewlines = allowNewlines).map(res => exprAlt.k(e, res))
            case N =>
              tryEmpty(tok, loc)
          case N =>
            tryEmpty(tok, loc)
    case (tok @ (_: NEWLINE_COMMA), l0) :: (id: IDENT, l1) :: _ if allowNewlines && rule.kwAlts.contains(id.name) =>
      consume
      parseRule(prec, rule, allowNewlines = allowNewlines)
    case (tok @ (_: NEWLINE_COMMA), l0) :: _ =>
      // TODO(cur)
      rule.emptyAlt match
        case S(res) => S(res())
        case N =>
          //err((msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> lastLoc :: Nil)
          err(msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> S(l0) :: Nil)
          N
    case (br @ BRACKETS(_: Indent_Curly, toks), loc) :: _ =>
      // rule.blkAlt match
      //   case S(res) => S(res)
      //   case N =>
      //    err((msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found ${tok.describe} instead" -> lastLoc :: Nil)
      //     N
      
      if verbose then printDbg("$ found an indented" + (toks match
        case (_, loc) :: tail =>
          val lastLoc = tail.lastOption.map(_._2).getOrElse(loc)
          s" block from ${loc.showStart} to ${lastLoc.showEnd}"
        case Nil => "empty block"))
      rule.blkAlt match
        case S(exprAlt) =>
          consume
          if verbose then printDbg("$ found blockAlt; proceed with block")
          val e = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.block(allowNewlines = true))
            |> Tree.Block.apply
          parseRule(prec, exprAlt.rest, allowNewlines = true).map(res => exprAlt.k(e, res))
        case N =>
          
          if verbose then printDbg("$ no blockAlt; proceed with rule")
          
          val continue = toks.headOption match
            case S(LITVAL(_) -> _) => true
            case S(IDENT(nme, sym) -> _) =>
              Keyword.all.contains(nme) && (
                  rule.kwAlts.contains(nme)
                  || prefixRules.kwAlts.contains(nme) && rule.exprAlt.nonEmpty
              ) || rule.exprAlt.nonEmpty
            case _ => false
            
          if continue then
            consume
            rec(toks, S(br.innerLoc), br.describe).concludeWith(_.parseRule(prec, rule, allowNewlines = false))
          else tryEmpty(br, loc)
          
    case (tok, loc) :: _ =>
      if verbose then printDbg("$ treat as an expression: " + tok.describe)
      tryParseExp(prec, tok, loc, rule, allowNewlines =
        true /* Making this false somehow makes the following not parse:
          ```
          if (print("Hello World"), false)
            then 0(0)
            else 1
          ```
          and this parse incorrectly (as a kw stutter):
          ```
          mut
            let x = 1
            in x
          ```
        */)
      // TODO(tok)
    case Nil =>
      rule.emptyAlt match
        case S(res) =>
          S(res())
        case N =>
          err(msg"Expected ${rule.whatComesAfter} ${rule.mkAfterStr}; found end of input instead" -> lastLoc :: Nil)
          N
  
  
  // TODO refactor? This is only used for quotes, which should parse like normal code
  final def bindings(acc: Ls[Tree -> Tree]): Ls[Tree -> Tree] = 
    cur match
      case (SPACE, _) :: _ =>
        consume
        bindings(acc)
      case (_: NEWLINE_COMMA, _) :: _ => // TODO: | ...
        acc.reverse
      case (IDENT(nme, sym), l0) :: _ =>
        consume
        yeetSpaces match
          case (IDENT("=", _), l1) :: _ => consume
          case (tk, l1) :: _ =>
            err(msg"Expected `=` after ${nme}; found ${tk.toString} instead" -> S(l1) :: Nil)
          case _ => die
        val rhs = simpleExprImpl(0, allowNewlines = true)
        val v = Tree.Ident(nme).withLoc(S(l0))
        cur match
          case (COMMA, l1) :: _ =>
            consume
            bindings((v -> rhs) :: acc)
          case _ =>
            ((v -> rhs) :: acc).reverse
      case _ =>
        Nil
  
  
  def expr(prec: Int, allowNewlines: Bool)(using Line): Tree =
    val res = parseRule(prec,
        prefixRulesAllowIndentedBlock,
        allowNewlines = allowNewlines
      ).getOrElse(errExpr) // * a `None` result means an alread-reported error
    exprCont(res, prec, allowNewlines = allowNewlines)
  
  def simpleExpr(prec: Int, allowNewlines: Bool)(using Line): Tree =
    wrap(prec)(simpleExprImpl(prec, allowNewlines = allowNewlines))
  def simpleExprImpl(prec: Int, allowNewlines: Bool): Tree =
    yeetSpaces match
    case (IDENT("=", _), l0) :: (IDENT(nme, false), l1) :: rest =>
      consume
      consume
      Pun(true, new Ident(nme).withLoc(S(l1)))
    case (IDENT(":", _), l0) :: (IDENT(nme, false), l1) :: rest =>
      consume
      consume
      Pun(false, new Ident(nme).withLoc(S(l1)))
    case (IDENT("@", _), l0) :: (IDENT(id, false), l1) :: _ =>
      consume
      consume
      val a = annot(new Ident(id).withLoc(S(l0 ++ l1)))
      exprCont(
        Annotated(a, simpleExpr(AnnotBodyPrec, allowNewlines = allowNewlines)),
        prec, allowNewlines = allowNewlines)
    case (ESC_IDENT(name), loc) :: _ =>
      consume
      val id = Tree.Ident(name).withLoc(S(loc))
      exprCont(id, prec, allowNewlines = true)
    case (IDENT(nme, sym), loc) :: _ =>
      Keyword.all.get(nme) match
      case S(kw) => // * Expressions starting with keywords should be handled in parseRule
        // * I guess this case is not really supposed to ever be reached (?)
        err(msg"Unexpected ${kw.toString} in this position" -> S(loc) :: Nil)
        errExpr
      case N =>
        consume
        val id = Tree.Ident(nme).withLoc(S(loc))
        if prefixOps.contains(nme)
        then
          yeetSpaces match
          case Nil => id
          case _ =>
            val newPrec =
              if nme === "!" then
                // Special case: bang operator currently used in BbML
                PrefixOpsPrec
              else
                opCharPrec(nme.head)
            val rhs = expr(newPrec, allowNewlines = allowNewlines)
            exprCont(App(id, PlainTup(rhs)), prec, allowNewlines = allowNewlines)
        else exprCont(id, prec, allowNewlines = allowNewlines)
    case (LITVAL(lit), loc) :: _ =>
      consume
      exprCont(lit.asTree.withLoc(S(loc)), prec, allowNewlines = allowNewlines)
    case (br @ BRACKETS(bk @ (Round | Curly | Square), toks), loc) :: _ =>
      consume
      val ps = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
      yeetSpaces match
        case (QUOTE, l) :: (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _ =>
            consume
            consume
            val rhs = effectfulRhs(kw.rightPrecOrMin, allowNewlines = allowNewlines)
            val lhs = bk match
              case Round => Tup(ps)
              case Curly => Bra(Curly, Block(ps))
              case Square => TyTup(ps)
            exprCont(
              Quoted(InfixApp(lhs, new Keywrd(kw).withLoc(S(l0)), Unquoted(rhs)).withLoc(S(loc))).withLoc(S(l ++ loc)),
              prec, allowNewlines = allowNewlines)
        case (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _
        if kw.leftPrecOrMin > prec =>
          consume
          val rhs = effectfulRhs(kw.rightPrecOrMin, allowNewlines = allowNewlines)
          val lhs = bk match
            case Round => Tup(ps)
            case Curly => ???
            case Square => TyTup(ps)
          val res = InfixApp(lhs.withLoc(S(loc)), new Keywrd(kw).withLoc(S(l0)), rhs)
          exprCont(res, prec, allowNewlines = allowNewlines)
        case _ =>
          val sts = ps
          val res = bk match
            case Square => Tup(sts).withLoc(S(loc))
            case Round => sts match
              case Nil => Unt().withLoc(S(loc))
              case e :: Nil => Bra(Round, e).withLoc(S(loc))
              case es => Bra(Round, Block(es).withLoc(S(loc)))
            case Curly => Bra(Curly, Block(ps))
          exprCont(res, prec, allowNewlines = allowNewlines)
    case (QUOTE, loc) :: _ =>
      consume
      cur match
        case (IDENT("let", _), l0) :: _ =>
          consume
          val bs = bindings(Nil)
          val body = yeetSpaces match
            case (QUOTE, l1) :: (IDENT("in", _), l2) :: _ =>
              consume
              consume
              simpleExpr(0, allowNewlines = false)
            case (tk, loc) :: _ =>
              err(msg"Expected an expression; found ${tk.toString} instead" -> S(loc) :: Nil)
              errExpr
            case Nil =>
              err(msg"Expected '`in'; found end of input instead" -> lastLoc :: Nil)
              errExpr
          bs.foldRight(body):
            case ((v, r), acc) => Quoted(LetLike(new Keywrd(`let`).withLoc(S(l0)), v, S(Unquoted(r)), S(Unquoted(acc))))
        case (IDENT("if", _), l0) :: _ =>
          consume
          // A quoted conditional is parsed as a complete conditional expression, independently
          // of the precedence of the context in which the quote occurs. In particular, a quoted
          // conditional used as a lambda RHS must still consume its `then` branch.
          val term = simpleExprImpl(Keyword.`if`.rightPrecOrMin, allowNewlines = false)
          yeetSpaces match
            case (IDENT("else", _), l1) :: _ =>
              consume
              val ele = simpleExprImpl(prec, allowNewlines = false)
              term match
                case InfixApp(lhs, kw @ Keywrd(Keyword.`then`), rhs) =>
                  Quoted(IfLike(new Keywrd(Keyword.`if`).withLoc(S(l0)), Block(
                    InfixApp(Unquoted(lhs), kw, Unquoted(rhs)) ::
                      PrefixApp(new Keywrd(Keyword.`else`).withLoc(S(l1)), Unquoted(ele)) :: Nil
                  )))
                case tk =>
                  err(msg"Expected '`in'; found ${tk.toString} instead" -> tk.toLoc :: Nil)
                  errExpr
            case (tk, loc) :: _ =>
              err(msg"Expected 'else'; found ${tk.toString} instead" -> S(loc) :: Nil)
              errExpr
            case Nil =>
              err(msg"Expected 'else'; found end of input instead" -> lastLoc :: Nil)
              errExpr
        case (IDENT(nme, sym), loc) :: _ =>
          consume
          val res =
            if nme === "true" then Tree.BoolLit(true) else if nme === "false" then Tree.BoolLit(false) else Tree.Ident(nme)
          exprCont(Tree.Quoted(res.withLoc(S(loc))), prec, allowNewlines = false)
        case (LITVAL(lit), l0) :: _ =>
          consume
          exprCont(Tree.Quoted(lit.asTree.withLoc(S(l0))), prec, allowNewlines = false)
        case _ => unsupportedQuote(S(loc))
    case (BRACKETS(_: Indent_Curly, _), loc) :: _ =>
      err(msg"Expected an expression; found block instead" -> lastLoc :: Nil)
      errExpr
    case (SUSPENSION(dotDotDot), loc) :: _ =>
      consume
      val bod = yeetSpaces match
        case Nil | (COMMA, _) :: _ => N
        case _ => S(expr(prec, allowNewlines = allowNewlines))
      val kw = if dotDotDot 
        then new Keywrd(Keyword.`...`) 
        else new Keywrd(Keyword.`..`)
      Spread(kw.withLoc(S(loc)), bod)
    // case (NEWLINE, loc) :: _ => // this seems to never be reached
    //   raise(WarningReport(msg"???" -> S(loc) :: Nil))
    //   consume
    //   simpleExprImpl(prec)
    case (SELECT(name = nme, dynamic = false), loc) :: _ =>
      consume
      exprCont(Tree.Sel(Tree.Empty(), new Ident(nme).withLoc(S(loc))), prec, allowNewlines = false) // TODO: use a new tree ctor
    case (tok, loc) :: _ =>
      err(msg"Expected an expression; found ${tok.describe} instead" -> S(loc) :: Nil)
      errExpr
    case Nil =>
      err(msg"Expected an expression; found end of input instead" -> lastLoc :: Nil)
      errExpr
  
  
  private def unsupportedQuote(loc: Opt[Loc]) =
    err(msg"This quote syntax is not supported yet" -> loc :: Nil)
    errExpr
  
  
  def effectfulRhs(prec: Int, allowNewlines: Bool)(using Line): Tree =
    yeetSpaces match
      case (br @ BRACKETS(Curly, toks), loc) :: _ =>
        consume
        val eff = rec(toks, S(loc), "effect type").concludeWith(_.expr(0, allowNewlines = allowNewlines))
        Effectful(eff, expr(prec, allowNewlines = allowNewlines))
      case _ => expr(prec, allowNewlines = allowNewlines)
      // case _ => Block.mk(blockMaybeIndented)
  
  
  def split(using Line): Ls[Tree] = wrap("")(splitItem(Nil).reverse)
  
  @tailrec final private def splitItem(acc: Ls[Tree]): Ls[Tree] =
    val item = wrap(s"index = ${acc.size + 1}"):
      cur match // `true | false | Tree`
      case Nil => false
      case (_: NEWLINE_COMMA | SPACE, _) :: _ => consume; true
      case (KEYWORD(kw), loc) :: _ if kw isnt Keyword.__ =>
        prefixRules.getKwAlt(kw, S(loc)) match
        case S(subRule) =>
          consume
          parseRule(CommaPrecNext, subRule, allowNewlines = false).getOrElse(errExpr)
        case N => expr(0, allowNewlines = false)
      case _ => expr(0, allowNewlines = false)
    item match
      case true => splitItem(acc) // continue
      case false => printDbg(s"! end of split"); acc // break
      case e: Tree => // needs further inspection
        yeetSpaces match
        case (_: NEWLINE_COMMA, _) :: _ =>
          consume; splitItem(e :: acc)
        case _ => printDbg(s"! end of split"); e :: acc
  
  
  /** Parse an operator split (block of lines starting by an operator).
   *  TODO: parse let bindings
   */
  def opSplit(lhs: Tree, splittingOpLoc: Loc, prec: Int)(using Line): Tree =
    wrap((lhs, splittingOpLoc, prec))(opSplitImpl(lhs, splittingOpLoc, prec, Nil))
  def opSplitImpl(lhs: Tree, splittingOpLoc: Loc, prec: Int, acc: Ls[Tree]): Tree =
    val (newAcc, e) = yeetSpaces match
      case (PrefixRule(kw, rule), loc) :: _ =>
        consume
        val e = parseRule(kw.rightPrecOrMin, rule.map(_.withLoc(S(loc))), allowNewlines = true).getOrElse(errExpr)
        (e :: acc, S(e))
      case _ => exprCont(SplitPoint(), prec, allowNewlines = false) match
        case SplitPoint() => // * Note: nothing was parsed!
          // * Kludge to accommodate the kludge for `then` below
          (acc, N)
        case e => (e :: acc, S(e))
    yeetSpaces match
    case Nil => OpSplit(lhs, newAcc.reverse)
    case (_: NEWLINE_COMMA, l0) :: _ =>
      consume
      opSplitImpl(lhs, splittingOpLoc, prec, newAcc)
    case (SELECT(nme, dyn), l0) :: rest =>
      assert(SelPrec <= prec)
      ??? // TODO?
    case (IDENT("then", false), l0) :: rest if e.isDefined =>
      // * Kludge – when we have a proper generally splittable syntax, this will be handled by construction
      consume
      val rhs = expr(Keyword.`then`.rightPrecOrMin, allowNewlines = false)
      e match
      case N => die
      case S(e) =>
        opSplitImpl(lhs, splittingOpLoc, prec, InfixApp(e, new Keywrd(Keyword.`then`).withLoc(S(l0)), rhs) :: acc)
    case (IDENT(op, true), l0) :: rest =>
      assert(opPrec(op)._1 <= prec)
      if rest.collectFirst{ case (_: NEWLINE_COMMA | IDENT("then", false), _) => }.isEmpty // TODO dedup
      then
        OpSplit(lhs, acc.reverse)
      else
        err(
          msg"Operator cannot be used inside this operator split" -> S(l0) ::
          msg"as it has lower precedence than the splitting operator here" -> S(splittingOpLoc) ::
          Nil)
        val rhs = expr(opPrec(op)._2, allowNewlines = false)
        opSplitImpl(OpApp(lhs, Ident(op).withLoc(S(l0)), rhs :: Nil), splittingOpLoc, prec, newAcc)
    case (tok, loc) :: _ => // TODO indented op block
      err(msg"Unexpected ${tok.describe} in this operator split inner position" -> S(loc)::
          msg"Note: the operator split starts here" -> S(splittingOpLoc)
          :: Nil)
      OpSplit(lhs, acc reverse_::: errExpr :: Nil)
  
  
  /** `gobbleSpaces` is currently only used to prevent `@foo (2 + 2)` from parsing as `@foo(2 + 2) ...` */
  final def exprCont(acc: Tree, prec: Int, allowNewlines: Bool, gobbleSpaces: Bool = true)(using Line): Tree =
    wrap(prec, s"`$acc`", allowNewlines)(exprContImpl(acc, prec, allowNewlines, gobbleSpaces))
  
  final def exprContImpl(acc: Tree, prec: Int, allowNewlines: Bool, gobbleSpaces: Bool): Tree =
    cur match
      
      case (SPACE, l0) :: _ if gobbleSpaces =>
        consume
        acc match // TODO: [CY] looks fishy. a better way? [LP] indeed; ref should be a prefix keyword!
        case Sel(reg, Ident("ref")) => RegRef(reg, simpleExprImpl(0, allowNewlines = false))
        case _ => exprCont(acc, prec, allowNewlines = allowNewlines)
        
      case (QUOTE, l) :: _ => cur match
        case _ :: (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _ if kw.leftPrecOrMin > prec =>
          consume
          consume
          val rhs = effectfulRhs(kw.rightPrecOrMin, allowNewlines = allowNewlines)
          exprCont(Quoted(InfixApp(PlainTup(acc), new Keywrd(kw).withLoc(S(l0)), Unquoted(rhs))), prec, allowNewlines = allowNewlines)
        case _ :: (br @ BRACKETS(Round, toks), loc) :: _ =>
          consume
          consume
          val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented).map(t => Unquoted(t))
          val res = App(Unquoted(acc), Tup(as).withLoc(S(loc)))
          exprCont(Quoted(res), prec, allowNewlines = allowNewlines)
        case _ :: (OP(opStr), l0) :: _ =>
          if opPrec(opStr)._1 > prec then
            consume
            consume
            val v = Ident(opStr).withLoc(S(l0))
            yeetSpaces match
              case (_: NEWLINE_COMMA, l0) :: _ => consume
              case _ =>
            val rhs = expr(opPrec(opStr)._2, allowNewlines = allowNewlines)
            exprCont(opStr match {
                case "with" => unsupportedQuote(S(l0))
                case _ => Quoted(App(v, PlainTup(Unquoted(acc), Unquoted(rhs))))
              }, prec, allowNewlines = allowNewlines)
          else acc
        case _ :: (KEYWORD(Keyword("in")), _) :: _ =>
          acc
        case _ =>
          consume
          unsupportedQuote(acc.toLoc)
          acc
      case (COMMA, l0) :: _ if prec === 0 =>
        consume
        err(msg"Unexpected comma in this position" -> S(l0) :: Nil)
        acc
        /* 
      case (KEYWORD(opStr @ "=>"), l0) :: (_: NEWLINE_COMMA, l1) :: _ if opPrec(opStr)._1 > prec =>
        consume
        val rhs = Blk(typingUnit.entities)
        R(Lam(PlainTup(acc), rhs))
        */
      // case (KEYWORD(kw @ (Keyword.`=`)), l0) :: _ if kw.leftPrecOrMin > prec =>
      //   consume
      //   ???
      case (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _
      if kw.leftPrecOrMin > prec =>
        consume
        val rhs = effectfulRhs(kw.rightPrecOrMin, allowNewlines = allowNewlines)
        val res = acc match
          case _ => InfixApp(PlainTup(acc), new Keywrd(kw).withLoc(S(l0)), rhs)
        exprCont(res, prec, allowNewlines = allowNewlines)
        
      case (IDENT("!", _), l0) :: (br @ BRACKETS(bk, toks), l1) :: _ =>
        consume
        consume
        val inner = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.expr(0, allowNewlines = true))
        exprCont(DynAccess(acc, Bra(bk, inner)), prec, allowNewlines = allowNewlines)
      // TODO: these should eventually no longer be treated as dynamic:
      case (PERIOD, l0) :: (br @ BRACKETS(bk @ (Round | Square), toks), l1) :: _ =>
        consume
        consume
        val inner = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.expr(0, allowNewlines = true))
        exprCont(DynAccess(acc, Bra(bk, inner)).withLoc(S(l0 ++ l1)), prec, allowNewlines = allowNewlines)
      
      case (PERIOD, l0) :: (br @ BRACKETS(Curly, toks), l1) :: _ =>
        consume
        consume
        val inner = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
        exprCont(OpenIn(acc, Block(inner)), prec, allowNewlines = allowNewlines)
        
      case (PERIOD, l0) :: (LITVAL(lit: (Tree & Literal)), l1) :: _ =>
        consume
        consume
        exprCont(DynAccess(acc, lit.withLoc(S(l1))).withLoc(S(l0 ++ l1)), prec, allowNewlines = allowNewlines)
        
        /* 
      case (PERIOD, l0) :: (br @ BRACKETS(Square, toks), l1) :: _ =>
        consume
        consume
        val idx = rec(toks, S(br.innerLoc), br.describe)
          .concludeWith(_.simpleExpr(0, allowSpace = true))
        val newAcc = Subs(acc, idx).withLoc(S(l0 ++ l1 ++ idx.toLoc))
        exprCont(newAcc, prec, allowNewlines)
        */
      
      // * Parse operator splits
      case (br @ BRACKETS(_: Indent_Curly,
          toks @ ((tok @ (IDENT(_, true) | SELECT(_, _) | KEYWORD(_: Keyword.InfixSplittable)), l0) :: _)), loc) :: _
      if tok.match {
        case KEYWORD(Keyword.`of`) => AppPrec
        case KEYWORD(kw) => kw.leftPrecOrMin
        case id: IDENT => opPrec(id.name)._1
        case sel: SELECT => SelPrec
      } > prec
      =>
        consume
        if toks.collectFirst{ case (_: NEWLINE_COMMA, _) => }.isEmpty then
          // * If the indented block doens't have any newlines or commas,
          // * this is not truly a split, and we can parse it as a normal expression continuation.
          cur = toks ::: cur
          exprCont(acc, prec, allowNewlines = allowNewlines)
        else
          val r = rec(toks, S(loc), "operator block")
          val res = r.opSplit(acc, l0, prec)
          r.yeetSpaces match
          case Nil =>
            exprCont(res, prec, allowNewlines = allowNewlines)
          case toks =>
            cur = toks ::: cur
            exprCont(res, prec, allowNewlines = allowNewlines)
      
      // TODO
      // case (NEWLINE, _) :: (SELECT(nme), _) :: _
      // =>
      
      // * Parse newline-operators, eg `2 + 2\n*\n2 + 2` <=> `(2 + 2) * (2 + 2)`
      // TODO also allow uses of SELECT
      case (_: NEWLINE_COMMA, _) :: (OP(opStr), l0) :: rest
      if allowNewlines
      && prec <= NoElsePrec // (Q: why doesn't MinPrec work?)
      && NOISE.get(rest).nonEmpty // * Don't treat as infix if there are no tokens for the RHS (eg `()\n???`)
      && (!prefixOps.contains(opStr) || rest.match
        case (_: NEWLINE_COMMA, _) :: _ | (SPACE, _) :: _ | (BRACKETS(_: Indent_Curly, _), _) :: _ | Nil => true
        case _ => false
      ) =>
        consume
        consume
        val v = Ident(opStr).withLoc(S(l0))
        val rhsPrec = yeetSpaces match
        case (_: NEWLINE_COMMA, l0) :: _ =>
          consume
          CommaPrecNext2 // for chained nl ops: left assoc
        case _ =>
          opPrec(opStr)._2
        val rhs = expr(rhsPrec, allowNewlines = allowNewlines)
        exprCont(OpApp(acc, v, rhs :: Nil), prec, allowNewlines = allowNewlines)
        
      case (OP("::"), l0) :: (IDENT(id, false), l1) :: _ =>
        consume
        consume
        exprCont(MemberProj(acc, new Ident(id).withLoc(S(l1))).withLoc(S(l0 ++ l1)), prec, allowNewlines = allowNewlines)
      case (OP(opStr), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        val v = Ident(opStr).withLoc(S(l0))
        yeetSpaces match
          case (_: NEWLINE_COMMA, l0) :: _ => consume
          case _ =>
        printDbg(s"! found operator `$opStr` with prec ${opPrec(opStr)}")
        yeetSpaces match
          case (BRACKETS(_: Indent_Curly, toks), l0) :: _ =>
            consume
            // rec(toks, S(br.innerLoc), br.describe).concludeWith(f(_, true))
            val rhs = rec(toks, S(l0), "operator split").concludeWith(_.split)
            exprCont(OpApp(acc, v, Block(rhs).withLoc(S(l0)) :: Nil),
              prec, allowNewlines = allowNewlines)
          case _ => 
            // val rhs = simpleExpr(opPrec(opStr)._2)
            val rhs = expr(opPrec(opStr)._2, allowNewlines = allowNewlines)
            exprCont(opStr match {
              case "with" =>
                rhs match {
                  // TODO?
                  // case rhs: Rcd =>
                  //   With(acc, rhs)//.withLocOf(term)
                  // case Bra(true, rhs: Rcd) =>
                  //   With(acc, rhs)//.withLocOf(term)
                  case _ =>
                    err(msg"record literal expected here; found ${rhs.describe}" -> rhs.toLoc :: Nil)
                    acc
                }
              case _ => OpApp(acc, v, rhs :: Nil)
            }, prec, allowNewlines = allowNewlines)
        
      case (SELECT(name, dyn), l0) :: _ if SelPrec >= prec =>
        consume
        val tree = if dyn then
          DynAccess(acc, new Ident(name).withLoc(S(l0)))
        else
          Sel(acc, new Ident(name).withLoc(S(l0)))
        exprCont(tree, prec, allowNewlines = allowNewlines)
        
      case (br @ BRACKETS(Angle | Square, toks), loc) :: _ =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
        // val res = TyApp(acc, as.map(_.mapSecond.to))
        val res = TyApp(acc, as).withLoc(acc.toLoc.fold(some(loc))(_ ++ loc |> some))
        exprCont(res, prec, allowNewlines = allowNewlines)
        /*
      /*case (br @ BRACKETS(Square, toks), loc) :: _ => // * Currently unreachable because we match Square brackets as tparams
        consume
        val idx = rec(toks, S(br.innerLoc), "subscript").concludeWith(_.simpleExpr(0))
        val res = Subs(acc, idx.withLoc(S(loc)))
        exprCont(res, prec, allowNewlines)*/
      */
      case (br @ BRACKETS(Round, toks), loc) :: _ if prec <= AppPrec =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
        val res = App(acc, Tup(as).withLoc(S(loc)))
        exprCont(res, prec, allowNewlines = allowNewlines)
      case (KEYWORD(Keyword.`of`), _) :: _ if prec <= AppPrec =>
        consume
        val as = blockMaybeIndented
        val res = App(acc, Tup(as))
        exprCont(res, prec, allowNewlines = allowNewlines)
      
      case (_: NEWLINE_COMMA, _) :: (KEYWORD(kw), _) :: _
      if kw.canStartInfixOnNewLine && kw.leftPrecOrMin > prec
      && infixRules.kwAlts.contains(kw.name)
      && (kw isnt Keyword.`do`) // This is to avoid the following case:
        //  ```
        //  0 then "null"
        //  do console.log("non-null")
        //  ```
        // Otherwise, `do` will be parsed as an infix operator
      =>
        consume
        exprCont(acc, prec, allowNewlines = allowNewlines)
        
      case (br @ BRACKETS(bk @ (_: Indent_Curly), toks @ ((KEYWORD(kw), _) :: _)), loc) :: _
      if kw.leftPrecOrMin > prec
      && infixRules.kwAlts.contains(kw.name)
      =>
        consume
        val (res, rest) = rec(toks, S(br.innerLoc), br.describe).continueWith:
          _.exprCont(acc, prec, allowNewlines = true)
        rest match
          case (_, l) :: _ =>
            printDbg(s"!! REDUCING BRACKET")
            cur = (NEWLINE, l.left) :: rest ::: cur
          case _ =>
        exprCont(res, prec, allowNewlines = allowNewlines)
        
      
      case (KEYWORD(kw), l0) :: _ if kw.leftPrecOrMin > prec =>
        if verbose then printDbg(s"$$ found keyword: ${kw.name} (${kw.leftPrecOrMin})")
        infixRules.getKwAlt(kw, S(l0)) match
          case S(subRule) =>
            consume
            /* // * Disabled for the sake of consistency
            // These operators used to follow the symbolic-operator path, which accepts an RHS
            // on the next line. Preserve that behavior now that they are parsed as keywords.
            // Example:
            //    foo |
            //    bar
            if (kw is Keyword.`|`) || (kw is Keyword.`&`) then
              yeetSpaces match
                case (_: NEWLINE_COMMA, _) :: _ => consume
                case _ =>
            */
            if verbose then printDbg(s"$$ proceed with rule: ${subRule.name}")
            subRule.exprAlt match
              case S(exprAlt) =>
                if verbose then printDbg("$ parsing the right-hand side")
                val rhs = expr(kw.rightPrecOrMin, allowNewlines = allowNewlines)
                parseRule(kw.rightPrecOrMin, exprAlt.rest, allowNewlines = allowNewlines).map: rest =>
                  exprCont(exprAlt.k(rhs, rest)(acc), prec, allowNewlines = allowNewlines) // FIXME prec??
                .getOrElse(errExpr)
              case N =>
                // TODO other alts...?
                err(msg"Expected ${subRule.whatComesAfter} ${subRule.mkAfterStr}; found ${kw.name} instead" -> S(l0) :: Nil)
                acc
          case _ => acc
      case _ =>
        exprJux(acc, prec, allowNewlines = false)
  
  
  final def exprJux(acc: Tree, prec: Int, allowNewlines: Bool)(using Line): Tree =
    wrap(prec, s"`$acc`", allowNewlines)(exprJuxImpl(acc, prec, allowNewlines))
  
  final def exprJuxImpl(acc: Tree, prec: Int, allowNewlines: Bool): Tree =
    cur match
    case (_: NEWLINE_COMMA, _) :: _ if allowNewlines =>
      consume
      exprJux(acc, prec, allowNewlines = allowNewlines)
    case (IDENT(id, false), _) :: _
    if prec < AppPrec && !Keyword.all.contains(id) =>
      val res = exprCont(Jux(acc, expr(AppPrec, allowNewlines = allowNewlines)), prec, allowNewlines = allowNewlines)
      exprJux(res, prec, allowNewlines = allowNewlines)
    // case (br @ BRACKETS(_: Indent_Curly, toks), l0) :: _
    case (br @ BRACKETS(Curly, toks), l0) :: _
    if prec <= AppPrec =>
      consume
      val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.block(allowNewlines = true))
      exprCont(Reft(acc, Block(res).withLoc(S(l0))), prec, allowNewlines = allowNewlines)
    case (br @ BRACKETS(Indent, toks), l0) :: _
    if prec < AppPrec && (toks.headOption match
      case S((IDENT(nme, sym), _)) => !sym && !Keyword.all.contains(nme)
      case _ => true
    ) =>
      consume
      val res = rec(toks, S(br.innerLoc), br.describe).concludeWith:
        _.block(allowNewlines = true)
      exprCont(Jux(acc, Block(res).withLoc(S(l0))), prec, allowNewlines = true)
    
    case (tok, _) :: _ =>
      printDbg(s"stops at ${tok.toString}")
      acc
    case Nil =>
      printDbg(s"stops at the end of input")
      acc  
