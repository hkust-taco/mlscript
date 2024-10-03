package hkmc2
package syntax

import scala.util.boundary
import sourcecode.{Name, Line}
import mlscript.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._

import Tree.*
import Parser.*
import scala.annotation.tailrec


object Parser:
  
  type TokLoc = (Stroken, Loc)
  
  type LTL = Ls[TokLoc]
  
  private val MinPrec = 0
  private val NoElsePrec = MinPrec + 1
  
  private val prec: Map[Char,Int] =
    List(
      "", // `of` rhs
      ",",
      // ^ for keywords
      // ";",
      "=",
      "@",
      ":",
      "|",
      "/ \\",
      "^",
      "&",
      // "= !",
      "!",
      "< >",
      "+ -",
      // "* / %",
      "* %",
      "", // Precedence of prefix operators
      "", // Precedence of application
      ".",
    ).zipWithIndex.flatMap {
      case (cs, i) => cs.filterNot(_ === ' ').map(_ -> (i + Keyword.maxPrec.get))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  // private val CommaPrec = prec(',')
  private val CommaPrec = 0
  private val CommaPrecNext = CommaPrec + 1
  private val AppPrec = prec('.') - 1
  private val PrefixOpsPrec = AppPrec - 1
  
  final def opCharPrec(opChar: Char): Int = prec(opChar)
  final def opPrec(opStr: Str): (Int, Int) = opStr match {
    case "+." | "-." | "*." =>
      (prec(opStr.head), prec(opStr.head))
    case _ if opStr.exists(_.isLetter) =>
      (Keyword.maxPrec.get, Keyword.maxPrec.get)
    case _ =>
      val r = opStr.last
      (prec(opStr.head), prec(r) - (if r === '@' || r === '/' || r === ',' || r === ':' then 1 else 0))
  }
  val prefixOps: Set[Str] = Set("!", "+", "-", "~", "@")
  
  object KEYWORD:
    def unapply(t: Token): Opt[Keyword] = t match
      case IDENT(nme, sym) => Keyword.all.get(nme)
      // case IDENT(nme, sym) => Keyword.all.get(nme).map(_.name)
      // case IDENT(nme, sym) if Keyword.all.contains(nme) => S(nme)
      case _ => N
  
  object OP:
    def unapply(t: Token): Opt[Str] = t match
      case IDENT(nme, true) if !Keyword.all.contains(nme) => S(nme)
      case _ => N
  
  object ALPHA:
    def unapply(t: Token): Opt[Str] = t match
      case IDENT(nme, false) if !Keyword.all.contains(nme) => S(nme)
      case _ => N

  extension (loc: Loc)
    def showStart: String =
      loc.origin.fph.getLineColAt(loc.spanStart) match
        case (ln, _, col) => s"Ln $ln Col $col"
    def showEnd: String =
      loc.origin.fph.getLineColAt(loc.spanStart) match
        case (ln, _, col) => s"Ln $ln Col $col"
  
end Parser
import Parser._

abstract class Parser(
  origin: Origin,
  tokens: Ls[TokLoc],
  raiseFun: Diagnostic => Unit,
  val dbg: Bool,
  // fallbackLoc: Opt[Loc], description: Str = "input",
):
  outer =>
  
  protected def doPrintDbg(msg: => Str): Unit
  protected def printDbg(msg: => Any): Unit =
    doPrintDbg("│ " * this.indent + msg)
  
  protected var indent = 0
  private var _cur: Ls[TokLoc] = tokens
  
  private def wrap[R](args: => Any)(mkRes: => R)(implicit l: Line, n: Name): R =
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
    new Parser(origin, tokens, raiseFun, dbg
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
  
  final def consume(implicit l: Line, n: Name): Unit =
    if dbg then printDbg(s"! ${n.value}\t\tconsumes ${Lexer.printTokens(_cur.take(1))}    [at syntax/Parser.scala:${l.value}]")
    resetCur(_cur.tailOption.getOrElse(Nil)) // FIXME throw error if empty?
  
  private def yeetSpaces(using Line, Name): Ls[TokLoc] =
    cur.dropWhile(tkloc =>
      (tkloc._1 === SPACE
      || tkloc._1.isInstanceOf[COMMENT] // TODO properly retrieve and store all comments in AST?
      ) && { consume; true })
  
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
  
  final def concludeWith[R](f: this.type => R): R =
    val res = f(this)
    cur.dropWhile(tk => (tk._1 === SPACE || tk._1 === NEWLINE) && { consume; true }) match
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        err(msg"Unexpected ${relevantToken.describe} here" -> S(rl) :: Nil)
      case Nil => ()
    printDbg(s"Concluded with $res")
    res
  
  
  final def maybeIndented[R](f: (Parser, Bool) => R): R =
    cur match
      case (br @ BRACKETS(Indent, toks), _) :: _ =>
        consume
        rec(toks, S(br.innerLoc), br.describe).concludeWith(f(_, true))
      case _ => f(this, false)
  
  final def blockMaybeIndented: Ls[Tree] =
    maybeIndented((p, i) => p.block(allowNewlines = i))
  
  def block(allowNewlines: Bool)(using Line): Ls[Tree] = blockOf(ParseRule.prefixRules, allowNewlines)
  
  def blockOf(rule: ParseRule[Tree], allowNewlines: Bool)(using Line): Ls[Tree] =
    wrap(rule.name)(blockOfImpl(rule, allowNewlines))
  def blockOfImpl(rule: ParseRule[Tree], allowNewlines: Bool): Ls[Tree] =
    def blockContOf(rule: ParseRule[Tree]): Ls[Tree] =
      yeetSpaces match
        case (COMMA, _) :: _ => consume; blockOf(rule, allowNewlines)
        case (SEMI, _) :: _ => consume; blockOf(rule, allowNewlines)
        case (NEWLINE, _) :: _ if allowNewlines => consume; blockOf(rule, allowNewlines)
        case _ => Nil
    cur match
    case Nil => Nil
    case (NEWLINE, _) :: _ if allowNewlines => consume; blockOf(rule, allowNewlines)
    case (SPACE, _) :: _ => consume; blockOf(rule, allowNewlines)
    case (tok @ (id: IDENT), loc) :: _ =>
      Keyword.all.get(id.name) match
      case S(kw) =>
        consume
        rule.kwAlts.get(kw.name) match
        case S(subRule) =>
          yeetSpaces match
          case (tok @ BRACKETS(Indent, toks), loc) :: _ if subRule.blkAlt.isEmpty =>
            consume
            rec(toks, S(tok.innerLoc), tok.describe).concludeWith(_.blockOf(subRule, allowNewlines)) // FIXME allowNewlines?
          case _ =>
            val res = parseRule(CommaPrecNext, subRule).getOrElse(errExpr)
            exprCont(res, CommaPrecNext, false) :: blockContOf(rule)
        case N =>
          
          // TODO dedup this common-looking logic:
          
          rule.exprAlt match
          case S(exprAlt) =>
            yeetSpaces match
            case (tok @ BRACKETS(Indent, toks), loc) :: _ /* if subRule.blkAlt.isEmpty */ =>
              consume
              ParseRule.prefixRules.kwAlts.get(kw.name) match
              case S(subRule) if subRule.blkAlt.isEmpty =>
                rec(toks, S(tok.innerLoc), tok.describe).concludeWith { p =>
                  p.blockOf(subRule.map(e => parseRule(CommaPrecNext, exprAlt.rest).map(res => exprAlt.k(e, res)).getOrElse(errExpr)), allowNewlines)
                } ++ blockContOf(rule)
              case _ =>
                TODO(cur)
            case _ =>
              ParseRule.prefixRules.kwAlts.get(kw.name) match
              case S(subRule) =>
                val e = parseRule(CommaPrecNext, subRule).getOrElse(errExpr)
                parseRule(CommaPrecNext, exprAlt.rest).map(res => exprAlt.k(e, res)).getOrElse(errExpr) :: blockContOf(rule)
              case N =>
                // TODO dedup?
                err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
                errExpr :: blockContOf(rule)
          case N =>
            err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
            errExpr :: blockContOf(rule)
            
      case N =>
        tryParseExp(CommaPrecNext, tok, loc, rule).getOrElse(errExpr) :: blockContOf(rule)
    case (tok, loc) :: _ =>
      tryParseExp(CommaPrecNext, tok, loc, rule).getOrElse(errExpr) :: blockContOf(rule)
  
  private def tryParseExp[A](prec: Int, tok: Token, loc: Loc, rule: ParseRule[A]): Opt[A] =
    rule.exprAlt match
      case S(exprAlt) =>
        val e = simpleExpr(prec)
        printDbg("$ proceed with rule: " + exprAlt)
        parseRule(prec, exprAlt.rest).map(res => exprAlt.k(e, res))
      case N =>
        rule.emptyAlt match
        case S(res) =>
          S(res)
        case N =>
          err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
          N
  
  /** A result of None means there was an error (already reported) and nothing could be parsed. */
  def parseRule[A](prec: Int, rule: ParseRule[A])(using Line): Opt[A] =
    wrap(prec, rule)(parseRuleImpl(prec, rule))
  def parseRuleImpl[A](prec: Int, rule: ParseRule[A]): Opt[A] =
    def tryEmpty(tok: Token, loc: Loc) = rule.emptyAlt match
      case S(res) => S(res)
      case N =>
        consume
        err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
        N
    yeetSpaces match
    // case (tok @ (id: IDENT), loc) :: _ if Keyword.all.get(id.name).exists(_.leftPrecOrMin < prec) =>
    //   printDbg(s"Precedence of $id < $prec")
    //   // TODO dedup with "nil" case below?
    //   rule.emptyAlt match
    //     case S(res) =>
    //       S(res)
    //     case N =>
    //       err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found end of phrase instead" -> S(loc.left) :: Nil))
    //       N
    case (tok @ (id: IDENT), loc) :: _ =>
      Keyword.all.get(id.name) match
      case S(kw) =>
        rule.kwAlts.get(id.name) match
        case S(subRule) =>
          printDbg(s"$$ proceed with rule: ${subRule.name}")
          consume
          yeetSpaces match
          case (tok @ BRACKETS(Indent, toks), loc) :: _ if subRule.blkAlt.isEmpty =>
            consume
            rec(toks, S(tok.innerLoc), tok.describe).concludeWith(_.parseRule(kw.assumeRightPrec, subRule))
          case _ =>
            parseRule(kw.assumeRightPrec, subRule)
        case N =>
          rule.exprAlt match
          case S(exprAlt) =>
            consume
            ParseRule.prefixRules.kwAlts.get(id.name) match
            case S(subRule) =>
              // parse(subRule)
              val e = exprCont(parseRule(kw.rightPrecOrMin, subRule).getOrElse(errExpr), prec, false)
              parseRule(prec, exprAlt.rest).map(res => exprAlt.k(e, res))
            case N =>
              tryEmpty(tok, loc)
          case N =>
            tryEmpty(tok, loc)
      case N =>
        printDbg(s"$$ cannot find a rule starting with: ${id.name}")
        tryParseExp(prec, tok, loc, rule)
    case (tok @ NEWLINE, l0) :: (id: IDENT, l1) :: _ if rule.kwAlts.contains(id.name) =>
      consume
      parseRule(prec, rule)
    case (tok @ (NEWLINE | SEMI | COMMA), l0) :: _ =>
      // TODO(cur)
      rule.emptyAlt match
        case S(res) => S(res)
        case N =>
          err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> lastLoc :: Nil))
          N
    case (br @ BRACKETS(Indent, toks), loc) :: _ =>
      // rule.blkAlt match
      //   case S(res) => S(res)
      //   case N =>
      //     err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> lastLoc :: Nil))
      //     N
      consume
      printDbg("$ found an indented" + (toks match
        case (_, loc) :: tail =>
          val lastLoc = tail.lastOption.map(_._2).getOrElse(loc)
          s" block from ${loc.showStart} to ${lastLoc.showEnd}"
        case Nil => "empty block"))
      rule.blkAlt match
        case S(exprAlt) =>
          printDbg("$ found blockAlt; proceed with block")
          val e = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.block(allowNewlines = true))
            |> Tree.Block.apply
          parseRule(prec, exprAlt.rest).map(res => exprAlt.k(e, res))
        case N =>
          printDbg("$ no blockAlt; proceed with rule")
          rec(toks, S(br.innerLoc), br.describe).concludeWith(_.parseRule(prec, rule))
    case (tok, loc) :: _ =>
      printDbg("$ treat as an expression: " + tok.describe)
      tryParseExp(prec, tok, loc, rule)
      // TODO(tok)
    case Nil =>
      rule.emptyAlt match
        case S(res) =>
          S(res)
        case N =>
          err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found end of input instead" -> lastLoc :: Nil))
          N
  
  final def bindings(acc: Ls[Tree -> Tree]): Ls[Tree -> Tree] = 
    cur match {
      case (SPACE, _) :: _ =>
        consume
        bindings(acc)
      case (NEWLINE | SEMI, _) :: _ => // TODO: | ...
        acc.reverse
      case (IDENT(nme, sym), l0) :: _ =>
        consume
        yeetSpaces match
          case (IDENT("=", _), l1) :: _ => consume
          case (tk, l1) :: _ =>
            err((msg"Expected `=` after ${nme}; found ${tk.toString} instead" -> S(l1) :: Nil))
        val rhs = simpleExprImpl(0)
        val v = Tree.Ident(nme).withLoc(S(l0))
        cur match {
          case (COMMA, l1) :: _ =>
            consume
            bindings((v -> rhs) :: acc)
          case _ =>
            ((v -> rhs) :: acc).reverse
        }
      case _ =>
        Nil
  }
  
  def expr(prec: Int, allowIndentedBlock: Bool = false)(using Line): Tree =
    parseRule(prec,
      if allowIndentedBlock then ParseRule.prefixRulesAllowIndentedBlock else ParseRule.prefixRules
    ).getOrElse(errExpr) // * a `None` result means an alread-reported error
  
  def simpleExpr(prec: Int)(using Line): Tree = wrap(prec)(simpleExprImpl(prec))
  def simpleExprImpl(prec: Int): Tree =
    yeetSpaces match
    case (IDENT(nme, sym), loc) :: _ =>
      Keyword.all.get(nme) match
        case S(kw) => // * Expressions starting with keywords should be handled in parseRule
          // * I guess this case is not really supposed to be ever reached (?)
          err((msg"Unexpected ${kw.toString} in this position" -> S(loc) :: Nil))
          errExpr
        case N =>
          consume
          val id = Tree.Ident(nme).withLoc(S(loc))
          if prefixOps.contains(nme)
          then
            yeetSpaces match
              case Nil => id
              case _ =>
                val rhs = expr(PrefixOpsPrec)
                exprCont(App(id, PlainTup(rhs)), prec, allowNewlines = true)
          else exprCont(id, prec, allowNewlines = true)
    case (LITVAL(lit), loc) :: _ =>
      consume
      exprCont(lit.asTree.withLoc(S(loc)), prec, allowNewlines = true)
    case (br @ BRACKETS(bk @ (Round | Square), toks), loc) :: _ =>
      consume
      val ps = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
      yeetSpaces match
        case (QUOTE, l) :: (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _ =>
            consume
            consume
            val rhs = effectfulRhs(kw.rightPrecOrMin)
            val lhs = bk match
              case Round => Tup(ps)
              case Square => TyTup(ps)
            exprCont(
              Quoted(InfixApp(lhs, kw, Unquoted(rhs)).withLoc(S(loc))).withLoc(S(l ++ loc)),
              prec, allowNewlines = true)
        case (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _ =>
          consume
          val rhs = effectfulRhs(kw.rightPrecOrMin)
          val lhs = bk match
            case Round => Tup(ps)
            case Square => TyTup(ps)
          val res = InfixApp(lhs, kw, rhs).withLoc(S(loc))
          exprCont(res, prec, allowNewlines = true)
        case _ =>
          val sts = ps
          val res = bk match
            case Square => Tup(sts).withLoc(S(loc))
            case Round => sts match
              case Nil => UnitLit(true).withLoc(S(loc))
              case e :: Nil => e
              case es => Block(es).withLoc(S(loc))
          exprCont(res, prec, allowNewlines = true)
    case (QUOTE, loc) :: _ =>
      consume
      cur match {
        case (IDENT("let", _), l0) :: _ =>
          consume
          val bs = bindings(Nil)
          val body = yeetSpaces match
            case (QUOTE, l1) :: (IDENT("in", _), l2) :: _ =>
              consume
              consume
              simpleExpr(0)
            case (tk, loc) :: _ =>
              err((msg"Expected an expression; found ${tk.toString} instead" -> S(loc) :: Nil))
              errExpr
            case Nil =>
              err(msg"Expected '`in'; found end of input instead" -> lastLoc :: Nil)
              errExpr
          bs.foldRight(body) {
            case ((v, r), acc) => Quoted(Let(v, Unquoted(r), S(Unquoted(acc))))
          }
        case (IDENT("if", _), l0) :: _ =>
          consume
          val term = simpleExprImpl(prec)
          yeetSpaces match
            case (IDENT("else", _), l1) :: _ =>
              consume
              val ele = simpleExprImpl(prec)
              term match
                case InfixApp(lhs, Keyword.`then`, rhs) =>
                  Quoted(IfElse(InfixApp(Unquoted(lhs), Keyword.`then`, Unquoted(rhs)), Unquoted(ele)))
                case tk =>
                  err(msg"Expected '`in'; found ${tk.toString} instead" -> tk.toLoc :: Nil)
                  errExpr
            case (tk, loc) :: _ =>
              err((msg"Expected 'else'; found ${tk.toString} instead" -> S(loc) :: Nil))
              errExpr
            case Nil =>
              err(msg"Expected 'else'; found end of input instead" -> lastLoc :: Nil)
              errExpr
        case (IDENT(nme, sym), loc) :: _ =>
          consume
          exprCont(Tree.Quoted(Tree.Ident(nme).withLoc(S(loc))), prec, allowNewlines = false)
        case (LITVAL(lit), l0) :: _ =>
          consume
          exprCont(Tree.Quoted(lit.asTree.withLoc(S(l0))), prec, allowNewlines = false)
        case _ => unsupportedQuote(S(loc))
      }
    case (BRACKETS(Indent, _), loc) :: _ =>
      err((msg"Expected an expression; found indented block instead" -> lastLoc :: Nil))
      errExpr
    case (tok, loc) :: _ =>
      TODO(tok)
    case Nil =>
      err((msg"Expected an expression; found end of input instead" -> lastLoc :: Nil))
      errExpr
  
  
  private def unsupportedQuote(loc: Opt[Loc]) = {
    err(msg"This quote syntax is not supported yet" -> loc :: Nil)
    errExpr
  }
  
  def effectfulRhs(prec: Int)(using Line): Tree =
    yeetSpaces match
      case (br @ BRACKETS(Curly, toks), loc) :: _ =>
        consume
        val eff = rec(toks, S(loc), "effect type").concludeWith(_.simpleExpr(0))
        Effectful(eff, simpleExpr(prec))
      case _ => expr(prec, allowIndentedBlock = true)
      // case _ => Block.mk(blockMaybeIndented)

  def splitOf()(using Line): Ls[Tree] = wrap("split")(splitOfImpl())
  def splitOfImpl(): Ls[Tree] =
    def splitContOf(): Ls[Tree] = yeetSpaces match
      case (COMMA, _) :: _ => consume; splitOf()
      case (SEMI, _) :: _ => consume; splitOf()
      case (NEWLINE, _) :: _ => consume; splitOf()
      case _ => Nil
    cur match
    case Nil => Nil
    case (NEWLINE, _) :: _ => consume; splitOf()
    case (SPACE, _) :: _ => consume; splitOf()
    case (tok @ (id: IDENT), loc) :: _ =>
      Keyword.all.get(id.name) match
      case S(kw) =>
        consume
        ParseRule.prefixRules.kwAlts.get(kw.name) match
          case S(subRule) =>
            parseRule(CommaPrecNext, subRule).getOrElse(errExpr) :: splitContOf()
          case N => expr(0, false) :: splitContOf()
      case N => expr(0, false) :: splitContOf()
    case _ =>
      printDbg(s"continue to parse expressions")
      expr(0, false) :: splitContOf()

  /** Parse an operator block. Each block item should be a binary operator
   *  followed by an expression, a `let` binding, or an `else` clause.
   */
  def operatorBlock()(using Line): OpBlock = wrap(""):
    @tailrec
    def item(acc: Ls[Tree -> Tree])(using Line): Ls[Tree -> Tree] =
      printDbg(s"! start parsing #${acc.size + 1} block item")
      cur match
      case Nil => printDbg(s"! end of the operator block"); acc
      case (NEWLINE | SPACE, _) :: _ => consume; item(acc)
      case (tok @ KEYWORD(kw @ (Keyword.`let` | Keyword.`else`)), loc) :: _ =>
        ParseRule.prefixRules.kwAlts.get(kw.name) match
        case S(subRule) =>
          consume
          val rhs = parseRule(kw.rightPrecOrMin, subRule).getOrElse(errExpr)
          item(Tree.Empty().withLoc(S(loc)) -> rhs :: acc)
        case N => lastWords(s"missing the parse rule for `${kw.name}`")
      case (tok @ IDENT(opStr, true), loc) :: _ if opPrec(opStr)._1 > 0 =>
        consume
        val res = (Ident(opStr).withLoc(S(loc)) -> expr(0, false)) :: acc
        yeetSpaces match
        case (COMMA | SEMI | NEWLINE, _) :: _ => consume; item(res)
        case _ => res
      case (tok, loc) :: _ =>
        err(msg"Expect an operator instead of ${tok.describe}" -> S(loc) :: Nil)
        (Tree.Error() -> Tree.Error()) :: acc
    OpBlock(item(Nil).reverse)
  
  final def exprCont(acc: Tree, prec: Int, allowNewlines: Bool)(using Line): Tree =
    wrap(prec, s"`$acc`", allowNewlines)(exprContImpl(acc, prec, allowNewlines))
  final def exprContImpl(acc: Tree, prec: Int, allowNewlines: Bool): Tree =
    cur match {
      case (QUOTE, l) :: _ => cur match {
        case _ :: (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _ if kw.leftPrecOrMin > prec =>
          consume
          consume
          val rhs = effectfulRhs(kw.rightPrecOrMin)
          exprCont(Quoted(InfixApp(PlainTup(acc), kw, Unquoted(rhs))), prec, allowNewlines)
        case _ :: (br @ BRACKETS(Round, toks), loc) :: _ =>
          consume
          consume
          val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented).map(t => Unquoted(t))
          val res = App(Unquoted(acc), Tup(as).withLoc(S(loc)))
          exprCont(Quoted(res), prec, allowNewlines)
        case _ :: (OP(opStr), l0) :: _ =>
          if opPrec(opStr)._1 > prec then {
            consume
            consume
            val v = Ident(opStr).withLoc(S(l0))
            yeetSpaces match {
              case (NEWLINE, l0) :: _ => consume
              case _ =>
            }
            val rhs = expr(opPrec(opStr)._2)
            exprCont(opStr match {
                case "with" => unsupportedQuote(S(l0))
                case _ => Quoted(App(v, PlainTup(Unquoted(acc), Unquoted(rhs))))
              }, prec, allowNewlines)
          }
          else acc
        case _ :: (KEYWORD(Keyword("in")), _) :: _ =>
          acc
        case _ =>
          consume
          unsupportedQuote(acc.toLoc)
          acc
      }
      case (COMMA, l0) :: _ if prec === 0 =>
        consume
        err((msg"Unexpected comma in this position" -> S(l0) :: Nil))
        acc
        /* 
      case (KEYWORD(opStr @ "=>"), l0) :: (NEWLINE, l1) :: _ if opPrec(opStr)._1 > prec =>
        consume
        val rhs = Blk(typingUnit.entities)
        R(Lam(PlainTup(acc), rhs))
        */
      case (KEYWORD(kw @ (Keyword.`=>` | Keyword.`->`)), l0) :: _ if kw.leftPrecOrMin > prec =>
        consume
        val rhs = effectfulRhs(kw.rightPrecOrMin)
        val res = acc match
          case _ => InfixApp(PlainTup(acc), kw, rhs)
        exprCont(res, prec, allowNewlines)
        /* 
      case (IDENT(".", _), l0) :: (br @ BRACKETS(Square, toks), l1) :: _ =>
        consume
        consume
        val idx = rec(toks, S(br.innerLoc), br.describe)
          .concludeWith(_.simpleExpr(0, allowSpace = true))
        val newAcc = Subs(acc, idx).withLoc(S(l0 ++ l1 ++ idx.toLoc))
        exprCont(newAcc, prec, allowNewlines)
        */
      case (br @ BRACKETS(Indent, toks @ ((IDENT(opStr, true), _) :: _)), loc) :: _ if opPrec(opStr)._1 > prec =>
        consume
        App(acc, rec(toks, S(loc), "operator block").concludeWith(_.operatorBlock()))
      case (OP(opStr), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        val v = Ident(opStr).withLoc(S(l0))
        yeetSpaces match {
          case (NEWLINE, l0) :: _ => consume
          case _ =>
        }
        printDbg(s"found an infix operator: $opStr")
        yeetSpaces match
          case (BRACKETS(Indent, toks), l0) :: _ =>
            consume
            // rec(toks, S(br.innerLoc), br.describe).concludeWith(f(_, true))
            val rhs = rec(toks, S(l0), "operator split").concludeWith(_.splitOf())
            App(v, PlainTup(acc, Block(rhs)))
          case _ => 
            // val rhs = simpleExpr(opPrec(opStr)._2)
            val rhs = expr(opPrec(opStr)._2)
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
              case _ => App(v, PlainTup(acc, rhs))
            }, prec, allowNewlines)
        /*
      case (KEYWORD(":"), l0) :: _ if prec <= NewParser.prec(':') =>
        consume
        R(Asc(acc, typ(0)))
      case (KEYWORD("where"), l0) :: _ if prec <= 1 =>
        consume
        val tu = typingUnitMaybeIndented
        val res = Where(acc, tu.entities).withLoc(S(l0))
        exprCont(res, prec, allowNewlines = false)
        */
      case (SPACE, l0) :: _ =>
        consume
        acc match // TODO: looks fishy. a better way?
          case Sel(reg, Ident("ref")) => RegRef(reg, simpleExprImpl(0))
          case _ => exprCont(acc, prec, allowNewlines)
      case (SELECT(name), l0) :: _ => // TODO precedence?
        consume
        exprCont(Sel(acc, new Ident(name).withLoc(S(l0))), prec, allowNewlines)
        /*
      // case (br @ BRACKETS(Indent, (SELECT(name), l0) :: toks), _) :: _ =>
      case (br @ BRACKETS(Indent, (SELECT(name), l0) :: toks), _) :: _ if prec <= 1 =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.exprCont(Sel(acc, Var(name).withLoc(S(l0))), 0, allowNewlines = true))
        if (allowNewlines) res match {
          case L(ifb) => L(ifb) // TODO something else?
          case R(res) => exprCont(res, 0, allowNewlines)
        }
        else res
      case (br @ BRACKETS(Indent, (IDENT(opStr, true), l0) :: toks), _) :: _ =>
        consume
        rec(toks, S(br.innerLoc), br.describe).concludeWith(_.opBlock(acc, opStr, l0))
      case (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
      // case (KEYWORD("then"), _) :: _ if /* expectThen && */ prec <= 1 =>
        consume
        L(IfThen(acc, exprOrBlockContinuation))
      case (NEWLINE, _) :: (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
        consume
        consume
        L(IfThen(acc, exprOrBlockContinuation))
      case (NEWLINE, _) :: _ if allowNewlines =>
        consume
        exprCont(acc, 0, allowNewlines)
        
      case (br @ BRACKETS(Curly, toks), loc) :: _ if prec <= AppPrec =>
        consume
        val tu = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.typingUnitMaybeIndented).withLoc(S(loc))
        exprCont(Rft(acc, tu), prec, allowNewlines)
        
      case (COMMA | SEMI | NEWLINE | KEYWORD("then" | "else" | "in" | "=" | "do")
        | OP(_) | BRACKETS(Curly, _), _) :: _ => R(acc)
      
      case (KEYWORD("of"), _) :: _ if prec <= 1 =>
        consume
        val as = argsMaybeIndented()
        val res = App(acc, Tup(as))
        exprCont(res, prec, allowNewlines)
      case (br @ BRACKETS(Indent, (KEYWORD("of"), _) :: toks), _) :: _ if prec <= 1 =>
        consume
        // 
        // val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        // val res = App(acc, Tup(as))
        // exprCont(res, 0, allowNewlines = true) // ?!
        // 
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith { nested =>
          val as = nested.argsMaybeIndented()
          nested.exprCont(App(acc, Tup(as)), 0, allowNewlines = true)
        }
        // if (allowNewlines) 
        res match {
          case L(ifb) => L(ifb) // TODO something else?
          case R(res) => exprCont(res, 0, allowNewlines)
        }
        // else res
        
      case (BRACKETS(Indent, (KEYWORD("then"|"else"), _) :: toks), _) :: _ => R(acc)
      
      /* 
      case (br @ BRACKETS(Indent, toks), _) :: _ 
      if prec === 0 && !toks.dropWhile(_._1 === SPACE).headOption.map(_._1).contains(KEYWORD("else")) // FIXME
      =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockTerm)
        R(App(acc, res))
      */
      // case (br @ BRACKETS(Indent, (BRACKETS(Round | Square, toks1), _) :: toks2), _) :: _ =>
      case (br @ BRACKETS(Indent, toks @ (BRACKETS(Round | Square, _), _) :: _), _) :: _ if prec <= 1 =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.exprCont(acc, 0, allowNewlines = true))
        res match {
          case L(ifb) => L(ifb) // TODO something else?
          case R(res) => exprCont(res, 0, allowNewlines)
        }
        */
      case (br @ BRACKETS(Angle | Square, toks), loc) :: _ =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockMaybeIndented)
        // val res = TyApp(acc, as.map(_.mapSecond.to))
        val res = TyApp(acc, as).withLoc(acc.toLoc.fold(some(loc))(_ ++ loc |> some))
        exprCont(res, prec, allowNewlines)
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
        exprCont(res, prec, allowNewlines)
      case (KEYWORD(Keyword.`of`), _) :: _ =>
        consume
        val as = blockMaybeIndented
        val res = App(acc, Tup(as))
        exprCont(res, prec, allowNewlines)
      /*
      case c @ (h :: _) if (h._1 match {
        case KEYWORD(":" | "of" | "where" | "extends") | SEMI | BRACKETS(Round | Square, _)
          | BRACKETS(Indent, (
              KEYWORD("of") | SEMI
              | BRACKETS(Round | Square, _)
              | SELECT(_)
            , _) :: _)
          => false
        case _ => true
      }) =>
        val as = argsMaybeIndented()
        val res = App(acc, Tup(as))
        raise(WarningReport(msg"Paren-less applications should use the 'of' keyword"
          -> res.toLoc :: Nil, newDefs = true))
        exprCont(res, prec, allowNewlines)
        */
        
      case (KEYWORD(kw), l0) :: _ if kw.leftPrecOrMin > prec =>
        printDbg(s"$$ found keyword: ${kw.name}")
        ParseRule.infixRules.kwAlts.get(kw.name) match
          case S(rule) =>
            consume
            printDbg(s"$$ proceed with rule: ${rule.name}")
            rule.exprAlt match
              case S(exprAlt) =>
                yeetSpaces match
                  case (NEWLINE, l0) :: _ =>
                    consume
                    ???
                  case _ =>
                printDbg("$ parsing the right-hand side")
                val rhs = expr(kw.rightPrecOrMin, true)
                parseRule(kw.rightPrecOrMin, exprAlt.rest).map: rest =>
                  exprCont(exprAlt.k(rhs, rest)(acc), prec, allowNewlines) // FIXME prec??
                .getOrElse(errExpr)
              case N =>
                // TODO other alts...?
                err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${kw.name} instead" -> S(l0) :: Nil))
                acc
          case _ => acc
      case (tok, _) :: _ =>
        printDbg(s"stops at ${tok.toString}")
        acc
      case Nil =>
        printDbg(s"stops at the end of input")
        acc
    }
  


  



