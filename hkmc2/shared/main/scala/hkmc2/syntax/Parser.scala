package hkmc2
package syntax

import sourcecode.{Name, Line}
import mlscript.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._

import Parser.*


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
      "", // Precedence of application
      ".",
    ).zipWithIndex.flatMap {
      case (cs, i) => cs.filterNot(_ === ' ').map(_ -> (i + Keyword.maxPrec.get))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  // private val CommaPrec = prec(',')
  private val CommaPrec = 0
  private val CommaPrecNext = CommaPrec + 1
  private val AppPrec = prec('.') - 1
  
  final def opCharPrec(opChar: Char): Int = prec(opChar)
  final def opPrec(opStr: Str): (Int, Int) = opStr match {
    case "is" => (4, 4)
    case "and" => (3, 3)
    case "or" => (2, 2)
    case "=>" =>
      // * The lambda operator is special:
      // *  it should associate very strongly on the left and very loosely on the right
      // *  so that we can write things like `f() |> x => x is 0` ie `(f()) |> (x => (x is 0))`
      val eqPrec = prec('.') // * We pick the tightest precedence
      (eqPrec, 1)
      // * Note: we used to do this instead which broke the example above on both sides:
      // val eqPrec = prec('=')
      // (eqPrec, eqPrec - 1)
    case "+." | "-." | "*." =>
      (prec(opStr.head), prec(opStr.head))
    case _ if opStr.exists(_.isLetter) =>
      (5, 5)
    case _ =>
      val r = opStr.last
      (prec(opStr.head), prec(r) - (if r === '@' || r === '/' || r === ',' || r === ':' then 1 else 0))
  }
  
  object KEYWORD:
    def unapply(t: Token): Opt[Str] = t match
      // case IDENT(nme, sym) => Keyword.all.get(nme).map(_.name)
      case IDENT(nme, sym) if Keyword.all.contains(nme) => S(nme)
      case _ => N
  
  object OP:
    def unapply(t: Token): Opt[Str] = t match
      case IDENT(nme, true) if !Keyword.all.contains(nme) => S(nme)
      case _ => N
  
  object ALPHA:
    def unapply(t: Token): Opt[Str] = t match
      case IDENT(nme, false) if !Keyword.all.contains(nme) => S(nme)
      case _ => N
  
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
    }}    [at l.${l.value}]")
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
    Tree.Empty // TODO FIXME produce error term instead
  
  final def err(msgs: Ls[Message -> Opt[Loc]])(implicit l: Line, n: Name): Unit =
    printDbg(s"Error    [at syntax/Parser.scala:${l.value}]")
    raise(ErrorReport(msgs, newDefs = true, source = Diagnostic.Source.Parsing))
  
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
  
  def block: Ls[Tree] = blockOf(ParseRule.prefixRules)
  
  def blockOf(rule: ParseRule[Tree]): Ls[Tree] = wrap(rule.name):
    cur match
    case Nil => Nil
    case (NEWLINE, _) :: _ => consume; blockOf(rule)
    case (SPACE, _) :: _ => consume; blockOf(rule)
    case (tok @ (id: IDENT), loc) :: _ =>
      Keyword.all.get(id.name) match
      case S(kw) =>
        consume
        rule.kwAlts.get(kw.name) match
        case S(subRule) =>
          yeetSpaces match
          case (tok @ BRACKETS(Indent, toks), loc) :: _ if subRule.blkAlt.isEmpty =>
            consume
            rec(toks, S(tok.innerLoc), tok.describe).concludeWith(_.blockOf(subRule))
          case _ =>
            parse(CommaPrecNext, subRule).getOrElse(errExpr) :: blockContOf(rule)
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
                  p.blockOf(subRule.map(e => parse(CommaPrecNext, exprAlt.rest).map(res => exprAlt.k(e, res)).getOrElse(errExpr)))
                } ++ blockContOf(rule)
              case _ =>
                TODO(cur)
            case _ =>
              ParseRule.prefixRules.kwAlts.get(kw.name) match
              case S(subRule) =>
                val e = parse(CommaPrecNext, subRule).getOrElse(errExpr)
                parse(CommaPrecNext, exprAlt.rest).map(res => exprAlt.k(e, res)).getOrElse(errExpr) :: blockContOf(rule)
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
  
  def blockContOf(rule: ParseRule[Tree]): Ls[Tree] =
    yeetSpaces match
      case (COMMA, _) :: _ => consume; blockOf(rule)
      case (SEMI, _) :: _ => consume; blockOf(rule)
      case (NEWLINE, _) :: _ => consume; blockOf(rule)
      case _ => Nil
  
  private def tryParseExp[A](prec: Int, tok: Token, loc: Loc, rule: ParseRule[A]): Opt[A] =
    rule.exprAlt match
      case S(exprAlt) =>
        val e = expr(prec)
        parse(prec, exprAlt.rest).map(res => exprAlt.k(e, res))
      case N =>
        err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
        N
  
  /** A result of None means there was an error (already reported) and nothing could be parsed. */
  def parse[A](prec: Int, rule: ParseRule[A]): Opt[A] = yeetSpaces match
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
        consume
        rule.kwAlts.get(id.name) match
        case S(subRule) =>
          yeetSpaces match
          case (tok @ BRACKETS(Indent, toks), loc) :: _ if subRule.blkAlt.isEmpty =>
            consume
            rec(toks, S(tok.innerLoc), tok.describe).concludeWith(_.parse(kw.assumeRightPrec, subRule))
          case _ =>
            parse(kw.assumeRightPrec, subRule)
        case N =>
          rule.exprAlt match
          case S(exprAlt) =>
            ParseRule.prefixRules.kwAlts.get(id.name) match
            case S(subRule) =>
              // parse(subRule)
              val e = parse(kw.assumeRightPrec, subRule).getOrElse(errExpr)
              parse(prec, exprAlt.rest).map(res => exprAlt.k(e, res))
            case N =>
              // TODO dedup?
              err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
              N
          case N =>
            err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
            N
      case N =>
        tryParseExp(prec, tok, loc, rule)
    case (tok @ NEWLINE, l0) :: (id: IDENT, l1) :: _ if rule.kwAlts.contains(id.name) =>
      consume
      parse(prec, rule)
    case (tok @ (NEWLINE | SEMI | COMMA), l0) :: _ =>
      // TODO(cur)
      rule.emptyAlt match
        case S(res) => S(res)
        case N =>
          err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> lastLoc :: Nil))
          N
    case (tok @ BRACKETS(Indent, toks), loc) :: _ =>
      // rule.blkAlt match
      //   case S(res) => S(res)
      //   case N =>
      //     err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> lastLoc :: Nil))
      //     N
      consume
      rule.blkAlt match
        case S(exprAlt) =>
          val e = rec(toks, S(tok.innerLoc), tok.describe).concludeWith(_.block)
            |> Tree.Block.apply
          parse(prec, exprAlt.rest).map(res => exprAlt.k(e, res))
        case N =>
          
          // TODO... [todo:0]
          // toks match
          //   case 
          
          err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found ${tok.describe} instead" -> S(loc) :: Nil))
          N
    case (tok, loc) :: _ =>
      tryParseExp(prec, tok, loc, rule)
      // TODO(tok)
    case Nil =>
      rule.emptyAlt match
        case S(res) =>
          S(res)
        case N =>
          err((msg"Expected ${rule.whatComesAfter} after ${rule.name}; found end of input instead" -> lastLoc :: Nil))
          N
  
  def expr(prec: Int): Tree = wrap(prec):
    cur match
    case (IDENT(nme, sym), loc) :: _ =>
      consume
      exprCont(Tree.Ident(nme), prec, allowNewlines = true)
    case (LITVAL(lit), loc) :: _ =>
      consume
      exprCont(lit.asTree, prec, allowNewlines = true)
    case (BRACKETS(Round, toks), loc) :: _ if toks.forall(_ is SPACE) =>
      consume
      val res = Tree.UnitLit(false).withLoc(S(loc))
      exprCont(res, prec, allowNewlines = true)
    case (BRACKETS(Round, toks), loc) :: _ =>
      consume
      val res = rec(toks, S(loc), "parenthesized expression").concludeWith(_.expr(0))
      exprCont(res, prec, allowNewlines = true)
    case (BRACKETS(Indent, _), loc) :: _ =>
      err((msg"Expected an expression; found indented block instead" -> lastLoc :: Nil))
      errExpr
    case (tok, loc) :: _ =>
      TODO(tok)
    case Nil =>
      err((msg"Expected an expression; found end of input instead" -> lastLoc :: Nil))
      errExpr
  
  
  import Tree.*
  
  private def unsupportedQuote(loc: Opt[Loc]) = {
    err(msg"This quote syntax is not supported yet" -> loc :: Nil)
    errExpr
  }
  
  final def exprCont(acc: Tree, prec: Int, allowNewlines: Bool): Tree = wrap(prec, s"`$acc`", allowNewlines):
    cur match {
      case (QUOTE, l) :: _ => cur match {
        case _ :: (KEYWORD(opStr @ "=>"), l0) :: _ if opPrec(opStr)._1 > prec =>
          consume
          consume
          exprCont(Quoted(Lam(acc match {
            case t: Tup => t
            case _ => PlainTup(acc)
          }, Unquoted(expr(1)))), prec, allowNewlines)
        case _ :: (br @ BRACKETS(Round, toks), loc) :: _ =>
          consume
          consume
          val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.block)
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
        case _ :: (KEYWORD("in"), _) :: _ =>
          acc
        case _ =>
          consume
          unsupportedQuote(acc.toLoc)
          acc
      }
      case (COMMA, l0) :: _ if prec === 0 =>
        consume
        yeetSpaces match {
          case (NEWLINE, _) :: _ => consume
          case _ =>
        }
        val rhs = expr(prec)
        App(Ident(",").withLoc(S(l0)), PlainTup(acc, rhs))
        /* 
      case (KEYWORD(opStr @ "=>"), l0) :: (NEWLINE, l1) :: _ if opPrec(opStr)._1 > prec =>
        consume
        val rhs = Blk(typingUnit.entities)
        R(Lam(PlainTup(acc), rhs))
        */
      case (KEYWORD(opStr @ "=>"), l0) :: _ if opPrec(opStr)._1 > prec =>
        consume
        val rhs = expr(1)
        val res = Lam(PlainTup(acc), rhs)
        exprCont(res, prec, allowNewlines)
        /* 
      case (IDENT(".", _), l0) :: (br @ BRACKETS(Square, toks), l1) :: _ =>
        consume
        consume
        val idx = rec(toks, S(br.innerLoc), br.describe)
          .concludeWith(_.expr(0, allowSpace = true))
        val newAcc = Subs(acc, idx).withLoc(S(l0 ++ l1 ++ idx.toLoc))
        exprCont(newAcc, prec, allowNewlines)
        */
      case (OP(opStr), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        val v = Ident(opStr).withLoc(S(l0))
        yeetSpaces match {
          case (NEWLINE, l0) :: _ => consume
          case _ =>
        }
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
        exprCont(acc, prec, allowNewlines)
        /*
      case (SELECT(name), l0) :: _ => // TODO precedence?
        consume
        exprCont(Sel(acc, Var(name).withLoc(S(l0))), prec, allowNewlines)
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
        
      case (br @ BRACKETS(Angle | Square, toks), loc) :: _ =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        // val res = TyApp(acc, as.map(_.mapSecond.to))
        val res = TyApp(acc, as.map {
          case (N, Fld(FldFlags(false, false, _), trm)) => trm.toType match {
            case L(d) => raise(d); Top // TODO better
            case R(ty) => ty
          }
          case _ => ???
        }).withLoc(acc.toLoc.fold(some(loc))(_ ++ loc |> some))
        exprCont(res, prec, allowNewlines)
        
      /*case (br @ BRACKETS(Square, toks), loc) :: _ => // * Currently unreachable because we match Square brackets as tparams
        consume
        val idx = rec(toks, S(br.innerLoc), "subscript").concludeWith(_.expr(0))
        val res = Subs(acc, idx.withLoc(S(loc)))
        exprCont(res, prec, allowNewlines)*/
      */
      case (br @ BRACKETS(Round, toks), loc) :: _ if prec <= AppPrec =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.block)
        val res = App(acc, Tup(as).withLoc(S(loc)))
        exprCont(res, prec, allowNewlines)
      case (KEYWORD("of"), _) :: _ =>
        consume
        val as = block
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
        
      case _ => acc
    }
  


  



