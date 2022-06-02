package mlscript

import scala.annotation.tailrec
import sourcecode.Name

import utils._, shorthands._
import mlscript.Message._


object NewParser {
  
  // def parse(ts: Iterable[Token], debug: Boolean = false): Term = {
  //   val p = new NewParser(ts.iterator, debug)
  //   val t = p.expr(0)
  //   // printDbg(p.cur)
  //   if (p.cur.nonEmpty) fail(p.cur.toList ++ p.rest)
  //   t
  // }
  
  // val prec: Map[Char,Int] = """
  //   =
  //   @
  //   :
  //   |
  //   ^
  //   &
  //   < >
  //   + -
  //   * / %
  //   !
  // """.split('\n').zipWithIndex.flatMap { (cs, i) =>
  //     cs.filterNot(_.isWhitespace).map(_ -> i)
  // }.toMap.withDefaultValue(Int.MaxValue) // prec('~') == 2147483647
}

abstract class NewParser(origin: Origin, tokens: Ls[Token -> Loc], raise: Diagnostic => Unit, val dbg: Bool) {

  def mkLoc(l: Int, r: Int): Loc =
    Loc(l, r, origin)

  def printDbg(msg: => Any): Unit
  
  def parseAll[R](parser: => R): R = {
    // val t = expr(0, allowSpace = false)
    val res = parser
    // printDbg(p.cur)
    // if (cur.nonEmpty) fail(cur)
    cur match {
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        raise(CompilationError(msg"Expected end of input; found ${relevantToken.describe} instead" -> S(rl) :: Nil))
      case Nil => ()
    }
    res
  }
  
  // def fail(ts: List[TokLoc]): Unit =
  //   // throw new IllegalArgumentException("Parse failure on: " + ts.mkString("|")) // TODO
  //   raise(CompilationError(msg"Parse failure on: ${ts.mkString("|")}" -> N :: Nil))
  
  type TokLoc = (Token, Loc)
  
  type LTL = Ls[TokLoc]
  
  private val MinPrec = 0
  
  private val prec: Map[Char,Int] =
    List(
      "",
      "",
      "",
      // ^ for keywords
      ",",
      ";",
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
      ".",
    ).zipWithIndex.flatMap {
      case (cs, i) => cs.filterNot(_ === ' ').map(_ -> (i + 1))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  def opCharPrec(opChar: Char): Int = prec(opChar)
  def opPrec(opStr: Str): (Int, Int) = opStr match {
    case "and" => (2, 2)
    case "or" => (1, 1)
    case _ =>
      val r = opStr.last
      (prec(opStr.head), prec(r) - (if (r === '@' || r === '/' || r === ',') 1 else 0))
  }
  
  def pe(msg: Message, l: Loc, rest: (Message, Opt[Loc])*): Unit =
    raise(CompilationError(msg -> S(l) :: rest.toList)) // TODO parse err
  
  
  
  private var _cur: Ls[TokLoc] = tokens
  
  private def cur(implicit n: Name) = {
    if (dbg) printDbg(s"=> ${n.value}\t\tinspects ${NewLexer printTokens _cur}")
    _cur
  }
  
  // val accept: Ls[TokLoc] => Unit =
  //   cur = _
  
  // def block(ts: LTL): (AST, LTL) =
  //   cur match {
  //     case t :: accept() => ???
  //     case _ => ???
  //   }
  
  // def next(implicit n: Name): Option[Token] = {
  //   if (dbg) printDbg(s"=> ${n.value}\t\tinspects next ${_next}")
  //   _next
  // }
  def consume(implicit n: Name): Unit = {
    if (dbg) printDbg(s"=> ${n.value}\t\tconsumes ${NewLexer printTokens _cur}")
    _cur = _cur.tailOption.getOrElse(Nil) // FIXME throw error if empty?
    // _next = ite.nextOption
  }
  def skip(tk: Token, ignored: Set[Token] = Set(SPACE), allowEnd: Bool = false, note: => Ls[Message -> Opt[Loc]] = Nil)
        (implicit n: Name): Opt[Loc] = {
    require(!ignored(tk))
    // if (!cur.headOption.forall(_._1 === tk)) {
    //   // fail(cur)
    //   raise(CompilationError(msg"Expected: ${tk.describe}; found: ${ts.mkString("|")}" -> N :: Nil))
    // }
    val res = cur match {
      case (tk2, l2) :: _ =>
        if (ignored(tk2)) {
          consume
          skip(tk, ignored, allowEnd, note)
        } else if (tk2 =/= tk)
          raise(CompilationError(msg"Expected ${tk.describe}; found ${tk2.describe} instead" -> S(l2) :: note))
        S(l2)
      case Nil =>
        if (!allowEnd)
          raise(CompilationError(msg"Expected ${tk.describe}; found end of input instead" -> lastLoc :: note))
        N
    }
    consume
    res
  }
  private def skipDeindent = 
    cur match {
      case (DEINDENT, _) :: _ => consume
      case (NEWLINE, l0) :: _ => consume; _cur ::= (INDENT, l0)
      case Nil => ()
      case (tk, l0) :: _ =>
        raise(CompilationError(msg"Expected deindent; found ${tk.describe} instead" -> S(l0) :: Nil))
    }
  
  import BracketKind._
  
  private lazy val lastLoc =
    tokens.lastOption.map(_._2.right)
  
  private def curLoc = _cur.headOption.map(_._2)
  
  def blockTerm: Term = {
    val ts = block
    // skip(DEINDENT, allowEnd = true, note =
    //   msg"Note: unmatched indentation is here:" -> S(l0) :: Nil)
    // R(Blk(ts)) // TODO
    val es = ts.map {
      case L(t) =>
        raise(CompilationError(msg"Unexpected 'then' clause" -> t.toLoc :: Nil))
        errExpr
      case R(e) => e
    }
    Blk(es)
  }
  
  def block: Ls[IfBody \/ Term] =
    cur match {
      case (DEINDENT, _) :: _ => Nil
      case (NEWLINE, _) :: _ => consume; block
      case _ =>
        val t = exprOrIf(0, allowSpace = false)
        cur match {
          case (NEWLINE, _) :: _ => consume; t :: block
          case _ => t :: Nil
        }
    }
  
  def expr(prec: Int, allowSpace: Bool = true): Term =
    exprOrIf(prec, allowSpace) match {
      case R(e) => e
      case L(e) =>
        // ??? // TODO
        raise(CompilationError(msg"Expected an expression; found a 'then' clause instead" -> e.toLoc :: Nil))
        errExpr
    }
  
  private def warnDbg(msg: Any, loco: Opt[Loc] = curLoc): Unit =
    raise(Warning(msg"[${cur.headOption.map(_._1).mkString}] ${""+msg}" -> loco :: Nil))
  
  def exprOrIf(prec: Int, allowSpace: Bool = true): IfBody \/ Term =
    cur match {
      case (SPACE, l0) :: _ if allowSpace =>
        consume
        exprOrIf(prec, allowSpace)
      case (INDENT, l0) :: _ if allowSpace =>
        consume
        val ts = block
        skip(DEINDENT, allowEnd = true, note =
          // msg"Note: unmatched indentation is here:" -> S(l0) :: Nil)
          msg"Note: indented block starts here:" -> S(l0) :: Nil)
        // R(Blk(ts)) // TODO
        val es = ts.map { case L(t) => return L(IfBlock(ts)); case R(e) => e }
        R(Blk(es))
      // case (NEWLINE, l0) :: _ =>
      //   Tup(Nil).withLoc(lastLoc)
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme).withLoc(S(l0)), prec)
      case (OPEN_BRACKET(bk), l0) :: _ =>
        consume
        // val res = expr(0)
        val res = args(Nil)
        val l1 = skip(CLOSE_BRACKET(bk), note =
          msg"Note: unmatched ${bk.name} was opened here:" -> S(l0) :: Nil)
        exprCont(Bra(bk === Curly, Tup(res)).withLoc(S(l0 ++ l1)), prec)
      // case Oper(opStr) :: _ if isPrefix(opStr) && opPrec(opStr)._1 > prec =>
      // case (IDENT(opStr, true), l0) :: _ if isPrefix(opStr) =>
      //   consume
      //   val rhs = expr(opPrec(opStr)._2)
      //   exprCont(Prefix(opStr, rhs), prec)
      case (KEYWORD("if"), l0) :: _ =>
        consume
        /* 
        val cond = expr(0)
        skip(KEYWORD("then"), ignored = Set(SPACE, NEWLINE), note =
          msg"Note: unmatched if here:" -> S(l0) :: Nil)
        val thn = expr(0)
        */
        val body = exprOrIf(0) match {
          case L(b) => b
          case R(e) =>
            // ??? // TODO
            /* 
            val (desc, loc) = _cur match {
              case (tk, l1) :: _ => (tk.describe, S(l1))
              case Nil => (e.describe, e.toLoc)
            }
            raise(CompilationError(msg"Expected 'then' clause; found ${desc} instead" -> 
                // e.toLoc ::
                // curLoc ::
                loc ::
              msg"Note: 'if' expression started here:" -> S(l0) :: Nil))
            */
            val (found, loc) = _cur.dropWhile(_._1 === SPACE) match {
              case (tk, l1) :: _ => (msg"${e.describe} followed by ${tk.describe}",
                // e.toLoc.fold(S(l1))(_ ++ l1 |> some))
                // e.toLoc.fold(S(l1))(_ ++ l1 |> some))
                S(e.toLoc.fold(l1)(_ ++ l1)))
                // e.toLoc.orElse(S(l1)))
              case Nil => (msg"${e.describe}", e.toLoc)
            }
            raise(CompilationError(msg"Expected 'then' clause; found $found instead" -> loc ::
              msg"Note: 'if' expression started here:" -> S(l0) :: Nil))
            IfThen(e, errExpr)
        }
        // warnDbg("huh")
        
        // val els = cur match {
        //   case (KEYWORD("else"), _) :: _ => 
        //   case _ => N
        // }
        val (hasEls, hasIndent) = cur match {
          case (SPACE, _) :: (KEYWORD("else"), _) :: _ => consume; (true, false) // no changes?
          case (KEYWORD("else"), _) :: _ => consume; (true, false)
          case (NEWLINE, _) :: (KEYWORD("else"), _) :: _ => consume; consume; (true, false)
          case (INDENT, _) :: (KEYWORD("else"), _) :: _ => consume; consume; (true, true) // FIXME consume matching DEINDENT
          case _ => (false, false)
        }
        // raiseDbg(hasEls)
        val els = Option.when(hasEls)(expr(0))
        // R(If(IfThen(cond, thn), els))
        if (hasIndent) skipDeindent
        R(If(body, els))
      case Nil =>
        raise(CompilationError(msg"Unexpected end of input; an expression was expected here" -> lastLoc :: Nil))
        R(errExpr)
      case //Nil | 
      ((CLOSE_BRACKET(_) /* | NEWLINE | DEINDENT */, _) :: _)=>
        R(UnitLit(true))
        // R(errExpr) // TODO
      case (tk, l0) :: _ =>
        // fail(cur)
        raise(CompilationError(msg"Unexpected ${tk.describe} in expression position" -> S(l0) :: Nil))
        consume
        exprOrIf(prec)
  }
  
  private def errExpr =
    // Tup(Nil).withLoc(lastLoc) // TODO FIXME produce error term instead
    UnitLit(true).withLoc(lastLoc) // TODO FIXME produce error term instead
  
  def exprCont(acc: Term, prec: Int): IfBody \/ Term = {
    implicit val n: Name = Name(s"exprCont($prec)")
    cur match {
      case (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        // val rhs = expr(opPrec(opStr)._2)
        // // exprCont(Infix(acc, opStr, rhs), prec)
        // exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
        val v = Var(opStr).withLoc(N/*TODO*/)
        exprOrIf(opPrec(opStr)._2) match {
          case L(rhs) =>
            L(IfOpApp(acc, v, rhs))
          case R(rhs) =>
            exprCont(App(App(v, acc), rhs), prec)
        }
      // case Oper(opStr) :: _ if isPostfix(opStr) =>
      // case Oper(opStr) :: _ if isPostfix(opStr) && opPrec(opStr)._1 > prec =>
      //   consume
      //   exprCont(Postfix(acc, opStr), prec)
      case (SPACE, l0) :: _ =>
        consume
        exprCont(acc, prec)
      // case (SPACE, l0) :: _ =>
      case (NEWLINE, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        // ??? // TODO
        consume
        consume
        val rhs = expr(opPrec(opStr)._2) // TODO if
        exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
      // case (NEWLINE, _) :: (INDENT, _) :: (IDENT(opStr, true), l0) :: _ =>
      case (INDENT, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        // consume
        // ??? // TODO
        consume
        consume
        val rhs = expr(opPrec(opStr)._2) // TODO if
        skipDeindent
        exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
      case Nil => R(acc)
      case (KEYWORD("then"), _) :: _ =>
        consume
        val e = expr(0)
        L(IfThen(acc, e))
      case (NEWLINE, _) :: (KEYWORD("then"), _) :: _ =>
        consume
        consume
        val e = expr(0)
        L(IfThen(acc, e))
      case (INDENT, _) :: (KEYWORD("then"), _) :: _ =>
        consume
        consume
        val e = expr(0)
        // skip(DEINDENT)
        skipDeindent
        L(IfThen(acc, e))
      case (DEINDENT | COMMA | NEWLINE | KEYWORD("then" | "else") | CLOSE_BRACKET(Round) | IDENT(_, true), _) :: _ => R(acc)
      
      // case c =>
      // case c @ ((KEYWORD("of"), _) :: _ | (OPEN_BRACKET(Round), _) :: _) =>
      // case c @ (h :: _) if h._1 =/= INDENT =>
      case c @ (h :: _) if (h._1 match {
        case INDENT => false
        case CLOSE_BRACKET(_) => false
        case _ => true
      }) =>
        val ofLess = c match {
          case (KEYWORD("of"), _) :: _ =>
            consume
            false
          case _ =>
            true
        }
        // val ofKw = curLoc
        val openedPar = cur match {
          case (OPEN_BRACKET(Round), l0) :: _ => consume; S(l0)
          case (SPACE, _) :: (OPEN_BRACKET(Round), l0) :: _ => consume; consume; S(l0)
          case _ => N
        }
        val as = args(Nil)
        // val res = App(acc, Tup(as.map(_.mapSecond(_ -> false))))
        val res = App(acc, Tup(as))
        openedPar match {
          case S(l0) =>
            skip(CLOSE_BRACKET(Round), note =
              msg"Note: unmatched application parenthesis was opened here:" -> S(l0) :: Nil)
            exprCont(res, 0)
          case N =>
            if (ofLess)
              raise(Warning(msg"Paren-less applications should use the 'of' keyword"
                // -> ofKw :: Nil))
                -> res.toLoc :: Nil))
            R(res)
        }
      case _ => R(acc)
    }
  }
  
  // TODO support comma-less arg blocks...
  def args(acc: Ls[Opt[Var] -> (Term -> Bool)]): Ls[Opt[Var] -> (Term -> Bool)] =
    cur match {
      case (SPACE, _) :: _ =>
        consume
        args(acc)
      case (NEWLINE | IDENT(_, true), _) :: _ => // TODO: | ...
        acc.reverse
      case _ =>
    // }
    // {
    
    val argMut = cur match {
      case (KEYWORD("mut"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argName = cur match {
      case (IDENT(idStr, false), l0) :: (IDENT(":", true), _) :: _ =>
        consume
        consume
        S(Var(idStr).withLoc(S(l0)))
      case _ => N
    }
    val e = expr(MinPrec) -> argMut.isDefined
    cur match {
      case (COMMA, l0) :: _ =>
        consume
        args((argName -> e) :: acc)
      case _ =>
        ((argName -> e) :: acc).reverse
    }
    
  }
  
  
  
}

