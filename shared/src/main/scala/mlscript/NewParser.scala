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

  def printDbg(msg: => Any): Unit
  
  def parse: Term = {
    val t = expr(0, allowSpace = false)
    // printDbg(p.cur)
    // if (cur.nonEmpty) fail(cur)
    cur match {
      case (tk, tkl) :: _ =>
        raise(CompilationError(msg"Expected end of input; found ${tk.describe} instead" -> S(tkl) :: Nil))
      case Nil => ()
    }
    t
  }
  
  // def fail(ts: List[TokLoc]): Unit =
  //   // throw new IllegalArgumentException("Parse failure on: " + ts.mkString("|")) // TODO
  //   raise(CompilationError(msg"Parse failure on: ${ts.mkString("|")}" -> N :: Nil))
  
  type TokLoc = (Token, Loc)
  
  type LTL = Ls[TokLoc]
  
  private val MinPrec = 0
  
  private val prec: Map[Char,Int] =
    List(
      "", // for keywords
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
  def opPrec(opStr: Str): (Int, Int) = {
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
  def skip(tk: Token, ignored: Set[Token] = Set(SPACE), allowEnd: Bool = false, note: => Ls[Message -> Opt[Loc]] = Nil)(implicit n: Name): Unit = {
    require(!ignored(tk))
    // if (!cur.headOption.forall(_._1 === tk)) {
    //   // fail(cur)
    //   raise(CompilationError(msg"Expected: ${tk.describe}; found: ${ts.mkString("|")}" -> N :: Nil))
    // }
    cur match {
      case (tk2, l2) :: _ =>
        if (ignored(tk2)) {
          consume
          skip(tk, ignored, allowEnd, note)
        } else if (tk2 =/= tk)
          raise(CompilationError(msg"Expected ${tk.describe}; found ${tk2.describe} instead" -> S(l2) :: note))
      case Nil =>
        if (!allowEnd)
          raise(CompilationError(msg"Expected ${tk.describe}; found end of input instead" -> lastLoc :: note))
    }
    consume
  }
  
  import BracketKind._
  
  private lazy val lastLoc =
    tokens.lastOption.map(_._2.right)
  
  def block: Ls[Term] =
    cur match {
      case (DEINDENT, _) :: _ => Nil
      case (NEWLINE, _) :: _ => consume; block
      case _ =>
        val t = expr(0, allowSpace = false)
        cur match {
          case (NEWLINE, _) :: _ => consume; t :: block
          case _ => t :: Nil
        }
    }
  
  def expr(prec: Int, allowSpace: Bool = true): Term =
    cur match {
      case (SPACE, l0) :: _ if allowSpace =>
        consume
        expr(prec, allowSpace)
      case (INDENT, l0) :: _ if allowSpace =>
        consume
        val ts = block
        skip(DEINDENT, allowEnd = true, note =
          msg"Note: unmatched indentation is here:" -> S(l0) :: Nil)
        Blk(ts)
      // case (NEWLINE, l0) :: _ =>
      //   Tup(Nil).withLoc(lastLoc)
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme).withLoc(S(l0)), prec)
      case (OPEN_BRACKET(Round), l0) :: _ =>
        consume
        val res = expr(0)
        skip(CLOSE_BRACKET(Round), note =
          msg"Note: unmatched parenthesis was opened here:" -> S(l0) :: Nil)
        exprCont(Bra(true, res), prec)
      // case Oper(opStr) :: _ if isPrefix(opStr) && opPrec(opStr)._1 > prec =>
      // case (IDENT(opStr, true), l0) :: _ if isPrefix(opStr) =>
      //   consume
      //   val rhs = expr(opPrec(opStr)._2)
      //   exprCont(Prefix(opStr, rhs), prec)
      case (KEYWORD("if"), l0) :: _ =>
        consume
        val cond = expr(0)
        skip(KEYWORD("then"), ignored = Set(SPACE, NEWLINE), note =
          msg"Note: unmatched if here:" -> S(l0) :: Nil)
        val thn = expr(0)
        // val els = cur match {
        //   case (KEYWORD("else"), _) :: _ => 
        //   case _ => N
        // }
        val hasEls = cur match {
          case (KEYWORD("else"), _) :: _ => consume; true
          case (NEWLINE, _) :: (KEYWORD("else"), _) :: _ => consume; true
          case _ => false
        }
        val els = Option.when(hasEls)(expr(0))
        If(IfThen(cond, thn), els)
      case Nil =>
        // UnitLit
        Tup(Nil).withLoc(lastLoc) // TODO FIXME produce error term instead
      case (tk, l0) :: _ =>
        // fail(cur)
        raise(CompilationError(msg"Unexpected ${tk.describe} in expression position" -> S(l0) :: Nil))
        consume
        expr(prec)
  }
  
  def exprCont(acc: Term, prec: Int): Term = {
    implicit val n: Name = Name(s"exprCont($prec)")
    cur match {
      case (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        val rhs = expr(opPrec(opStr)._2)
        // exprCont(Infix(acc, opStr, rhs), prec)
        exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
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
        val rhs = expr(opPrec(opStr)._2)
        exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
      // case (NEWLINE, _) :: (INDENT, _) :: (IDENT(opStr, true), l0) :: _ =>
      case (INDENT, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        // consume
        // ??? // TODO
        consume
        consume
        val rhs = expr(opPrec(opStr)._2)
        exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
      case Nil => acc
      case (DEINDENT | COMMA | NEWLINE | KEYWORD("then" | "else") | CLOSE_BRACKET(Round) | IDENT(_, true), _) :: _ => acc
      case c =>
        c match {
          case (KEYWORD("of"), _) :: _ =>
            consume
          case _ =>
        }
        val as = args(Nil)
        App(acc, Tup(as.map(_.mapSecond(_ -> false))))
      // case _ => acc
    }
  }
  
  def args(acc: Ls[Opt[Var] -> Term]): Ls[Opt[Var] -> Term] =
    cur match {
      case (SPACE, _) :: _ =>
        consume
        args(acc)
      case (NEWLINE | IDENT(_, true), _) :: _ => // TODO: | ...
        acc.reverse
      case _ =>
    // }
    // {
    
    val argName = cur match {
      case (IDENT(idStr, false), l0) :: (IDENT(":", true), _) :: _ =>
        consume
        consume
        S(Var(idStr).withLoc(S(l0)))
      case _ => N
    }
    val e = expr(MinPrec)
    cur match {
      case (COMMA, l0) :: _ =>
        consume
        args((argName -> e) :: acc)
      case _ =>
        ((argName -> e) :: acc).reverse
    }
    
  }
  
  
  
}

