package mlscript

import scala.annotation.tailrec
import sourcecode.Name

import utils._, shorthands._
import mlscript.Message._


object NewParser {
  
  // def parse(ts: Iterable[Token], debug: Boolean = false): Term = {
  //   val p = new NewParser(ts.iterator, debug)
  //   val t = p.expr(0)
  //   // println(p.cur)
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

class NewParser(origin: Origin, tokens: Ls[Token -> Loc], raise: Diagnostic => Unit, dbg: Bool) {
  
  def parse: Term = {
    val t = expr(0)
    // println(p.cur)
    // if (cur.nonEmpty) fail(cur)
    cur match {
      case (tk, tkl) :: _ =>
        raise(CompilationError(msg"Expected end of input; found ${tk.describe} token instead" -> S(tkl) :: Nil))
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
    (prec(opStr.head), prec(r) - (if (r == '@' || r == '/' || r == ',') 1 else 0))
  }
  
  def pe(msg: Message, l: Loc, rest: (Message, Opt[Loc])*): Unit =
    raise(CompilationError(msg -> S(l) :: rest.toList)) // TODO parse err
  
  
  
  private var cur: Ls[TokLoc] = tokens
  
  // val accept: Ls[TokLoc] => Unit =
  //   cur = _
  
  // def block(ts: LTL): (AST, LTL) =
  //   cur match {
  //     case t :: accept() => ???
  //     case _ => ???
  //   }
  
  // def next(implicit n: Name): Option[Token] = {
  //   if (dbg) println(s"=> ${n.value}\t\tinspects next ${_next}")
  //   _next
  // }
  def consume(implicit n: Name): Unit = {
    if (dbg) println(s"=> ${n.value}\t\tconsumes ${cur}")
    cur = cur.tailOption.getOrElse(Nil)
    // _next = ite.nextOption
  }
  def skip(tk: Token)(implicit n: Name): Unit = {
    // if (!cur.headOption.forall(_._1 === tk)) {
    //   // fail(cur)
    //   raise(CompilationError(msg"Expected: ${tk.describe}; found: ${ts.mkString("|")}" -> N :: Nil))
    // }
    cur match {
      case (tk2, l2) :: _ =>
        if (tk2 =/= tk)
          raise(CompilationError(msg"Expected ${tk.describe} token; found ${tk2.describe} instead" -> S(l2) :: Nil))
      case Nil =>
        raise(CompilationError(msg"Expected ${tk.describe} token; found end of input instead" -> lastLoc :: Nil))
    }
    consume
  }
  
  import BracketKind._
  
  private lazy val lastLoc =
    tokens.lastOption.map(_._2.right)
  
  def expr(prec: Int): Term =
    cur match {
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme).withLoc(S(l0)), prec)
      case (OPEN_BRACKET(Round), _) :: _ =>
        consume
        val res = expr(0)
        skip(CLOSE_BRACKET(Round))
        exprCont(Bra(true, res), prec)
      // case Oper(opStr) :: _ if isPrefix(opStr) && opPrec(opStr)._1 > prec =>
      // case (IDENT(opStr, true), l0) :: _ if isPrefix(opStr) =>
      //   consume
      //   val rhs = expr(opPrec(opStr)._2)
      //   exprCont(Prefix(opStr, rhs), prec)
      case Nil =>
        // UnitLit
        Tup(Nil).withLoc(lastLoc)
      case (tk, l0) :: _ =>
        // fail(cur)
        raise(CompilationError(msg"Unexpected ${tk.describe} token" -> S(l0) :: Nil))
        consume
        expr(prec)
  }
  
  def exprCont(acc: Term, prec: Int): Term =
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
      case _ => acc
    }
  
  
  
}

