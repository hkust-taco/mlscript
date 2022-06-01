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
    if (cur.nonEmpty) fail(cur)
    t
  }
  
  def fail(ts: List[TokLoc]): Unit =
    // throw new IllegalArgumentException("Parse failure on: " + ts.mkString("|")) // TODO
    raise(TypeError(msg"Parse failure on: ${ts.mkString("|")}" -> N :: Nil))
  
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
      case (cs, i) => cs.filterNot(_ == ' ').map(_ -> (i + 1))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  def opCharPrec(opChar: Char): Int = prec(opChar)
  def opPrec(opStr: Str): (Int, Int) = {
    val r = opStr.last
    (prec(opStr.head), prec(r) - (if (r == '@' || r == '/' || r == ',') 1 else 0))
  }
  
  def pe(msg: Message, l: Loc, rest: (Message, Opt[Loc])*): Unit =
    raise(TypeError(msg -> S(l) :: rest.toList)) // TODO parse err
  
  
  
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
    cur = cur.tail
    // _next = ite.nextOption
  }
  def skip(tk: Token)(implicit n: Name): Unit = {
    if (!cur.headOption.forall(_._1 === tk)) fail(cur)
    consume
  }
  
  import BracketKind._
  
  def expr(prec: Int): Term =
    cur match {
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme), prec)
      case (OPEN_BRACKET(Round), _) :: _ =>
        consume
        val res = expr(0)
        skip(OPEN_BRACKET(Round))
        exprCont(res, prec)
      // case Oper(opStr) :: _ if isPrefix(opStr) && opPrec(opStr)._1 > prec =>
      // case (IDENT(opStr, true), l0) :: _ if isPrefix(opStr) =>
      //   consume
      //   val rhs = expr(opPrec(opStr)._2)
      //   exprCont(Prefix(opStr, rhs), prec)
      case _ =>
        fail(cur)
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

