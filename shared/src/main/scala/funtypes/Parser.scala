package funtypes

import scala.annotation.nowarn
import scala.util.chaining._
import scala.language.implicitConversions
import fastparse._
import funtypes.utils._, shorthands._
import funtypes.Lexer._

/** Inspired by and adapted from:
  *   scalaparse: https://github.com/lihaoyi/fastparse/tree/master/scalaparse
  *   pythonparse: https://github.com/lihaoyi/fastparse/tree/master/pythonparse
  */
@nowarn("cat=other") // "comparing a fresh object using `ne` will always yield true" in macrco-generated code
@SuppressWarnings(Array("org.wartremover.warts.All"))
class Parser(indent: Int = 0, recordLocations: Bool = true) {
  //implicit def whitespace(cfg: P[_]): P[Unit] = Lexical.wscomment(cfg)
  implicit def whitespace(cfg: P[_]): P[Unit] = Lexer.nonewlinewscomment(cfg)
  
  lazy val nextLevel = new Parser(indent + 1, recordLocations)
  
  def UnitLit = Tup(Nil)
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[_:P, L <: Located](tree: => P[L]) = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => n.withLoc(i0, i1)
  }
  
  def space[_: P] = P( CharIn(" \n") )
  def NEWLINE[_: P]: P0 = P( "\n" | End )
  def ENDMARKER[_: P]: P0 = P( End ).opaque("unexpected token in this position")
  
  def nl_indents[_: P] = P( "\n" ~~ emptyLines ~~ " ".repX(indent, max = indent) )
  def emptyLines[_: P] = P( ("" ~ Lexer.comment.? ~ "\n").repX(0) )
  
  def spaces[_: P] = P( (Lexer.nonewlinewscomment.? ~~ "\n").repX(1) )
  
  def NAME[_: P]: P[Var] = locate(ident.map(Var(_)))
  
  def ident[_: P] = Lexer.identifier | "(" ~ operator.! ~ ")"
  
  def NUMBER[_: P]: P[Lit] = locate(
    P( Lexer.longinteger | Lexer.integer ).map(IntLit) |
    P( Lexer.floatnumber ).map(DecLit)
  )
  def STRING[_: P]: P[StrLit] = locate(Lexer.stringliteral.map(StrLit(_)))
  
  def expr[_: P]: P[Term] = P( ite | basicExpr ).opaque("expression")
  
  def ite[_: P]: P[Term] = P( kw("if") ~/ expr ~ kw("then") ~ expr ~ kw("else") ~ expr ).map { ite =>
    App(App(App(Var("if"), ite._1), ite._2), ite._3)
  }
  
  def basicExpr[_: P]: P[Term] = P( lams ~ operator_suite.? ).map {
    case (lhs, N) => lhs
    case (lhs, S(ops)) => ops.foldLeft(lhs) {
      case (acc, (op, rhs)) => App(App(op, acc), rhs)
    }
  }.opaque("expression")
  
  def stmt[_: P]: P[Statement] = let | expr
  
  def let[_: P]: P[LetS] =
    locate(P( kw("let") ~ kw("rec").!.? ~ commas ~ "=" ~/ (expr | suite) ).map {
      case (r, p, e) => LetS(r.isDefined, p, e)
    }).opaque("let binding")
  
  def multilineBlock[_: P]: P[Blk] =
    P( stmt ~ (";" ~ stmt).rep ~ (";".? ~ nl_indents ~~ multilineBlock).? ).map {
      case (s, ss1, N) => Blk(s :: ss1.toList)
      case (s, ss1, S(Blk(ss2))) => Blk(s :: ss1.toList ::: ss2.toList)
    }
  def operatorBlock[_: P]: P[Seq[(Var, Term)]] =
    P( Index ~~ operator.! ~~ Index ~ expr ~ (nl_indents ~~ operatorBlock).? ).map {
      case (i0, op, i1, t, opts) => (Var(op).withLoc(i0, i1), t) +: opts.toList.flatten
    }
  
  def lams[_: P]: P[Term] = P( commas ~ (("/".! | "=>".!) ~/ (expr | suite) | "".! ~ suite).? ).map(checkless {
    case (trm, N) => trm
    case (trm, S(("", rest))) => App(trm, rest)
    case (trm, S(("/", rest))) => App(trm, rest)
    case (trm, S(("=>", rest))) => Lam(trm, rest)
  }).opaque("applied expressions")
  
  // TODO support spreads ""...xs""
  def commas[_: P]: P[Term] =
    P(Index ~~ (ident ~ ":" ~ (binops | suite) | binops.map("" -> _)).rep(1, ",").map(_.toList) ~ ",".!.? ~~ Index)
    .map {
      case (_, ("", x) :: Nil, N, _) => x
      case (i0, xs, _, i1) => Tup(xs.map { case (n, t) => (n optionIf (_.nonEmpty), t) }).withLoc(i0, i1)
    }
  
  /** Note that `,` implicitly has the lowest precedence, followed by the ones below. */
  private val prec: Map[Char,Int] = List(
    //",", // Used to have it here; but that made it left-associative
    ":",
    "|",
    "^",
    "&",
    "= !",
    "< >",
    "+ -",
    "* / %",
    ".",
  ).zipWithIndex.flatMap {
    case (cs,i) => cs.filterNot(_ == ' ').map(_ -> i)
  }.toMap.withDefaultValue(Int.MaxValue)
  
  def precedence(op: String): Int = prec(op.head) min prec(op.last)
  
  // Note: There are three right-associative operators, dealt with above, not here: `=>`, `/`, and `,`
  // Adapted from: https://github.com/databricks/sjsonnet/blob/master/sjsonnet/src/sjsonnet/Parser.scala#L136-L180
  def binops[_: P]: P[Term] =
    P(apps ~ (Index ~~ operator.! ~~ Index ~/ (apps | suite)).rep ~ "")
  // Note: interestingly, the ~/ cut above prevents:  
  //    a +
  //      b +
  //      c
  // from being parsed as:
  //    (a +
  //      b) +
  //      c
  .map { case (pre, fs) =>
    var remaining = fs
    def climb(minPrec: Int, current: Term): Term = {
      var result = current
      while (
        remaining.headOption match {
          case None => false
          case Some((off0, op, off1, next)) =>
            val prec: Int = precedence(op)
            if (prec < minPrec) false
            else {
              remaining = remaining.tail
              val rhs = climb(prec + 1, next)
              result = App(App(Var(op).withLoc(off0, off1), result), rhs)
              true
            }
        }
      )()
      result
    }
    climb(0, pre)
  }
  
  // Note: the `suite.?` here is used in cases like:
  //  foo
  //      bar
  //    baz      // outer app, uses this suite...
  def apps[_: P]: P[Term] = P( atomOrSelect.rep(1) ~ suite.? ).map {
    case (as, ao) => (as ++ ao.toList).reduceLeft(App(_, _))
  }
  
  def atomOrSelect[_: P]: P[Term] = P(atom ~ (Index ~~ "." ~ ident ~~ Index).rep).map {
    case (lhs, sels) => sels.foldLeft(lhs) {
      case (acc, (i0,str,i1)) => Sel(lhs, str).withLoc(i0, i1)
    }
  }
  
  def recordBrackets[_: P]: P[Term] =
    locate(P( "{" ~ (suite | nextLevel.multilineBlock).? ~ nl_indents.? ~ "}" )
      .map(xo => Bra(true, xo.getOrElse(Tup(Nil)))))
  
  def tupleBrackets[_: P]: P[Term] =
    locate(P( "(" ~ (suite | nextLevel.multilineBlock).? ~ nl_indents.? ~ ")" )
      .map(xo => Bra(false, xo.getOrElse(Tup(Nil)))))
  
  def atom[_: P]: P[Term] = P(tupleBrackets | recordBrackets | STRING | NAME | NUMBER)
  
  def nextIndentP[_: P]: P[Int] = " ".repX(indent + 1).!.map(_.length)
  def indented[_: P, A](p: Parser => P[A]): P[A] = "\n" ~~ emptyLines ~~ nextIndentP.flatMapX { nextIndent =>
    p(new Parser(nextIndent, recordLocations))
  }
  def suite[_: P]: P[Term] =
    P( indented(_.multilineBlock) ).opaque("indented block")
  def operator_suite[_: P]: P[Seq[(Var, Term)]] =
    P( indented(_.operatorBlock) ).opaque("operators block")
  
  
  // def repl_input[_: P]: P[Term] = P( (expr | P("").map(_ => UnitLit)) ~ ENDMARKER )
  
  def pgrm[_: P]: P[Blk] = P( multilineBlock ~ End )
  
}
