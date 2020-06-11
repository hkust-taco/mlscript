package funtypes

import funtypes.utils._, shorthands._
import scala.language.implicitConversions
import scala.util.chaining._
import Lexer._
import fastparse._

/** Inspired by and adapted from:
  *   scalaparse: https://github.com/lihaoyi/fastparse/tree/master/scalaparse
  *   pythonparse: https://github.com/lihaoyi/fastparse/tree/master/pythonparse
  */
@SuppressWarnings(Array("org.wartremover.warts.All"))
class Parser(indent: Int = 0, recordLocations: Bool = true) {
  //implicit def whitespace(cfg: P[_]): P[Unit] = Lexical.wscomment(cfg)
  implicit def whitespace(cfg: P[_]): P[Unit] = Lexer.nonewlinewscomment(cfg)
  
  def UnitLit = Tup(Nil)
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[_:P, L <: Located](tree: => P[L]) = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => n.withLoc(i0, i1)
  }
  
  def space[_: P] = P( CharIn(" \n") )
  def NEWLINE[_: P]: P0 = P( "\n" | End )
  def ENDMARKER[_: P]: P0 = P( End )//.opaque("unexpected token in this position")
  
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
  
  def expr[_: P]: P[Term] = P( emptyLines ~ multilineBlock ~ emptyLines )
  
  def stmt[_: P]: P[Statement] = let | lams
  
  def let[_: P]: P[LetS] =
    locate(P( kw("let") ~ kw("rec").!.? ~ commas ~ "=" ~/ (lams | suite) ).map {
      case (r, p, e) => LetS(r.isDefined, p, e)
    }).opaque("let binding")
  
  def multilineBlock[_: P]: P[Blk] = P( stmt ~ (";" ~ stmt).rep ~ (";".? ~ nl_indents ~~ multilineBlock).? ).map {
    case (s, ss1, N) => Blk(s :: ss1.toList)
    case (s, ss1, S(Blk(ss2))) => Blk(s :: ss1.toList ::: ss2.toList)
  }
  
  def lams[_: P]: P[Term] = P( commas ~ (("/".! | "=>".!) ~/ (lams | suite) | "".! ~ suite).? ).map {
    case (trm, N) => trm
    case (trm, S(("", rest))) => App(trm, rest)
    case (trm, S(("/", rest))) => App(trm, rest)
    case (trm, S(("=>", rest))) => Lam(trm, rest)
  }.opaque("applied expressions")
  
  def commas[_: P]: P[Term] = P( binops ~/ (Index ~~ "," ~~ Index ~/ commas).? ).map {
    case (lhs, N) => lhs
    case (lhs, S((i0,i1,rhs))) => App(App(Var(",").withLoc(i0,i1), lhs), rhs) // TODO
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
  def binops[_: P]: P[Term] = P(apps ~ (Index ~~ operator.! ~~ Index ~/ apps).rep ~ "").map { case (pre, fs) =>
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
  
  def apps[_: P]: P[Term] = P( atomOrSelect.rep(1) ~ suite.? ).map {
    case (as, ao) => (as ++ ao.toList).reduceLeft(App(_, _))
  }
  
  def atomOrSelect[_: P]: P[Term] = P(atom ~ (Index ~~ "." ~ ident ~~ Index).?).map {
    case (lhs, Some((i0,str,i1))) => Sel(lhs, str).withLoc(i0, i1)
    case (lhs, None) => lhs
  }
  
  // TOOD support suite
  def record[_: P]: P[Term] =
    locate(P( "{" ~ (ident ~ ":" ~ (binops | suite)).rep(sep = ",") ~ "}" ).map(_.toList pipe Rcd))
  
  def atom[_: P]: P[Term] =
    P(locate("(" ~ (suite | blockWithIndentedNextLines) ~ nl_indents.? ~ ")") | STRING | NAME | NUMBER | record)
  
  def blockWithIndentedNextLines[_: P] =
    new Parser(indent + 1).multilineBlock
  
  def suite[_: P]: P[Term] = {
    def nextIndentP = " ".repX(indent + 1).!.map(_.length)
    def indented = "\n" ~~ emptyLines ~~ nextIndentP.flatMapX{ nextIndent =>
      new Parser(nextIndent,recordLocations).multilineBlock
    }
    P( indented ).opaque("indented block")
  }
  
  def repl_input[_: P]: P[Term] = P( (expr | P("").map(_ => UnitLit)) ~ ENDMARKER )
  
  def pgrm[_: P]: P[Blk] = P( multilineBlock ~ End )
  
}
