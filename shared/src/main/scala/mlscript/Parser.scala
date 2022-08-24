package mlscript

import scala.annotation.nowarn
import scala.util.chaining._
import scala.language.implicitConversions
import fastparse._
import mlscript.utils._, shorthands._
import mlscript.Lexer._

/** Inspired by and adapted from:
  *   scalaparse: https://github.com/lihaoyi/fastparse/tree/master/scalaparse
  *   pythonparse: https://github.com/lihaoyi/fastparse/tree/master/pythonparse
  */
@nowarn("cat=other") // "comparing a fresh object using `ne` will always yield true" in macrco-generated code
@SuppressWarnings(Array("org.wartremover.warts.All"))
class Parser(origin: Origin, indent: Int = 0, recordLocations: Bool = true) {
  //implicit def whitespace(cfg: P[_]): P[Unit] = Lexical.wscomment(cfg)
  implicit def whitespace(cfg: P[_]): P[Unit] = Lexer.nonewlinewscomment(cfg)
  
  lazy val nextLevel = new Parser(origin: Origin, indent + 1, recordLocations)
  
  def toParams(t: Term) = t
  
  def UnitLit = Tup(Nil)
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[p:P, L <: Located](tree: => P[L]) = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => n.withLoc(i0, i1, origin)
  }
  
  def space[p: P] = P( CharIn(" \n") )
  def NEWLINE[p: P]: P0 = P( "\n" | End )
  def ENDMARKER[p: P]: P0 = P( End ).opaque("unexpected token in this position")
  
  def nl_indents[p: P] = P( "\n" ~~ emptyLines ~~ " ".repX(indent, max = indent) )
  def emptyLines[p: P] = P( ("" ~ Lexer.comment.? ~ "\n").repX(0) )
  
  def spaces[p: P] = P( (Lexer.nonewlinewscomment.? ~~ "\n").repX(1) )
  
  def NAME[p: P]: P[Var] = locate(ident.map(Var(_)))
  
  def ident[p: P] = Lexer.identifier | "(" ~ operator.! ~ ")"
  
  def NUMBER[p: P]: P[Lit] = locate(
    P( Lexer.longinteger | Lexer.integer ).map(IntLit) |
    P( Lexer.floatnumber ).map(DecLit)
  )
  def STRING[p: P]: P[StrLit] = locate(Lexer.stringliteral.map(StrLit(_)))
  
  def expr[p: P]: P[Term] = P( ite | basicExpr ).opaque("expression")
  
  def ite[p: P]: P[Term] = P( kw("if") ~/ expr ~ kw("then") ~ expr ~ kw("else") ~ expr ).map { ite =>
    App(App(App(Var("if"), ite._1), ite._2), ite._3)
  }
  
  def basicExpr[p: P]: P[Term] = P( lams ~ operator_suite.? ).map {
    case (lhs, N) => lhs
    case (lhs, S(ops)) => ops.foldLeft(lhs) {
      case (acc, (op, rhs)) => App(App(op, acc), rhs)
    }
  }.opaque("expression")
  
  def stmt[p: P]: P[Statement] = defn | let | expr
  
  def datatypeDefn[p: P]: P[DatatypeDefn] = P(
      kw("data") ~ kw("type") ~/ expr ~ emptyLines ~
      ( kw("of") ~ (binops.rep(1, ",").map(es => Blk(es.toList)) | suite) ).?
    ).map {
      case (hd, N) => DatatypeDefn(hd, Blk(Nil))
      case (hd, S(cs)) => DatatypeDefn(hd, cs)
    }.opaque("data type definition")
  
  def dataDefn[p: P]: P[DataDefn] = P( kw("data") ~/ expr ).map(DataDefn(_)).opaque("data definition")
  
  def defn[p: P]: P[Statement] = datatypeDefn | dataDefn
  
  def let[p: P]: P[LetS] =
    locate(P( kw("let") ~ kw("rec").!.? ~ commas ~ "=" ~/ (expr | suite) ).map {
      case (r, p, e) => LetS(r.isDefined, p, e)
    }).opaque("let binding")
  
  def multilineBlock[p: P]: P[Blk] =
    P( stmt ~ (";" ~ stmt).rep ~ (";".? ~ nl_indents ~~ multilineBlock).? ).map {
      case (s, ss1, N) => Blk(s :: ss1.toList)
      case (s, ss1, S(Blk(ss2))) => Blk(s :: ss1.toList ::: ss2.toList)
    }
  def operatorBlock[p: P]: P[Seq[(Var, Term)]] =
    P( Index ~~ operator.! ~~ Index ~ expr ~ (nl_indents ~~ operatorBlock).? ).map {
      case (i0, op, i1, t, opts) => (Var(op).withLoc(i0, i1, origin), t) +: opts.toList.flatten
    }
  
  def lams[p: P]: P[Term] = P( commas ~ (("/".! | "=>".!) ~/ (expr | suite) | "".! ~ suite).? ).map(checkless {
    case (trm, N) => trm
    case (trm, S(("", rest))) => App(trm, toParams(rest))
    case (trm, S(("/", rest))) => App(trm, toParams(rest))
    case (trm, S(("=>", rest))) => Lam(toParams(trm), rest)
  }).opaque("applied expressions")
  
  // TODO support spreads ""...xs""
  def commas[p: P]: P[Term] = P(
    Index ~~ (NAME ~ ":" ~ (noCommas | suite) | noCommas.map(Var("") -> _)).rep(1, ",").map(_.toList) ~ ",".!.? ~~ Index
  ).map {
    case (_, (Var(""), x) :: Nil, N, _) => x
    case (i0, xs, _, i1) => Tup(xs.map { case (n, t) => (n optionIf (_.name.nonEmpty), Fld(false, false, t)) }).withLoc(i0, i1, origin)
  }
  
  def booleans[p: P]: P[Term] = P(binops rep (1, kw("and")) rep (1, kw("or"))) // TODO locs
    .map(_.map(_.reduce((l, r) => App(OpApp("and", l), r))).reduce((l, r) => App(OpApp("or", l), r)))
  def noCommas[p: P]: P[Term] = P(booleans ~ ((kw("as") | kw("is")).! ~ booleans).rep).map {
    case (lhs, casts) => casts.foldLeft(lhs) {
      case (acc, ("as", rhs)) => Bind(acc, rhs)
      case (acc, ("is", rhs)) => Test(acc, rhs)
    }
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
  def binops[p: P]: P[Term] =
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
              result = App(App(Var(op).withLoc(off0, off1, origin), result), rhs)
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
  def apps[p: P]: P[Term] = P( atomOrSelect.rep(1) ~ suite.? ).map {
    case (as, ao) => (as ++ ao.toList).reduceLeft((f, a) => App(f, toParams(a)))
  }
  
  def atomOrSelect[p: P]: P[Term] = P(atom ~ (Index ~~ "." ~ NAME ~~ Index).rep).map {
    case (lhs, sels) => sels.foldLeft(lhs) {
      case (acc, (i0,str,i1)) => Sel(lhs, str).withLoc(i0, i1, origin)
    }
  }
  
  def recordBrackets[p: P]: P[Term] =
    locate(P( "{" ~ (suite | nextLevel.multilineBlock).? ~ nl_indents.? ~ "}" )
      .map(xo => Bra(true, xo.getOrElse(Tup(Nil)))))
  
  def tupleBrackets[p: P]: P[Term] =
    locate(P( "(" ~ (suite | nextLevel.multilineBlock).? ~ nl_indents.? ~ ")" )
      .map(xo => Bra(false, xo.getOrElse(Tup(Nil)))))
  
  def atom[p: P]: P[Term] = P(tupleBrackets | recordBrackets | STRING | NAME | NUMBER)
  
  def nextIndentP[p: P]: P[Int] = " ".repX(indent + 1).!.map(_.length)
  def indented[p: P, A](p: Parser => P[A]): P[A] = "\n" ~~ emptyLines ~~ nextIndentP.flatMapX { nextIndent =>
    p(new Parser(origin, nextIndent, recordLocations))
  }
  def suite[p: P]: P[Term] =
    P( indented(_.multilineBlock) ).opaque("indented block")
  def operator_suite[p: P]: P[Seq[(Var, Term)]] =
    P( indented(_.operatorBlock) ).opaque("operators block")
  
  
  // def repl_input[p: P]: P[Term] = P( (expr | P("").map(_ => UnitLit)) ~ ENDMARKER )
  
  def pgrm[p: P]: P[Pgrm] = P( multilineBlock ~  emptyLines ~ End map (b => Pgrm(b.stmts)) )
  
}
