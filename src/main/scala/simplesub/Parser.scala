package simplesub

import scala.util.chaining._
import fastparse._, fastparse.ScalaWhitespace._
import simplesub.Syntax._

@SuppressWarnings(Array("org.wartremover.warts.All"))
object Parser {
  
  val keywords = Set("let", "rec", "in", "fun", "if", "then", "else")
  def kw[_: P](s: String) = s ~~ !(letter | digit | "_" | "'")
  
  def letter[_: P]     = P( lowercase | uppercase )
  def lowercase[_: P]  = P( CharIn("a-z") )
  def uppercase[_: P]  = P( CharIn("A-Z") )
  def digit[_: P]      = P( CharIn("0-9") )
  def number[_: P]: P[Int] = P( CharIn("0-9").repX(1).!.map(_.toInt) )
  def ident[_: P]: P[String] =
    P( (letter | "_") ~~ (letter | digit | "_" | "'").repX ).!.filter(!keywords(_))
  
  def term[_: P]: P[Term] = P( let | fun | ite | apps )
  def const[_: P]: P[Term] = number.map(Lit)
  def variable[_: P]: P[Term] = ident.map(Var)
  def parens[_: P]: P[Term] = P( "(" ~/ term ~ ")" )
  def subtermNoSel[_: P]: P[Term] = P( parens | record | const | variable )
  def subterm[_: P]: P[Term] = P( subtermNoSel ~ ("." ~/ ident).rep ).map {
    case (st, sels) => sels.foldLeft(st)(Sel) }
  def record[_: P]: P[Term] =
    P( "{" ~/ (ident ~ "=" ~ term).rep(sep = ";") ~ "}" ).map(_.toList pipe Rcd)
  def fun[_: P]: P[Term] = P( kw("fun") ~/ ident ~ "->" ~ term ).map(Lam.tupled)
  def let[_: P]: P[Term] =
    P( kw("let") ~/ kw("rec").!.?.map(_.isDefined) ~ ident ~ "=" ~ term ~ kw("in") ~ term )
    .map(Let.tupled)
  def ite[_: P]: P[Term] = P( kw("if") ~/ term ~ kw("then") ~ term ~ kw("else") ~ term ).map(ite =>
    App(App(App(Var("if"), ite._1), ite._2), ite._3))
  def apps[_: P]: P[Term] = P( subterm.rep(1).map(_.reduce(App)) )
  
  def expr[_: P]: P[Term] = P( term ~ End )
  
  def toplvl[_: P]: P[(Boolean, String, Term)] =
    P( kw("let") ~/ kw("rec").!.?.map(_.isDefined) ~ ident ~ "=" ~ term )
  def pgrm[_: P]: P[Pgrm] = P( ("" ~ toplvl).rep.map(_.toList) ~ End ).map(Pgrm)
  
}
