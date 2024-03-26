package hkmc2
package syntax

import sourcecode.{Name, Line}
import mlscript.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._


enum Alt[+A]:
  case Kw[Rest](kw: Keyword)(val rest: ParseRule[Rest]) extends Alt[Rest]
  case Expr[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case End(a: A)
  
  def map[B](f: A => B): Alt[B] = 
    this match
    case k: Kw[?] => Kw(k.kw)(k.rest.map(f))
    case e: Expr[rest, A] => Expr(e.rest)((tree, rest) => f(e.k(tree, rest)))
    case End(a) => End(f(a))

class ParseRule[+A](val name: Str)(alts: Alt[A]*):
  def map[B](f: A => B): ParseRule[B] =
    ParseRule(name)(alts.map(_.map(f))*)
  
  lazy val emptyAlt = alts.collectFirst { case Alt.End(a) => a }
  lazy val kwAlts = alts.collect { case k @ Alt.Kw(kw) => kw.name -> k.rest }.toMap
  lazy val exprAlt = alts.collectFirst { case alt: Alt.Expr[rst, A] => alt }
  
  def whatComesAfter: Str =
    alts.map:
      case Alt.Kw(kw) => s"'${kw.name}' keyword"
      case Alt.Expr(rest) => "expression"
      case Alt.End(_) => "end of input"
    .toList
    match
      case Nil => ???
      case str :: Nil => str
      case str1 :: str2 :: Nil => s"$str1 or $str2"
      case strs => strs.init.mkString(", ") + ", or " + strs.last

object ParseRule:
  import Keyword.*
  import Alt.*
  import Tree.*

  val prefixRules: ParseRule[Tree] = ParseRule("prefix expression"):
    Kw(`let`):
      ParseRule("let binding keyword 'let'"):
        Expr(
          ParseRule("let binding head"):
            Kw(`=`):
              ParseRule("let binding equals sign"):
                Expr(
                  ParseRule("let binding right-hand side")(
                    Kw(`in`):
                      ParseRule("let binding `in` clause"):
                        Expr(ParseRule("let binding body")(End(())))((body, _: Unit) => S(body))
                    ,
                    End(N)
                  )
                ) { (rhs, body) => (rhs, body) }
        ) { case (lhs, (rhs, body)) => Let(lhs, rhs, body) }

  // lazy val decl: ParseRule = ParseRule("class declaration",
  //   `class` -> S(ParseRule("class head",
  //     Expression -> S(decl)
  //   ))
  // )


