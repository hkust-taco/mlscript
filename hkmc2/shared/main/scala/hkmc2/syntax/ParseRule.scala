package hkmc2
package syntax

import sourcecode.{Name, Line}
import mlscript.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._


enum Alt[+A]:
  case Kw[Rest](kw: Keyword)(val rest: ParseRule[Rest]) extends Alt[Rest]
  case Expr[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case Blk[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case End(a: A)
  
  def map[B](f: A => B): Alt[B] = 
    this match
    case k: Kw[?] => Kw(k.kw)(k.rest.map(f))
    case e: Expr[rest, A] => Expr(e.rest)((tree, rest) => f(e.k(tree, rest)))
    case End(a) => End(f(a))
    case b: Blk[rest, A] => Blk(b.rest)((tree, rest) => f(b.k(tree, rest)))

class ParseRule[+A](val name: Str)(alts: Alt[A]*):
  def map[B](f: A => B): ParseRule[B] =
    ParseRule(name)(alts.map(_.map(f))*)
  
  override def toString: Str = s"$name ::= " + alts.mkString(" | ")
  
  lazy val emptyAlt = alts.collectFirst { case Alt.End(a) => a }
  lazy val kwAlts = alts.collect { case k @ Alt.Kw(kw) => kw.name -> k.rest }.toMap
  lazy val exprAlt = alts.collectFirst { case alt: Alt.Expr[rst, A] => alt }
  lazy val blkAlt = alts.collectFirst { case alt: Alt.Blk[rst, A] => alt }
  
  def whatComesAfter: Str =
    alts.map:
      case Alt.Kw(kw) => s"'${kw.name}' keyword"
      case Alt.Expr(rest) => "expression"
      case Alt.Blk(rest) => "indented block"
      case Alt.End(_) => "end of input"
    .toList
    match
      case Nil => "nothing at all"
      case str :: Nil => str
      case str1 :: str2 :: Nil => s"$str1 or $str2"
      case strs => strs.init.mkString(", ") + ", or " + strs.last

object ParseRule:
  import Keyword.*
  import Alt.*
  import Tree.*
  
  val typeDeclTemplate: Alt[Opt[Tree]] =
    Kw(`with`):
      ParseRule("type declaration body")(
        Blk(
          ParseRule("type declaration block"):
            End(())
        ) { case (res, ()) => S(res) }
      )
  
  val typeDeclBody: ParseRule[TypeDecl] = 
    ParseRule("type declaration start"):
      Expr(
        ParseRule("type declaration head")(
          End((N, N)),
          Kw(`extends`):
            ParseRule("extension clause")(
              // End((N, N)),
              Expr(
                ParseRule("parent specification")(
                  typeDeclTemplate,
                  End(N),
                )
              ) { case (ext, bod) => (S(ext), bod) }
            ),
          typeDeclTemplate.map(bod => (N, bod)),
        )
      // ) { case (head, ext, bod) => TypeDecl(head, ext, bod) }
      ) { case (head, (ext, bod)) => TypeDecl(head, ext, bod) }
  
  val prefixRules: ParseRule[Tree] = ParseRule("prefix expression")(
    Kw(`val`):
      ParseRule("field binding keyword 'val'")(
        Expr(ParseRule("'val' head")(End(())))((body, _: Unit) => body),
        // Expr(ParseRule("'val' head")(End(())))((body, _) => body),
        Blk(
          ParseRule("'val' block"):
            End(())
        ) { case (res, ()) => res }
      ).map(Val.apply),
    Kw(`let`):
      ParseRule("let binding keyword 'let'")(
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
        ,
        // Blk(
        //   ParseRule("let block"):
        //     Kw(`class`):
        //       typeDeclBody
        // ) { case (lhs, body) => Let(lhs, lhs, body) }
      )
    ,
    Kw(`type`)(typeDeclBody),
    Kw(`class`)(typeDeclBody),
    Kw(`trait`)(typeDeclBody),
    Kw(`module`)(typeDeclBody),
    Expr(ParseRule("standalone expression")(End(())))((l, _: Unit) => l),
  )

  // lazy val decl: ParseRule = ParseRule("class declaration",
  //   `class` -> S(ParseRule("class head",
  //     Expression -> S(decl)
  //   ))
  // )


