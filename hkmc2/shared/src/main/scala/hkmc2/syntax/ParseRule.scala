package hkmc2
package syntax

import sourcecode.{Name, Line}
import mlscript.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._


// * TODO: add lookahead to Expr as a PartialFunction[Ls[Token], Bool]

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

class ParseRule[+A](val name: Str)(val alts: Alt[A]*):
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
  
  val standaloneExpr =
    Expr(ParseRule("expression")(End(())))((l, _: Unit) => l)
  
  def modified(kw: Keyword): Alt[Tree] = modified(kw, standaloneExpr)
  def modified(kw: Keyword, body: Alt[Tree]) =
    Kw(kw)(ParseRule(s"modifier keyword '${kw.name}'")(body)).map(Tree.Modified(kw, _))
  
  val typeDeclTemplate: Alt[Opt[Tree]] =
    Kw(`with`):
      ParseRule("type declaration body")(
        Blk(
          ParseRule("type declaration block"):
            End(())
        ) { case (res, ()) => S(res) }
      )
  
  /*
  def termDefBody(k: TermDefKind): ParseRule[Tree] = 
      ParseRule(s"'${k.str}' binding keyword")(
        Expr(
          ParseRule(s"'${k.str}' binding head")(
            Expr(
              ParseRule(s"'${k.str}' binding name part")(
                funBody(k).map(b => (b, N)),
                funSign(k),
              )
            ) { case (sym, (sign, rhs)) => (S(sym), sign, rhs) },
            funBody(k).map(b => (N, N, b)),
            funSign(k).map(sb => (N, sb._1, sb._2)),
          )
        ) {
          case (lhs, (N, sign, rhs)) => TermDef(k, N, S(lhs), sign, rhs)
          case (lhs, (sym, sign, rhs)) => TermDef(k, S(lhs), sym, sign, rhs)
        }
      )
  */
  def termDefBody(k: TermDefKind): ParseRule[Tree] = 
      ParseRule(s"'${k.str}' binding keyword")(
        Expr(
          ParseRule(s"'${k.str}' binding head")(
            Expr(
              ParseRule(s"'${k.str}' binding name part")(
                funBody(k),
                End(N),
              )
            ) { case (sym, rhs) => (S(sym), rhs) },
            funBody(k).map(b => (N, b)),
            End((N, N)),
          )
        ) {
          case (lhs, (N, rhs)) => TermDef(k, N, S(lhs), rhs)
          case (lhs, (sym, rhs)) => TermDef(k, S(lhs), sym, rhs)
        }
      )
  
  def typeDeclBody(k: TypeDefKind): ParseRule[TypeDef] =
    ParseRule("type declaration start"):
      Expr(
        ParseRule("type declaration head")(
          End((N, N, N)),
          Expr(
            ParseRule("type declaration name")(
              End((N, N)),
              Kw(`extends`):
                ParseRule("extension clause")(
                  Expr(
                    ParseRule("parent specification")(
                      typeDeclTemplate,
                      End(N),
                    )
                  ) { case (ext, bod) => (S(ext), bod) }
                ),
              typeDeclTemplate.map(bod => (N, bod)),
            )
          ):
            case (head, (ext, bod)) => (S(head), ext, bod)
          ,
          Kw(`extends`):
            ParseRule("extension clause")(
              Expr(
                ParseRule("parent specification")(
                  typeDeclTemplate,
                  End(N),
                )
              ) { case (ext, bod) => (N, S(ext), bod) }
            ),
          typeDeclTemplate.map(bod => (N, N, bod)),
        )
      // ) { case (head, ext, bod) => TypeDecl(head, ext, bod) }
      ):
        case (symName, (S(head), ext, bod)) => TypeDef(k, S(symName), head, ext, bod)
        case (head, (N, ext, bod)) => TypeDef(k, N, head, ext, bod)
  
  val prefixRules: ParseRule[Tree] = ParseRule("start of statement")(
    Kw(`let`):
      ParseRule("'let' binding keyword")(
        Expr(
          ParseRule("'let' binding head"):
            Kw(`=`):
              ParseRule("'let' binding equals sign"):
                Expr(
                  ParseRule("'let' binding right-hand side")(
                    Kw(`in`):
                      ParseRule("'let' binding `in` clause"):
                        Expr(ParseRule("'let' binding body")(End(())))((body, _: Unit) => S(body))
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
    Kw(`new`):
      ParseRule("`new` keyword"):
        Expr(ParseRule("`new` expression")(End(())))((body, _: Unit) => New(body))
    ,
    Kw(`in`):
      ParseRule("modifier keyword `in`"):
        Expr(
          ParseRule("`in` expression")(
            Kw(`out`)(ParseRule(s"modifier keyword `out`")(standaloneExpr)).map(s => S(Tree.Modified(`out`, s))),
            End(N),
          )
        ) {
          case (lhs, N) => Tree.Modified(`in`, lhs)
          case (lhs, S(rhs)) => Tup(Tree.Modified(`in`, lhs) :: rhs :: Nil)
        }
    ,
    Kw(`if`):
      ParseRule("`if` keyword")(
        Expr(
          ParseRule("`if` expression")(
            End(N),
            Kw(`else`):
              ParseRule(s"`then` operator `else` clause")(
                Expr(ParseRule(s"`then` operator `else` body")(End(()))):
                  case (body, _) => S(body)
              )
          )
        ):
          case (split, S(default)) =>
            val clause = Modified(`else`, default)
            val items = split match
              case Block(stmts) => stmts.appended(clause)
              case _ => split :: clause :: Nil
            If(Block(items))
          case (split, N) => If(split)
        ,
        Blk(
          ParseRule("`if` block")(End(()))
        ) { case (body, _) => If(body) }
      )
    ,
    Kw(`else`):
      ParseRule("`else` clause")(
        Expr(
          ParseRule("`else` body")(End(()))
        ) { case (tree, _) => Modified(`else`, tree) },
      )
    ,
    Kw(`case`):
      ParseRule("`case` keyword")(
        Blk(ParseRule("`case` branches")(End(())))((body, _: Unit) => Case(body))
      )
    ,
    Kw(`region`):
      ParseRule("`region` keyword"):
        Expr(
          ParseRule("`region` declaration"):
            Kw(`in`):
              ParseRule("`in` keyword")(
                Expr(ParseRule("'region' expression")(End(())))((body, _: Unit) => body),
                Blk(ParseRule("'region' block")(End(())))((body, _: Unit) => body)
              )
        ) { case (name, body) => Region(name, body) }
    ,
    Kw(`fun`)(termDefBody(Fun)),
    Kw(`val`)(termDefBody(Val)),
    Kw(`type`):
      ParseRule("type alias declaration"):
        Expr(
          ParseRule("type alias head"):
            Kw(`=`):
              ParseRule("type alias declaration equals sign"):
                Expr(
                  ParseRule("type alias declaration right-hand side")(
                    End(())
                  )
                ) { (rhs, _) => rhs }
        ) { (lhs, rhs) => TypeDef(Als, N, lhs, S(rhs), N) },
    Kw(`class`)(typeDeclBody(Cls)),
    Kw(`trait`)(typeDeclBody(Trt)),
    Kw(`module`)(typeDeclBody(Mod)),
    modified(`abstract`, Kw(`class`)(typeDeclBody(Cls))),
    modified(`mut`),
    modified(`virtual`),
    modified(`override`),
    modified(`declare`),
    modified(`public`),
    modified(`private`),
    modified(`out`),
    standaloneExpr,
    Kw(`true`)(ParseRule("'true' keyword")(End(BoolLit(true)))),
    Kw(`false`)(ParseRule("'false' keyword")(End(BoolLit(false)))),
  )
  
  val prefixRulesAllowIndentedBlock: ParseRule[Tree] =
    ParseRule(prefixRules.name)(prefixRules.alts :+ 
        (Blk(
          ParseRule("???????????????????????????????????????????"):
            End(())
        ) { case (res, ()) => res })
    : _*)
  
  /* 
  def funSign(k: TermDefKind): Alt[(S[Tree], Opt[Tree])] =
    Kw(`:`):
      ParseRule(s"'${k.str}' binding colon"):
        Expr(
          ParseRule(s"'${k.str}' binding signature")(
            funBody(k),
            End(N),
          )
        ) { case (sign, rhs) => (S(sign), rhs) }
  */
  
  def funBody(k: TermDefKind): Alt[S[Tree]] =
    Kw(`=`):
      ParseRule(s"'${k.str}' binding equals sign")(
        Expr(
          ParseRule(s"'${k.str}' binding right-hand side")(End(()))
        ) { case (rhs, ()) => S(rhs) }
        ,
        Blk(
          ParseRule(s"'${k.str}' binding block")(End(()))
        ) { case (rhs, _) => S(rhs) }
      )

  def genInfixRule[A](kw: Keyword, k: (Tree, Unit) => A): Alt[A] =
    Kw(kw):
      ParseRule(s"'${kw}' operator")(
        Expr(ParseRule(s"'${kw}' operator right-hand side")(End(())))(k)
      )
  
  val infixRules: ParseRule[Tree => Tree] = ParseRule("continuation of statement")(
    genInfixRule(`and`, (rhs, _: Unit) => lhs => InfixApp(lhs, `and`, rhs)),
    genInfixRule(`or`, (rhs, _: Unit) => lhs => InfixApp(lhs, `or`, rhs)),
    genInfixRule(`is`, (rhs, _: Unit) => lhs => InfixApp(lhs, `is`, rhs)),
    genInfixRule(`then`, (rhs, _: Unit) => lhs => InfixApp(lhs, `then`, rhs)),
    genInfixRule(`:`, (rhs, _: Unit) => lhs => InfixApp(lhs, `:`, rhs)),
    genInfixRule(`extends`, (rhs, _: Unit) => lhs => InfixApp(lhs, `extends`, rhs)),
    genInfixRule(`restricts`, (rhs, _: Unit) => lhs => InfixApp(lhs, `restricts`, rhs)),
  )


