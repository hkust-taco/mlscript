package hkmc2
package syntax

import sourcecode.{Name, Line}
import mlscript.utils.*, shorthands.*
import hkmc2.Message._
import BracketKind._
import semantics.Elaborator.State


// * TODO: add lookahead to Expr as a PartialFunction[Ls[Token], Bool]

enum Alt[+A]:
  case Kw[Rest](kw: Keyword)(val rest: ParseRule[Rest]) extends Alt[//Loc -> // TODO
    Rest]
  case Expr[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case Blk[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case End(a: A)
  
  def map[B](f: A => B): Alt[B] = 
    this match
    case k: Kw[?] => Kw(k.kw)(k.rest.map(f))
    case e: Expr[rest, A] => Expr(e.rest)((tree, rest) => f(e.k(tree, rest)))
    case End(a) => End(f(a))
    case b: Blk[rest, A] => Blk(b.rest)((tree, rest) => f(b.k(tree, rest)))

class ParseRule[+A](val name: Str, val omitAltsStr: Bool = false)(val alts: Alt[A]*):
  def map[B](f: A => B): ParseRule[B] =
    ParseRule(name)(alts.map(_.map(f))*)
  
  override def toString: Str = s"$name ::= " + alts.mkString(" | ")
  
  lazy val emptyAlt = alts.collectFirst { case Alt.End(a) => a }
  lazy val kwAlts = alts.collect { case k @ Alt.Kw(kw) => kw.name -> k.rest }.toMap
  lazy val exprAlt = alts.collectFirst { case alt: Alt.Expr[rst, A] => alt }
  lazy val blkAlt = alts.collectFirst { case alt: Alt.Blk[rst, A] => alt }
  
  def mkAfterStr: Str = if omitAltsStr then "in this position" else s"after $name"
  
  def whatComesAfter: Str = if omitAltsStr then name else
    alts.map:
      case Alt.Kw(kw) => s"'${kw.name}' keyword"
      case Alt.Expr(rest) => "expression"
      case Alt.Blk(rest) => "block"
      case Alt.End(_) => "end of input"
    .toList
    match
      case Nil => "nothing at all"
      case str :: Nil => str
      case str1 :: str2 :: Nil => s"$str1 or $str2"
      case strs => strs.init.mkString(", ") + ", or " + strs.last

end ParseRule


class ParseRules(using State):
  import Keyword.*
  import Alt.*
  import Tree.*
  
  val standaloneExpr =
    Expr(ParseRule("expression")(End(())))((l, _: Unit) => l)
  
  def modified(kw: Keyword): Alt[Tree] = modified(kw, standaloneExpr)
  def modified(kw: Keyword, body: Alt[Tree]) =
    Kw(kw)(ParseRule(s"modifier keyword '${kw.name}'")(body)).map(Tree.Modified(kw, N, _))
  
  def exprOrBlk[Rest, Res](body: ParseRule[Rest])(k: (Tree, Rest) => Res): List[Alt[Res]] =
    Expr(body)(k) ::
    Blk(body)(k) ::
    Nil

  def typeDeclTemplateThen[A](after: Alt[A]*): Alt[(S[Tree], A)] =
    Kw(`with`):
      ParseRule("type declaration body")(
        Blk(
          ParseRule("type declaration block")(after*)
        ) { case (res, t) => (S(res), t) }
      )
  
  val typeDeclTemplate: Alt[Opt[Tree]] = typeDeclTemplateThen(End(())).map((res, _) => res)
  
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
            funBody(k),
            End(N),
          )
        ) {
          case (lhs, rhs) => TermDef(k, lhs, rhs)
        }
      )
  
  def typeDeclBody(k: TypeDefKind): ParseRule[TypeDef] =
    ParseRule("type declaration keyword"):
      Expr(
        ParseRule("type declaration head")(
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
        case (head, (ext, bod)) =>
          TypeDef(k, head, ext, bod)
  
  def letLike(kw: Keyword.letLike) = 
    Kw(kw):
      ParseRule(s"'${kw.name}' binding keyword")(
        Expr(
          ParseRule(s"'${kw.name}' binding head")(
            Kw(`=`):
              ParseRule(s"'${kw.name}' binding equals sign")(
                exprOrBlk(
                  ParseRule(s"'${kw.name}' binding right-hand side")(
                    Kw(`in`):
                      ParseRule(s"'${kw.name}' binding `in` clause")(
                        exprOrBlk(ParseRule(s"'${kw.name}' binding body")(End(())))((body, _: Unit) => S(body))*
                      ),
                    End(N)
                  )
                ) { (rhs, body) => (S(rhs), body) }*
              ),
            Kw(`in`):
              ParseRule(s"'${kw.name}' binding `in` clause"):
                Expr(ParseRule(s"'${kw.name}' binding body")(End(())))((body, _: Unit) => N -> S(body))
            ,
            End(N -> N)
          )
        ) { case (lhs, (rhs, body)) => LetLike(kw, lhs, rhs, body) }
        ,
        // Blk(
        //   ParseRule("let block"):
        //     Kw(`class`):
        //       typeDeclBody
        // ) { case (lhs, body) => Let(lhs, lhs, body) }
      )
  
  def ifLike(kw: `if`.type | `while`.type): Alt[Tree] =
    Kw(kw):
      ParseRule(s"'${kw.name}' keyword")(
        Expr(
          ParseRule(s"'${kw.name}' expression")(
            End(N),
            Kw(`else`):
              ParseRule(s"`else` keyword")(
                exprOrBlk(ParseRule(s"`else` expression")(End(()))):
                  case (body, _) => S(body)
                *
              )
          )
        ):
          case (split, S(default)) =>
            val clause = Modified(`else`, N/* TODO */, default)
            val items = split match
              case Block(stmts) => stmts.appended(clause)
              case _ => split :: clause :: Nil
            IfLike(kw, N/* TODO */, Block(items))
          case (split, N) => IfLike(kw, N/* TODO */, split)
        ,
        Blk(
          ParseRule(s"'${kw.name}' block")(End(()))
        ) { case (body, _) => IfLike(kw, N/* TODO */, body) }
      )
  
  def typeAliasLike(kw: Keyword, kind: TypeDefKind): Kw[TypeDef] =
    Kw(kw):
      ParseRule(s"${kind.desc} declaration"):
        Expr(
          ParseRule(s"${kind.desc} head")(
            Kw(`=`):
              ParseRule(s"${kind.desc} declaration equals sign"):
                Expr(
                  ParseRule(s"${kind.desc} declaration right-hand side")(
                    End(())
                  )
                ) { case (rhs, ()) => S(rhs) },
            End(N),
          )
        ) { (lhs, rhs) => TypeDef(kind, lhs, rhs, N) }
  
  val prefixRules: ParseRule[Tree] = ParseRule("start of statement", omitAltsStr = true)(
    letLike(`let`),
    letLike(`set`),
    
    Kw(`handle`):
      ParseRule("'handle' binding keyword"):
        Expr(
          ParseRule("'handle' binding head"):
            Kw(`=`):
              ParseRule("'handle' binding equals sign"):
                Expr(
                  ParseRule("'handle' binding class name"):
                    typeDeclTemplateThen(
                      Kw(`in`):
                        ParseRule(s"'handle' binding `in` clause")(
                          exprOrBlk(ParseRule(s"'handle' binding body")(End(())))((body, _: Unit) => S(body))*
                        ),
                      End(None)
                    )
                ) { case (rhs, (S(defs), body)) => (rhs, defs, body) }
        ) { case (lhs, (rhs, defs, body))=> Handle(lhs, rhs, defs, body) }
    ,
    Kw(`new`):
      ParseRule("`new` keyword")(
        exprOrBlk(ParseRule("`new` expression")(End(())))((body, _: Unit) => New(body))*
      )
    ,
    Kw(`in`):
      ParseRule("modifier keyword `in`"):
        Expr(
          ParseRule("`in` expression")(
            Kw(`out`)(ParseRule(s"modifier keyword `out`")(standaloneExpr)).map(s => S(Tree.Modified(`out`, N/* TODO */, s))),
            End(N),
          )
        ) {
          case (lhs, N) => Tree.Modified(`in`, N/* TODO */, lhs)
          case (lhs, S(rhs)) => Tup(Tree.Modified(`in`, N/* TODO */, lhs) :: rhs :: Nil)
        }
    ,
    ifLike(`if`),
    ifLike(`while`),
    Kw(`else`):
      ParseRule("`else` clause")(
        Expr(ParseRule("`else` expression")(End(()))):
          case (tree, _) => Modified(`else`, N/* TODO */, tree),
        Blk(ParseRule("`else` expression")(End(()))):
          case (tree, _) => Modified(`else`, N/* TODO */, tree),
      )
    ,
    Kw(`case`):
      ParseRule("`case` keyword")(
        exprOrBlk(ParseRule("`case` branches")(End(())))((body, _: Unit) => Case(N/* TODO */, body))*
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
    Kw(`val`)(termDefBody(ImmutVal)),
    typeAliasLike(`type`, Als),
    typeAliasLike(`pattern`, Pat),
    Kw(`class`)(typeDeclBody(Cls)),
    Kw(`trait`)(typeDeclBody(Trt)),
    Kw(`module`)(typeDeclBody(Mod)),
    Kw(`object`)(typeDeclBody(Obj)),
    Kw(`open`):
      ParseRule("'open' keyword")(
        exprOrBlk(ParseRule("'open' declaration")(End(()))){
          case (body, _) => Open(body)}*),
    modified(`abstract`, Kw(`class`)(typeDeclBody(Cls))),
    modified(`mut`),
    modified(`do`),
    modified(`virtual`),
    modified(`override`),
    modified(`declare`),
    modified(`public`),
    modified(`private`),
    modified(`out`),
    modified(`return`),
    modified(`throw`),
    modified(`import`), // TODO improve – only allow strings
    // modified(`type`),
    singleKw(`true`)(BoolLit(true)),
    singleKw(`false`)(BoolLit(false)),
    singleKw(`undefined`)(UnitLit(false)),
    singleKw(`null`)(UnitLit(true)),
    singleKw(`this`)(Ident("this")),
    singleKw(Keyword.__)(Under()),
    standaloneExpr,
  )
  
  def singleKw[T](kw: Keyword)(v: T): Alt[T] =
    Kw(kw)(ParseRule(s"'${kw.name}' keyword")(End(v)))
  
  
  val prefixRulesAllowIndentedBlock: ParseRule[Tree] =
    ParseRule(prefixRules.name, prefixRules.omitAltsStr)(prefixRules.alts :+ 
        (Blk(
          ParseRule("block"):
            End(())
        ) { case (res, ()) => res })*)
  
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
        // * Interestingly, this does not seem to change anything:
        // exprOrBlk(ParseRule(s"'${kw}' operator right-hand side")(End(())))(k)*
      )
  
  val infixRules: ParseRule[Tree => Tree] = ParseRule("continuation of statement")(
    genInfixRule(`and`, (rhs, _: Unit) => lhs => InfixApp(lhs, `and`, rhs)),
    genInfixRule(`or`, (rhs, _: Unit) => lhs => InfixApp(lhs, `or`, rhs)),
    genInfixRule(`is`, (rhs, _: Unit) => lhs => InfixApp(lhs, `is`, rhs)),
    genInfixRule(`as`, (rhs, _: Unit) => lhs => InfixApp(lhs, `as`, rhs)),
    genInfixRule(`then`, (rhs, _: Unit) => lhs => InfixApp(lhs, `then`, rhs)),
    // genInfixRule(`else`, (rhs, _: Unit) => lhs => InfixApp(lhs, `else`, rhs)),
    genInfixRule(`:`, (rhs, _: Unit) => lhs => InfixApp(lhs, `:`, rhs)),
    genInfixRule(`extends`, (rhs, _: Unit) => lhs => InfixApp(lhs, `extends`, rhs)),
    genInfixRule(`restricts`, (rhs, _: Unit) => lhs => InfixApp(lhs, `restricts`, rhs)),
    genInfixRule(`do`, (rhs, _: Unit) => lhs => InfixApp(lhs, `do`, rhs)),
  )

end ParseRules

