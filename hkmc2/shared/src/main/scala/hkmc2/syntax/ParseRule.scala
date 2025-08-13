package hkmc2
package syntax

import sourcecode.{Name, Line}

import mlscript.utils.*, shorthands.*
import hkmc2.Message._

import BracketKind._
import syntax.Tree.Keywrd
import semantics.Elaborator.State


// * TODO: add lookahead to Expr as a PartialFunction[Ls[Token], Bool]

enum Alt[+A]:
  case Kw[Rest, +Res](kw: Keyword)(val rest: ParseRule[Rest])(val k: (Keywrd[kw.type], Rest) => Res) extends Alt[Res]
  case Expr[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case Blk[Rest, +Res](rest: ParseRule[Rest])(val k: (Tree, Rest) => Res) extends Alt[Res]
  case End()(val a: () => A)
  
  def map[B](f: A => B): Alt[B] = 
    this match
    case k: Kw[rest, A] => Kw(k.kw)(k.rest)((kw, rest) => f(k.k(kw, rest)))
    case e: Expr[rest, A] => Expr(e.rest)((tree, rest) => f(e.k(tree, rest)))
    case e: End[?] => End()(() => f(e.a()))
    case b: Blk[rest, A] => Blk(b.rest)((tree, rest) => f(b.k(tree, rest)))

def end[A](a: => A): Alt[A] = Alt.End()(() => a)

def discard[A]: (A, Unit) => A = { case (a, _) => a }

def extendLoc[T <: Tree]: (Keywrd[?], T) => T = { case (k, a) => a.mkLocWith(k) }

def discardKw[Rest](kw: Keyword)(rest: ParseRule[Rest]): Alt[Rest] =
  Alt.Kw(kw)(rest)((_, rest) => rest)
def keepKw[Rest](kw: Keyword)(rest: ParseRule[Rest]): Alt[Keywrd[kw.type] -> Rest] = 
  Alt.Kw(kw)(rest)((k, rest) => k -> rest)

class ParseRule[+A](val name: Str, val omitAltsStr: Bool = false)(val alts: Alt[A]*):
  def map[B](f: A => B): ParseRule[B] =
    ParseRule(name)(alts.map(_.map(f))*)
  
  override def toString: Str = s"$name ::= " + alts.mkString(" | ")
  
  lazy val emptyAlt = alts.collectFirst { case e: Alt.End[?] => e.a }
  
  lazy val kwAlts = alts.collect { case alt: Alt.Kw[rst, A] => alt.kw.name -> alt }.toMap
  // * `kwAltsTODO` below is a temporary workaround; all uses should eventually be replaced by `kwAlts`
  lazy val kwAltsTODO = alts.collect { case alt: Alt.Kw[rst, A] => alt.kw.name ->
    alt.rest.map(rst => alt.k(Keywrd(alt.kw), rst)) }.toMap
  
  def getKwAlt(k: Keyword): Opt[Alt.Kw[?, A] & { val kw: k.type }] =
    kwAlts.get(k.name).asInstanceOf
  
  lazy val exprAlt = alts.collectFirst { case alt: Alt.Expr[rst, A] => alt }
  lazy val blkAlt = alts.collectFirst { case alt: Alt.Blk[rst, A] => alt }
  
  def mkAfterStr: Str = if omitAltsStr then "in this position" else s"after $name"
  
  def whatComesAfter: Str = if omitAltsStr then name else
    alts.map:
      case Alt.Kw(kw) => s"'${kw.name}' keyword"
      case Alt.Expr(rest) => "expression"
      case Alt.Blk(rest) => "block"
      case Alt.End() => "end of input"
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
    Expr(ParseRule("expression")(end(())))((l, _: Unit) => l)
  
  def prefixed(kw: Keyword.Prefix): Alt[Tree] = prefixed(kw, standaloneExpr)
  def prefixed(kw: Keyword.Prefix, body: Alt[Tree]) =
    Kw(kw)(ParseRule(s"prefix keyword '${kw.name}'")(body))((k, r) => Tree.PrefixApp(k, r))
  
  def modified(kw: Keyword): Alt[Tree] = modified(kw, standaloneExpr)
  def modified(kw: Keyword, body: Alt[Tree]) =
    Kw(kw)(ParseRule(s"modifier keyword '${kw.name}'")(body))((k, r) =>
        Tree.Modified(k.kw, N, r) // TODO
      )
  
  def exprOrBlk[Rest, Res](body: ParseRule[Rest])(k: (Tree, Rest) => Res): List[Alt[Res]] =
    Expr(body)(k) ::
    Blk(body)(k) ::
    Nil
  
  def standaloneExprOrBlk[Rest, Res]: List[Alt[Tree]] =
    standaloneExpr ::
    Blk(ParseRule("block")(end(())))((l, _: Unit) => l) ::
    Nil
  
  val typeDeclTemplate: Alt[Opt[Tree]] = end(N)
  
  /* // * What we had before we allowed parsing juxtapositions
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
            end(N),
          )
        ) {
          case (lhs, rhs) => TermDef(k, lhs, rhs)
        }
      )
  
  def typeDeclBody(k: TypeDefKind): ParseRule[TypeDef] =
    ParseRule("type declaration keyword"):
      Expr(
        ParseRule("type declaration head"):
          end(())
      ):
        case (head, ()) =>
          TypeDef(k, head, N)
  
  def letLike(kw: Keyword.letLike) = 
    discardKw(kw): // TODO keep kw
      ParseRule(s"'${kw.name}' binding keyword")(
        Expr(
          ParseRule(s"'${kw.name}' binding head")(
            discardKw(`=`):
              ParseRule(s"'${kw.name}' binding equals sign")(
                exprOrBlk(
                  ParseRule(s"'${kw.name}' binding right-hand side")(
                    discardKw(`in`):
                      ParseRule(s"'${kw.name}' binding `in` clause")(
                        exprOrBlk(
                          ParseRule(s"'${kw.name}' binding body"){end{()}}
                        ){ (body, _: Unit) => S(body) }*
                      ),
                    end(N)
                  )
                ) { (rhs, body) => (S(rhs), body) }*
              ),
            discardKw(`in`):
              ParseRule(s"'${kw.name}' binding `in` clause")(
                exprOrBlk(
                  ParseRule(s"'${kw.name}' binding body")(end(()))
                ){ (body, _: Unit) => N -> S(body) }*
              )
            ,
            end(N -> N)
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
    Kw(kw)(
      ParseRule(s"'${kw.name}' keyword")(
        Expr(
          ParseRule(s"'${kw.name}' expression")(
            end(N),
            Kw(`else`)(
              ParseRule(s"`else` keyword")(
                exprOrBlk(ParseRule(s"`else` expression")(end(()))):
                  discard
                *
              )
            ) {  case (elsKw, default) => S((elsKw, default)) }
          )
        ):
          case (split, S((elsKw, default))) =>
            val clause = PrefixApp(elsKw, default)
            val items = split match
              case Block(stmts) => stmts.appended(clause)
              case _ => split :: clause :: Nil
            Block(items)
          case (split, N) => split
        ,
        Blk(
          ParseRule(s"'${kw.name}' block")(end(()))
        )(discard)
      )
    ) { case (kw, body) => IfLike(kw.kw, N/* TODO */, body) }
  
  def typeAliasLike(kw: Keyword, kind: TypeDefKind): Alt[TypeDef] =
    discardKw(kw): // TODO keep kw
      ParseRule(s"${kind.desc} declaration"):
        Expr(
          ParseRule(s"${kind.desc} head")(
            discardKw(`=`):
              ParseRule(s"${kind.desc} declaration equals sign"):
                Expr(
                  ParseRule(s"${kind.desc} declaration right-hand side")(
                    end(())
                  )
                ) { case (rhs, ()) => S(rhs) },
            end(N),
          )
        ) { (lhs, rhs) => TypeDef(kind, lhs, rhs) }
  
  val prefixRules: ParseRule[Tree] = ParseRule("start of expression", omitAltsStr = true)(
    letLike(`let`),
    letLike(`set`),
    
    discardKw(`handle`): // TODO keep kw
      ParseRule("'handle' binding keyword"):
        Expr(
          ParseRule("'handle' binding head"):
            discardKw(`=`):
              ParseRule("'handle' binding equals sign"):
                Expr(
                  ParseRule("'handle' binding class name"):
                    discardKw(`with`):
                      ParseRule("type declaration body")(
                        Blk(
                          ParseRule("type declaration block")(
                            discardKw(`in`):
                              ParseRule(s"'handle' binding `in` clause")(
                                exprOrBlk(ParseRule(s"'handle' binding body")(end(())))((body, _: Unit) => S(body))*
                              ),
                            end(N))
                        ) { case (res, t) => (S(res), t) }
                      )
                ) { case (rhs, (S(defs), body)) => (rhs, defs, body) }
        ) { case (lhs, (rhs, defs, body)) => Hndl(lhs, rhs, defs, body) }
    ,
    discardKw(`new`): // TODO keep kw
      val withRefinement = discardKw(`with`)(
          ParseRule("'new' body")(
            Blk(ParseRule("'new' expression")(end(()))) { case (res: Block // FIXME: can it be something else?
              , ()) => S(res) }
          )
        )
      ParseRule("`new` keyword")(
        (
          withRefinement.map(rfto => LexicalNew(N, rfto)) ::
          exprOrBlk(ParseRule("`new` expression")(
            withRefinement,
            end(N),
          ))((body, rfto) => LexicalNew(S(body), rfto))
        )*
      )
    ,
    discardKw(`in`):
      ParseRule("modifier keyword `in`"):
        Expr(
          ParseRule("`in` expression")(
            discardKw(`out`)( // TODO keep kw
              ParseRule(s"modifier keyword `out`")(standaloneExpr)).map(s => S(Tree.Modified(`out`, N/* TODO */, s))),
            end(N),
          )
        ) {
          case (lhs, N) => Tree.Modified(`in`, N/* TODO */, lhs)
          case (lhs, S(rhs)) => Tup(Tree.Modified(`in`, N/* TODO */, lhs) :: rhs :: Nil)
        }
    ,
    ifLike(`if`),
    ifLike(`while`),
    Kw(`else`)(
      ParseRule("`else` clause")(
        Expr(ParseRule("`else` expression")(end(())))(discard),
        Blk(ParseRule("`else` expression")(end(())))(discard)
      )
    ) { case (kwrd, tree) => PrefixApp(kwrd, tree) },
    discardKw(`case`): // TODO keep kw
      ParseRule("`case` keyword")(
        exprOrBlk(ParseRule("`case` branches")(end(())))((body, _: Unit) => Case(N/* TODO */, body))*
      )
    ,
    discardKw(`region`): // TODO keep kw
      ParseRule("`region` keyword"):
        Expr(
          ParseRule("`region` declaration"):
            discardKw(`in`):
              ParseRule("`in` keyword")(
                Expr(ParseRule("'region' expression")(end(())))((body, _: Unit) => body),
                Blk(ParseRule("'region' block")(end(())))((body, _: Unit) => body)
              )
        ) { case (name, body) => Region(name, body) }
    ,
    discardKw(`outer`): // TODO keep kw
      ParseRule("outer binding operator")(
        Expr(
          ParseRule("`outer` binding name")(end(()))
        ){ (body, _: Unit) => Outer(S(body)) },
        end(Outer(N))
      ),
    discardKw(`constructor`): // TODO keep kw
      ParseRule("constructor keyword"):
        Blk(
          ParseRule(s"constructor block")(end(()))
        ) { case (body, _) => Tree.Constructor(body) },
    Kw(`fun`)(termDefBody(Fun))(extendLoc),
    Kw(`val`)(termDefBody(ImmutVal))(extendLoc),
    Kw(`using`)(termDefBody(Ins))(extendLoc),
    typeAliasLike(`type`, Als),
    typeAliasLike(`pattern`, Pat),
    Kw(`class`)(typeDeclBody(Cls))(extendLoc),
    Kw(`trait`)(typeDeclBody(Trt))(extendLoc),
    Kw(`module`)(typeDeclBody(Mod))(extendLoc),
    Kw(`object`)(typeDeclBody(Obj))(extendLoc),
    discardKw(`open`): // TODO keep kw
      ParseRule("'open' keyword")(
        exprOrBlk(ParseRule("'open' declaration")(end(()))){
          case (body, _) => Open(body)}*),
    modified(`abstract`, discardKw(`class`)(typeDeclBody(Cls))), // TODO keep kw
    discardKw(`mut`)(ParseRule(s"'mut' keyword")(standaloneExprOrBlk*)).map(Tree.Modified(`mut`, N, _)), // TODO keep kw
    Kw(`do`)(
      ParseRule(s"`do` keyword")(
        exprOrBlk(ParseRule(s"`do` body")(end(()))):
          discard
        *)
    ) { case (kw, body) => Tree.PrefixApp(kw, body) },
    prefixed(`not`),
    prefixed(`new!`),
    prefixed(`return`),
    prefixed(`throw`),
    prefixed(`import`), // TODO improve – only allow strings
    modified(`virtual`),
    modified(`override`),
    modified(`declare`),
    modified(`data`),
    modified(`public`),
    modified(`private`),
    modified(`out`),
    singleKw(`true`)(BoolLit(true)),
    singleKw(`false`)(BoolLit(false)),
    singleKw(`undefined`)(UnitLit(false)),
    singleKw(`null`)(UnitLit(true)),
    singleKw(`this`)(Ident("this")),
    singleKw(Keyword.__)(Under()),
    standaloneExpr,
  )
  
  def singleKw[T <: Tree](kw: Keyword)(v: => T): Alt[T] =
    Kw(kw)(ParseRule(s"'${kw.name}' keyword")(end(v)))((kwrd, v) => v.withLocOf(kwrd))
  
  
  val prefixRulesAllowIndentedBlock: ParseRule[Tree] =
    ParseRule(prefixRules.name, prefixRules.omitAltsStr)(prefixRules.alts :+ 
        (Blk(
          ParseRule("block"):
            end(())
        ) { case (res, ()) => res })*)
  
  /* 
  def funSign(k: TermDefKind): Alt[(S[Tree], Opt[Tree])] =
    Kw(`:`):
      ParseRule(s"'${k.str}' binding colon"):
        Expr(
          ParseRule(s"'${k.str}' binding signature")(
            funBody(k),
            end(N),
          )
        ) { case (sign, rhs) => (S(sign), rhs) }
  */
  
  def funBody(k: TermDefKind): Alt[S[Tree]] =
    discardKw(`=`):
      ParseRule(s"'${k.str}' binding equals sign")(
        Expr(
          ParseRule(s"'${k.str}' binding right-hand side")(end(()))
        ) { case (rhs, ()) => S(rhs) }
        ,
        Blk(
          ParseRule(s"'${k.str}' binding block")(end(()))
        ) { case (rhs, _) => S(rhs) }
      )
  
  def genInfixRule[A](kw: Keyword, k: (Tree, Unit) => A): Alt[A] =
    discardKw(kw):
      ParseRule(s"'${kw}' operator")(
        Expr(ParseRule(s"'${kw}' operator right-hand side")(end(())))(k)
        // * Interestingly, this does not seem to change anything:
        // exprOrBlk(ParseRule(s"'${kw}' operator right-hand side")(End(())))(k)*
      )
  
  val infixRules: ParseRule[Tree => Tree] = ParseRule("continuation of expression")(
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
    genInfixRule(`where`, (rhs, _: Unit) => lhs => InfixApp(lhs, `where`, rhs)),
    genInfixRule(`with`, (rhs, _: Unit) => lhs => InfixApp(lhs, `with`, rhs)),
  )

end ParseRules

