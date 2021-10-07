package mlscript

import scala.util.chaining._
import fastparse._, fastparse.ScalaWhitespace._
import mlscript.utils._, shorthands._

/** Parser for an ML-style input syntax, used in the legacy `ML*` tests. */
@SuppressWarnings(Array("org.wartremover.warts.All"))
class MLParser(origin: Origin, indent: Int = 0, recordLocations: Bool = true) {
  
  val keywords = Set(
    "def", "class", "trait", "type",
    "let", "rec", "in", "fun", "with",
    "if", "then", "else", "match", "case", "of",
    "_")
  def kw[_: P](s: String) = s ~~ !(letter | digit | "_" | "'")
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[_:P, L <: Located](tree: => P[L]) = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => n.withLoc(i0, i1, origin)
  }
  
  def letter[_: P]     = P( lowercase | uppercase )
  def lowercase[_: P]  = P( CharIn("a-z") )
  def uppercase[_: P]  = P( CharIn("A-Z") )
  def digit[_: P]      = P( CharIn("0-9") )
  def number[_: P]: P[Int] = P( CharIn("0-9").repX(1).!.map(_.toInt) )
  def ident[_: P]: P[String] =
    P( (letter | "_") ~~ (letter | digit | "_" | "'").repX ).!.filter(!keywords(_))
  
  def term[_: P]: P[Term] = P( let | fun | ite | withsAsc | _match )
  def const[_: P]: P[Term] =
    locate(number.map(x => IntLit(BigInt(x))) | Lexer.stringliteral.map(StrLit(_)))
  def variable[_: P]: P[Term] = locate(ident.map(Var))
  def parens[_: P]: P[Term] = P( "(" ~/ term ~ ")" )
  def subtermNoSel[_: P]: P[Term] = P( parens | record | const | variable )
  def subterm[_: P]: P[Term] = P( subtermNoSel ~ ("." ~/ ident).rep ).map {
    case (st, sels) => sels.foldLeft(st)(Sel) }
  def record[_: P]: P[Rcd] = locate(P(
      "{" ~/ (ident ~ "=" ~ term map L.apply).|(ident map R.apply).rep(sep = ";") ~ "}"
    ).map { fs =>
      Rcd(fs.map{ case L(nt) => nt; case R(id) => id -> Var(id) }.toList)
    })
  def fun[_: P]: P[Term] = P( kw("fun") ~/ term ~ "->" ~ term ).map(nb => Lam(nb._1, nb._2))
  def let[_: P]: P[Term] = locate(P(
      kw("let") ~/ kw("rec").!.?.map(_.isDefined) ~ ident ~ term.rep ~ "=" ~ term ~ kw("in") ~ term
    ) map {
      case (rec, id, ps, rhs, bod) => Let(rec, id, ps.foldRight(rhs)((i, acc) => Lam(i, acc)), bod)
    })
  def ite[_: P]: P[Term] = P( kw("if") ~/ term ~ kw("then") ~ term ~ kw("else") ~ term ).map(ite =>
    App(App(App(Var("if"), ite._1), ite._2), ite._3))
  def withsAsc[_: P]: P[Term] = P( withs ~ (":" ~ ty).rep ).map {
    // case (as, N) => as
    case (withs, ascs) => ascs.foldLeft(withs)(Asc)
  }
  def withs[_: P]: P[Term] = P( apps ~ (kw("with") ~ record).rep ).map {
    case (as, ws) => ws.foldLeft(as)((acc, w) => w.fields.foldLeft(acc)((acc1, fv) => With(acc1, fv._1, fv._2)))
  }
  def apps[_: P]: P[Term] = P( subterm.rep(1).map(_.reduce(App)) )
  def _match[_: P]: P[CaseOf] =
    P( kw("case") ~/ term ~ "of" ~ "{" ~ "|".? ~ matchArms ~ "}" ).map(CaseOf.tupled)
  def matchArms[_: P]: P[CaseBranches] = P(
    (tyName ~ "->" ~ term ~ matchArms2).map {
      case (t, b, rest) => Case(t, b, rest)
    } | (kw("_") ~ "->" ~ term).?.map {
      case None => NoCases
      case Some(b) => Wildcard(b)
    }
  )
  def matchArms2[_: P]: P[CaseBranches] = ("|" ~ matchArms).?.map(_.getOrElse(NoCases))
  
  def expr[_: P]: P[Term] = P( term ~ End )
  
  def defDecl[_: P]: P[Def] =
    P(kw("def") ~/ kw("rec").!.?.map(_.isDefined) ~ ident ~ term.rep ~ "=" ~ term map {
      case (rec, id, ps, bod) => Def(rec, id, ps.foldRight(bod)((i, acc) => Lam(i, acc)))
    })
  
  def tyKind[_: P]: P[TypeDefKind] = (kw("class") | kw("trait") | kw("type")).! map {
    case "class" => Cls
    case "trait" => Trt
    case "type"  => Als
  }
  def tyDecl[_: P]: P[TypeDef] =
    P((tyKind ~/ tyName ~ tyParams).flatMap {
      case (k @ (Cls | Trt), id, ts) => ":" ~ ty map (bod => TypeDef(k, id, ts, bod))
      case (k @ Als, id, ts) => "=" ~ ty map (bod => TypeDef(k, id, ts, bod))
    })
  def tyParams[_: P]: P[Ls[Str]] =
    ("[" ~ tyName.rep(0, ",") ~ "]").?.map(_.toList.flatMap(_.map(_.name)))
  
  def ty[_: P]: P[Type] = P( tyNoUnion.rep(1, "|") ).map(_.reduce(Union))
  def tyNoUnion[_: P]: P[Type] = P( tyNoInter.rep(1, "&") ).map(_.reduce(Inter))
  def tyNoInter[_: P]: P[Type] = P( tyNoFun ~ ("->" ~ tyNoFun).rep ).map {
    case (t, ts) => ts.reverseIterator.foldLeft(t)(Function) }
  def tyNoFun[_: P]: P[Type] = P( rcd | ctor | parTy )
  def ctor[_: P]: P[Type] = locate(P( tyName ~ "[" ~ ty.rep(0, ",") ~ "]" ) map {
    case (tname, targs) => AppliedType(tname, targs.toList)
  }) | tyName //| const.map(Const) // TODO
  def tyName[_: P]: P[Primitive] = locate(P(ident map Primitive))
  def rcd[_: P]: P[Record] =
    locate(P( "{" ~/ (ident ~ ":" ~ ty).rep(sep = ";") ~ "}" ).map(_.toList pipe Record))
  def parTy[_: P]: P[Type] = P( "(" ~/ ty ~ ")" )
  
  def toplvl[_: P]: P[TopLevel] =
    P( defDecl | tyDecl | term )
  def pgrm[_: P]: P[Pgrm] = P( ("" ~ toplvl ~ topLevelSep.rep).rep.map(_.toList) ~ End ).map(Pgrm)
  def topLevelSep[_: P]: P[Unit] = ";"
  
}
object MLParser {
  
  def addTopLevelSeparators(lines: IndexedSeq[Str]): IndexedSeq[Str] = {
    (lines.iterator ++ lines.lastOption).toList.sliding(2).map {
      case l0 :: l1 :: Nil =>
        if (l1.startsWith(" ") || l1.startsWith("\t")) l0 + "\n"
        else l0 + ";"
      case l :: Nil => l
      case _ => die
    }.toIndexedSeq
  }
  
}
