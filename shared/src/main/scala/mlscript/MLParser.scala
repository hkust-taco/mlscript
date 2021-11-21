package mlscript

import scala.util.chaining._
import scala.collection.mutable
import fastparse._, fastparse.ScalaWhitespace._
import mlscript.utils._, shorthands._

// TODO: empty lines

/** Parser for an ML-style input syntax, used in the legacy `ML*` tests. */
@SuppressWarnings(Array("org.wartremover.warts.All"))
class MLParser(origin: Origin, indent: Int = 0, recordLocations: Bool = true) {
  
  val keywords = Set(
    "def", "class", "trait", "type", "method",
    "let", "rec", "in", "fun", "with",
    "if", "then", "else", "match", "case", "of",
    "_")
  def kw[_: P](s: String) = s ~~ !(letter | digit | "_" | "'")
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[_:P, L <: Located](tree: => P[L], ignoreIfSet: Bool = false): P[L] = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => if (!ignoreIfSet || n.toLoc.isDefined) n.withLoc(i0, i1, origin) else n
  }
  
  def letter[_: P]     = P( lowercase | uppercase )
  def lowercase[_: P]  = P( CharIn("a-z") )
  def uppercase[_: P]  = P( CharIn("A-Z") )
  def digit[_: P]      = P( CharIn("0-9") )
  def number[_: P]: P[Int] = P( CharIn("0-9").repX(1).!.map(_.toInt) )
  def ident[_: P]: P[String] =
    P( (letter | "_") ~~ (letter | digit | "_" | "'").repX ).!.filter(!keywords(_))
  
  def termOrAssign[_: P]: P[Statement] = P( term ~ ("=" ~ term).? ).map {
    case (expr, N) => expr
    case (pat, S(bod)) => LetS(false, pat, bod)
  }
  def term[_: P]: P[Term] = P( let | fun | ite | withsAsc | _match )
  def lit[_: P]: P[Lit] =
    locate(number.map(x => IntLit(BigInt(x))) | Lexer.stringliteral.map(StrLit(_)))
  def variable[_: P]: P[Var] = locate(ident.map(Var))
  def parens[_: P]: P[Term] = P( "(" ~/ term ~ ")" )
  def subtermNoSel[_: P]: P[Term] = P( parens | record | lit | variable )
  def subterm[_: P]: P[Term] = P( subtermNoSel ~ ("." ~/ ( variable | locate(("(" ~/ ident ~ "." ~ ident ~ ")").map {
      case (prt, id) => Var(s"${prt}.${id}")
    }))).rep ).map {
      case (st, sels) => sels.foldLeft(st)(Sel)
    }
  def record[_: P]: P[Rcd] = locate(P(
      "{" ~/ (variable ~ "=" ~ term map L.apply).|(variable map R.apply).rep(sep = ";") ~ "}"
    ).map { fs =>
      Rcd(fs.map{ case L(nt) => nt; case R(id) => id -> id }.toList)
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
    case (as, ws) => ws.foldLeft(as)((acc, w) => With(acc, w))
  }
  def apps[_: P]: P[Term] = P( subterm.rep(1).map(_.reduce(App)) )
  def _match[_: P]: P[CaseOf] =
    P( kw("case") ~/ term ~ "of" ~ "{" ~ "|".? ~ matchArms ~ "}" ).map(CaseOf.tupled)
  def matchArms[_: P]: P[CaseBranches] = P(
    ((lit | variable) ~ "->" ~ term ~ matchArms2).map {
      case (t, b, rest) => Case(t, b, rest)
    } | locate((kw("_") ~ "->" ~ term).?.map {
      case None => NoCases
      case Some(b) => Wildcard(b)
    })
  )
  def matchArms2[_: P]: P[CaseBranches] = ("|" ~ matchArms).?.map(_.getOrElse(NoCases))
  
  def expr[_: P]: P[Term] = P( term ~ End )
  
  def defDecl[_: P]: P[Def] =
    P((kw("def") ~ ident ~ tyParams ~ ":" ~/ ty map {
      case (id, tps, t) => Def(true, id, R(PolyType(tps, t)))
    }) | (kw("rec").!.?.map(_.isDefined) ~ kw("def") ~/ ident ~ subterm.rep ~ "=" ~ term map {
      case (rec, id, ps, bod) => Def(rec, id, L(ps.foldRight(bod)((i, acc) => Lam(i, acc))))
    }))
  
  def tyKind[_: P]: P[TypeDefKind] = (kw("class") | kw("trait") | kw("type")).! map {
    case "class" => Cls
    case "trait" => Trt
    case "type"  => Als
  }
  def tyDecl[_: P]: P[TypeDef] =
    P((tyKind ~/ tyName ~ tyParams).flatMap {
      case (k @ (Cls | Trt), id, ts) => (":" ~ ty).? ~ (mthDecl(id) | mthDef(id)).rep.map(_.toList) map {
        case (bod, ms) => TypeDef(k, id, ts, bod.getOrElse(Top), 
          ms.collect { case R(md) => md }, ms.collect{ case L(md) => md })
      }
      case (k @ Als, id, ts) => "=" ~ ty map (bod => TypeDef(k, id, ts, bod))
    })
  def tyParams[_: P]: P[Ls[Primitive]] =
    ("[" ~ tyName.rep(0, ",") ~ "]").?.map(_.toList.flatten)
  def mthDecl[_: P](prt: Primitive): P[R[MethodDef[Right[Term, Type]]]] = 
    P(kw("method") ~ tyName ~ tyParams ~ ":" ~/ ty map {
      case (id, ts, t) => R(MethodDef[Right[Term, Type]](true, prt, id, ts, R(t)))
    })
  def mthDef[_: P](prt: Primitive): P[L[MethodDef[Left[Term, Type]]]] = 
    P(kw("rec").!.?.map(_.isDefined) ~ kw("method") ~ tyName ~ tyParams ~ subterm.rep ~ "=" ~/ term map {
      case (rec, id, ts, ps, bod) => L(MethodDef(rec, prt, id, ts, L(ps.foldRight(bod)((i, acc) => Lam(i, acc)))))
    })
  
  def ty[_: P]: P[Type] = P( tyNoUnion.rep(1, "|") ).map(_.reduce(Union))
  def tyNoUnion[_: P]: P[Type] = P( tyNoInter.rep(1, "&") ).map(_.reduce(Inter))
  def tyNoInter[_: P]: P[Type] = P( tyNoFun ~ ("->" ~/ tyNoInter).? ).map {
    case (l, S(r)) => Function(l, r)
    case (l, N) => l
  }
  // Note: field removal types are not supposed to be explicitly used by programmers,
  //    and they won't work in negative positions,
  //    but parsing them is useful in tests (such as shared/src/test/diff/mlscript/Annoying.mls)
  def tyNoFun[_: P]: P[Type] = P( (rcd | ctor | litTy | parTy) ~ ("\\" ~ variable).rep(0) ) map {
    case (ty, Nil) => ty
    case (ty, ids) => Rem(ty, ids.toList)
  }
  def ctor[_: P]: P[Type] = locate(P( tyName ~ "[" ~ ty.rep(0, ",") ~ "]" ) map {
    case (tname, targs) => AppliedType(tname, targs.toList)
  }) | tyNeg | tyName | tyVar //| const.map(Const) // TODO
  def tyNeg[_: P]: P[Type] = locate(P("~" ~/ tyNoFun map { t => Neg(t) }))
  def tyName[_: P]: P[Primitive] = locate(P(ident map Primitive))
  def tyVar[_: P]: P[TypeVar] = locate(P("'" ~ ident map (id => getVar(id))), ignoreIfSet = true)
  def rcd[_: P]: P[Record] =
    locate(P( "{" ~/ (variable ~ ":" ~ ty).rep(sep = ";") ~ "}" ).map(_.toList pipe Record))
  def parTy[_: P]: P[Type] = P( "(" ~/ ty ~ ")" )
  def litTy[_: P]: P[Type] = P( lit.map(Literal) )
  
  def toplvl[_: P]: P[Statement] =
    P( defDecl | tyDecl | termOrAssign )
  def pgrm[_: P]: P[Pgrm] = P( (";".rep ~ toplvl ~ topLevelSep.rep).rep.map(_.toList) ~ End ).map(Pgrm)
  def topLevelSep[_: P]: P[Unit] = ";"
  
  private var curHash = 0
  def nextHash: Int = {
    val res = curHash
    curHash = res + 1
    res
  }
  private val vars = mutable.Map.empty[Str, TypeVar]
  def getVar(nme: Str): TypeVar = vars.getOrElseUpdate(nme,
    new TypeVar(nme, nextHash))
  
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
