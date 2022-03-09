package mlscript

import scala.util.chaining._
import scala.collection.mutable
import fastparse._, fastparse.ScalaWhitespace._
import mlscript.utils._, shorthands._
import mlscript.Lexer._

/** Parser for an ML-style input syntax, used in the legacy `ML*` tests. */
@SuppressWarnings(Array("org.wartremover.warts.All"))
class MLParser(origin: Origin, indent: Int = 0, recordLocations: Bool = true) {
  
  val keywords = Set(
    "def", "class", "trait", "type", "method", "mut",
    "let", "rec", "in", "fun", "with",
    "if", "then", "else", "match", "case", "of")
  def kw[_: P](s: String) = s ~~ !(letter | digit | "_" | "'")
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[_:P, L <: Located](tree: => P[L]): P[L] = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => n.withLoc(i0, i1, origin)
  }
  
  def toParams(t: Term): Tup = t match {
    case t: Tup => t
    case _ => Tup((N, (t, false)) :: Nil)
  }
  def toParamsTy(t: Type): Tuple = t match {
    case t: Tuple => t
    case _ => Tuple((N, Field(None, t)) :: Nil)
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

  def term[_: P]: P[Term] = P(let | fun | ite | withsAsc | _match)

  def lit[_: P]: P[Lit] =
    locate(number.map(x => IntLit(BigInt(x))) | Lexer.stringliteral.map(StrLit(_)))
  def variable[_: P]: P[Var] = locate(ident.map(Var))

  def parens[_: P]: P[Term] = locate(P( "(" ~/ (kw("mut").!.? ~ term).rep(0, ",") ~ ",".!.? ~ ")" ).map {
    case (Seq(None -> t), N) => Bra(false, t)
    case (Seq(Some(_) -> t), N) => Tup(N -> (t, true) :: Nil)   // ? single tuple with mutable
    case (ts, _) => Tup(ts.iterator.map(f => N -> (f._2, f._1.isDefined)).toList)
  })

  def subtermNoSel[_: P]: P[Term] = P( parens | record | lit | variable )
  def subterm[_: P]: P[Term] = P( subtermNoSel ~ (
    // fields
    ("." ~/ (variable | locate(("(" ~/ ident ~ "." ~ ident ~ ")")
      .map {case (prt, id) => Var(s"${prt}.${id}")})))
      .map {(t: Var) => Left(t)} |
    // array subscript
    ("[" ~ term ~/ "]").map {Right(_)}
    // assign
    ).rep ~ ("<-" ~ term).?).map {
      case (st, sels, a) => sels.foldLeft(st)((acc, t) => t match {
        case Left(se) => Sel(acc, se)
        case Right(su) => Subs(acc, su)
      }) pipe (a match {
        case None => identity
        case Some(v) => Assign(_, v)
      })
    }

  def record[_: P]: P[Rcd] = locate(P(
      "{" ~/ (kw("mut").!.? ~ variable ~ "=" ~ term map L.apply).|(kw("mut").!.? ~ variable map R.apply).rep(sep = ";") ~ "}"
    ).map { fs => Rcd(fs.map{ 
        case L((mut, v, t)) => v -> (t -> mut.isDefined)
        case R(mut -> id) => id -> (id -> mut.isDefined) }.toList)})
  def fun[_: P]: P[Term] = locate(P( kw("fun") ~/ term ~ "->" ~ term ).map(nb => Lam(toParams(nb._1), nb._2)))
  def let[_: P]: P[Term] = locate(P(
      kw("let") ~/ kw("rec").!.?.map(_.isDefined) ~ variable ~ subterm.rep ~ "=" ~ term ~ kw("in") ~ term
    ) map {
      case (rec, id, ps, rhs, bod) => Let(rec, id, ps.foldRight(rhs)((i, acc) => Lam(toParams(i), acc)), bod)
    })
  def ite[_: P]: P[Term] = P( kw("if") ~/ term ~ kw("then") ~ term ~ kw("else") ~ term ).map(ite =>
    App(App(App(Var("if"), ite._1), ite._2), ite._3))
  def withsAsc[_: P]: P[Term] = P( withs ~ (":" ~/ ty).rep ).map {
    case (withs, ascs) => ascs.foldLeft(withs)(Asc)
  }
  def withs[_: P]: P[Term] = P( binops ~ (kw("with") ~ record).rep ).map {
    case (as, ws) => ws.foldLeft(as)((acc, w) => With(acc, w))
  }
  def mkApp(lhs: Term, rhs: Term): Term = App(lhs, toParams(rhs))
  def apps[_: P]: P[Term] = P( subterm.rep(1).map(_.reduce(mkApp)) )
  def _match[_: P]: P[CaseOf] =
    locate(P( kw("case") ~/ term ~ "of" ~ "{" ~ "|".? ~ matchArms ~ "}" ).map(CaseOf.tupled))
  def matchArms[_: P]: P[CaseBranches] = P(
    ( ("_" ~ "->" ~ term).map(Wildcard)
    | ((lit | variable) ~ "->" ~ term ~ matchArms2)
      .map { case (t, b, rest) => Case(t, b, rest) }
    ).?.map {
      case None => NoCases
      case Some(b) => b
    }
  )
  def matchArms2[_: P]: P[CaseBranches] = ("|" ~ matchArms).?.map(_.getOrElse(NoCases))
  
  private val prec: Map[Char,Int] = List(
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
  
  // Adapted from: https://github.com/databricks/sjsonnet/blob/master/sjsonnet/src/sjsonnet/Parser.scala#L136-L180
  def binops[_: P]: P[Term] =
    P(apps ~ (Index ~~ operator.! ~~ Index ~/ apps).rep ~ "").map { case (pre, fs) =>
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
                result = App(App(Var(op).withLoc(off0, off1, origin), toParams(result)), toParams(rhs))
                true
              }
          }
        )()
        result
      }
      climb(0, pre)
    }
  def operator[_: P]: P[Unit] = P(
    !symbolicKeywords ~~ (!StringIn("/*", "//") ~~ (CharsWhile(OpCharNotSlash) | "/")).rep(1)
  ).opaque("operator")
  def symbolicKeywords[_: P] = P{
    StringIn(
      "|",
      "~",
      ";", "=>", "=", "->", "<-",
      ":",
      "#", "@", "\\", "\u21d2", "\u2190"
    ) ~~ !OpChar
  }.opaque("symbolic keywords")
  
  def expr[_: P]: P[Term] = P( term ~ End )
  
  def defDecl[_: P]: P[Def] =
    locate(P((kw("def") ~ variable ~ tyParams ~ ":" ~/ ty map {
      case (id, tps, t) => Def(true, id, R(PolyType(tps, t)))
    }) | (kw("rec").!.?.map(_.isDefined) ~ kw("def") ~/ variable ~ subterm.rep ~ "=" ~ term map {
      case (rec, id, ps, bod) => Def(rec, id, L(ps.foldRight(bod)((i, acc) => Lam(toParams(i), acc))))
    })))
  
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
  def tyParams[_: P]: P[Ls[TypeName]] =
    ("[" ~ tyName.rep(0, ",") ~ "]").?.map(_.toList.flatten)
  def mthDecl[_: P](prt: TypeName): P[R[MethodDef[Right[Term, Type]]]] = 
    P(kw("method") ~ variable ~ tyParams ~ ":" ~/ ty map {
      case (id, ts, t) => R(MethodDef[Right[Term, Type]](true, prt, id, ts, R(t)))
    })
  def mthDef[_: P](prt: TypeName): P[L[MethodDef[Left[Term, Type]]]] = 
    P(kw("rec").!.?.map(_.isDefined) ~ kw("method") ~ variable ~ tyParams ~ subterm.rep ~ "=" ~/ term map {
      case (rec, id, ts, ps, bod) =>
        L(MethodDef(rec, prt, id, ts, L(ps.foldRight(bod)((i, acc) => Lam(toParams(i), acc)))))
    })
  
  def ty[_: P]: P[Type] = P( tyNoAs ~ ("as" ~ tyVar).rep ).map {
    case (ty, ass) => ass.foldLeft(ty)((a, b) => Recursive(b, a))
  }
  def tyNoAs[_: P]: P[Type] = P( tyNoUnion.rep(1, "|") ).map(_.reduce(Union))
  def tyNoUnion[_: P]: P[Type] = P( tyNoInter.rep(1, "&") ).map(_.reduce(Inter))
  def tyNoInter[_: P]: P[Type] = P( tyNoFun ~ ("->" ~/ tyNoInter).? ).map {
    case (l, S(r)) => Function(toParamsTy(l), r)
    case (l, N) => l
  }
  // Note: field removal types are not supposed to be explicitly used by programmers,
  //    and they won't work in negative positions,
  //    but parsing them is useful in tests (such as shared/src/test/diff/mlscript/Annoying.mls)
  def tyNoFun[_: P]: P[Type] = P( (rcd | ctor | parTy) ~ ("\\" ~ variable).rep(0) ) map {
    case (ty, Nil) => ty
    case (ty, ids) => Rem(ty, ids.toList)
  }
  def ctor[_: P]: P[Type] = locate(P( tyName ~ "[" ~ ty.rep(0, ",") ~ "]" ) map {
    case (tname, targs) => AppliedType(tname, targs.toList)
  }) | tyNeg | tyName | tyVar | tyWild | litTy
  def tyNeg[_: P]: P[Type] = locate(P("~" ~/ tyNoFun map { t => Neg(t) }))
  def tyName[_: P]: P[TypeName] = locate(P(ident map TypeName))
  def tyVar[_: P]: P[TypeVar] = locate(P("'" ~ ident map (id => TypeVar(R("'" + id), N))))
  def tyWild[_: P]: P[Bounds] = locate(P("?".! map (_ => Bounds(Bot, Top))))
  def rcd[_: P]: P[Record] =
    locate(P( "{" ~/ ( kw("mut").!.? ~ variable ~ ":" ~ ty).rep(sep = ";") ~ "}" )
      .map(_.toList.map {
        case (None, v, t) => v -> Field(None, t)
        case (Some(_), v, t) => v -> Field(Some(t), t)
      } pipe Record))
  def parTy[_: P]: P[Type] = locate(P( "(" ~/ (kw("mut").!.? ~ ty).rep(0, ",").map(_.map(N -> _).toList) ~ ",".!.? ~ ")" ).map {
    case (N -> (N -> ty) :: Nil, N) => ty
    case (fs, _) => Tuple(fs.map {
        case (l, N -> t) => l -> Field(None, t)
        case (l, S(_) -> t) => l -> Field(Some(t), t)
      })
  })
  def litTy[_: P]: P[Type] = P( lit.map(l => Literal(l).withLocOf(l)) )
  
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
