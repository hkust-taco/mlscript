package mlscript

import scala.util.chaining._
import scala.annotation.tailrec
import sourcecode.{Name, Line}

import utils._, shorthands._
import mlscript.Message._
import BracketKind._

object NewParser {
  
  type ExpectThen >: Bool
  type FoundErr >: Bool  // may be better done as:  class FoundErr(var found: Bool)
  
  def expectThen(implicit ptr: ExpectThen): Bool = ptr === true
  def foundErr(implicit ptr: FoundErr): Bool = ptr === true
  
}
import NewParser._

abstract class NewParser(origin: Origin, tokens: Ls[Stroken -> Loc], raiseFun: Diagnostic => Unit, val dbg: Bool, fallbackLoc: Opt[Loc], description: Str = "input") {
  outer =>
  
  def rec(tokens: Ls[Stroken -> Loc], fallbackLoc: Opt[Loc], description: Str): NewParser =
    new NewParser(origin, tokens, raiseFun, dbg, fallbackLoc, description) {
      def doPrintDbg(msg: => Str): Unit = outer.printDbg("> " + msg)
    }
  
  def raise(mkDiag: => Diagnostic)(implicit fe: FoundErr = false): Unit =
    if (!foundErr) raiseFun(mkDiag)
  
  def err(msgs: Ls[Message -> Opt[Loc]]): Unit =
    raise(ErrorReport(msgs, source = Diagnostic.Parsing))
  
  def mkLoc(l: Int, r: Int): Loc =
    Loc(l, r, origin)

  protected def doPrintDbg(msg: => Str): Unit
  protected def printDbg(msg: => Any): Unit =
    doPrintDbg("│ " * this.indent + msg)
  protected var indent = 0
  private def wrap[R](args: Any)(mkRes: Unit => R)(implicit l: Line, n: Name): R = {
    printDbg(s"@ ${n.value}${args match {
      case it: Iterable[_] => it.mkString("(", ",", ")")
      case _: Product => args
      case _ => s"($args)"
    }}    [at l.${l.value}]")
    val res = try {
      indent += 1
      // mkRes
      mkRes(())
    } finally indent -= 1
    printDbg(s"= $res")
    res
  }
  
  def parseAll[R](parser: => R): R = {
    val res = parser
    cur match {
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        err(msg"Expected end of input; found ${relevantToken.describe} instead" -> S(rl) :: Nil)
      case Nil => ()
    }
    res
  }
  
  def concludeWith[R](f: this.type => R): R = {
    val res = f(this)
    cur.dropWhile(tk => (tk._1 === SPACE || tk._1 === NEWLINE) && { consume; true }) match {
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        err(msg"Unexpected ${relevantToken.describe} here" -> S(rl) :: Nil)
      case Nil => ()
    }
    printDbg(s"Concluded with $res")
    res
  }
  def nil: Unit = ()
  
  type TokLoc = (Stroken, Loc)
  
  type LTL = Ls[TokLoc]
  
  private val MinPrec = 0
  private val NoElsePrec = MinPrec + 1
  
  private val prec: Map[Char,Int] =
    List(
      "", // 0 is the virtual precedence of 'else'
      "",
      "",
      "",
      "",
      // ^ for keywords
      ",",
      ";",
      "=",
      "@",
      ":",
      "|",
      "/ \\",
      "^",
      "&",
      // "= !",
      "!",
      "< >",
      "+ -",
      // "* / %",
      "* %",
      ".",
    ).zipWithIndex.flatMap {
      case (cs, i) => cs.filterNot(_ === ' ').map(_ -> (i + 1))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  def opCharPrec(opChar: Char): Int = prec(opChar)
  def opPrec(opStr: Str): (Int, Int) = opStr match {
    case "and" => (3, 3)
    case "or" => (2, 2)
    case _ if opStr.exists(_.isLetter) =>
      (4, 4)
    case _ =>
      val r = opStr.last
      (prec(opStr.head), prec(r) - (if (r === '@' || r === '/' || r === ',') 1 else 0))
  }
  
  // def pe(msg: Message, l: Loc, rest: (Message, Opt[Loc])*): Unit =
  //   err((msg -> S(l) :: rest.toList)) // TODO parse err
  
  
  
  private var _cur: Ls[TokLoc] = tokens
  
  private def summarizeCur =
    NewLexer.printTokens(_cur.take(5)) + (if (_cur.size > 5) "..." else "")
  
  private def cur(implicit l: Line, n: Name) = {
    if (dbg) printDbg(s"? ${n.value}\t\tinspects ${summarizeCur}    [at l.${l.value}]")
    _cur
  }
  
  def consume(implicit l: Line, n: Name): Unit = {
    if (dbg) printDbg(s"! ${n.value}\t\tconsumes ${NewLexer.printTokens(_cur.take(1))}    [at l.${l.value}]")
    _cur = _cur.tailOption.getOrElse(Nil) // FIXME throw error if empty?
  }
  
  // TODO simplify logic – this is no longer used much
  def skip(tk: Stroken, ignored: Set[Stroken] = Set(SPACE), allowEnd: Bool = false, note: => Ls[Message -> Opt[Loc]] = Nil)
        (implicit fe: FoundErr): (Bool, Opt[Loc]) = wrap(tk, ignored, allowEnd) { l =>
    require(!ignored(tk))
    val skip_res = cur match {
      case (tk2, l2) :: _ =>
        if (ignored(tk2)) {
          consume
          return skip(tk, ignored, allowEnd, note)
        } else if (tk2 =/= tk) {
          if (!foundErr) err((
            msg"Expected ${tk.describe}; found ${tk2.describe} instead" -> S(l2) :: note))
          (false, S(l2))
        } else (true, S(l2))
      case Nil =>
        if (!allowEnd)
          if (!foundErr) err((
            msg"Expected ${tk.describe}; found end of input instead" -> lastLoc :: note))
        (allowEnd, N)
    }
    consume
    skip_res
  }
  
  private lazy val lastLoc =
    tokens.lastOption.map(_._2.right).orElse(fallbackLoc)
  
  private def curLoc = _cur.headOption.map(_._2)
  
  /* // * TODO rm
  def blockTerm: Blk = {
    val ts = block(false, false)
    val es = ts.map {
      case L(t) =>
        err(msg"Unexpected 'then'/'else' clause" -> t.toLoc :: Nil)
        errExpr
      case R(e) => e
    }
    Blk(es)
  }
  */
  
  def typingUnit: TypingUnit = {
    val ts = block(false, false)
    val es = ts.map {
      case L(t) =>
        err(msg"Unexpected 'then'/'else' clause" -> t.toLoc :: Nil)
        errExpr
      case R(d: NuDecl) => d
      case R(e: Term) => e
      case _ => ???
    }
    TypingUnit(es)
  }
  def typingUnitMaybeIndented(implicit fe: FoundErr): TypingUnit = yeetSpaces match {
    case (br @ BRACKETS(Indent, toks), _) :: _ =>
      consume
      rec(toks, S(br.innerLoc), br.describe).concludeWith(_.typingUnit)
    case _ => typingUnit
  }
  def curlyTypingUnit(implicit fe: FoundErr): TypingUnit = yeetSpaces match {
    case (br @ BRACKETS(Curly, toks), l1) :: _ =>
      consume
      rec(toks, S(br.innerLoc), br.describe).concludeWith(_.typingUnitMaybeIndented).withLoc(S(l1))
    case _ =>
      TypingUnit(Nil)
  }
  
  def toParams(t: Term): Tup = t match {
    case t: Tup => t
    case Bra(false, t: Tup) => t
    case _ => Tup((N, Fld(false, false, t)) :: Nil)
  }
  def toParamsTy(t: Type): Tuple = t match {
    case t: Tuple => t
    case _ => Tuple((N, Field(None, t)) :: Nil)
  }
  def typ(implicit fe: FoundErr, l: Line): Type =
    expr(0).toType match {
      case L(d) => raise(d); Top // TODO better
      case R(ty) => ty
    }
  
  def block(implicit et: ExpectThen, fe: FoundErr): Ls[IfBody \/ Statement] =
    cur match {
      case Nil => Nil
      case (NEWLINE, _) :: _ => consume; block
      case (SPACE, _) :: _ => consume; block
      case c =>
        val t = c match {
          case (KEYWORD(k @ ("class" | "trait" | "type")), l0) :: c =>
            consume
            val kind = k match {
              case "class" => Cls
              case "trait" => Trt
              case "type" => Als
              case _ => die
            }
            val (tn, success) = yeetSpaces match {
              case (IDENT(idStr, false), l1) :: _ =>
                consume
                (TypeName(idStr).withLoc(S(l1)), true)
              case c =>
                val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                err((
                  msg"Expected a type name; found ${tkstr} instead" -> loc :: Nil))
                consume
                // R(errExpr)
                (TypeName("<error>").withLoc(curLoc.map(_.left)), false)
            }
            val tparams = yeetSpaces match {
              case (br @ BRACKETS(Angle, toks), loc) :: _ =>
                consume
                val ts = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()).map {
                  case (N, Fld(false, false, v @ Var(nme))) =>
                    TypeName(nme).withLocOf(v)
                  case _ => ???
                }
                ts
              case _ => Nil
            }
            val params = yeetSpaces match {
              case (br @ BRACKETS(Round, toks), loc) :: _ =>
                consume
                val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()) // TODO
                Tup(as).withLoc(S(loc))
              case _ => Tup(Nil)
            }
            def parents(Sep: Stroken): Ls[Term] = yeetSpaces match {
              case (Sep, _) :: _ =>
                consume
                expr(0) :: parents(COMMA)
              case _ => Nil
            }
            val ps = parents(KEYWORD(":"))
            val body = curlyTypingUnit
            R(NuTypeDef(kind, tn, tparams, params, ps, body))
          
          // TODO make `fun` by-name and `let` by-value
          case (KEYWORD(kwStr @ ("fun" | "let")), l0) :: c => // TODO support rec?
            consume
            val isLetRec = yeetSpaces match {
              case (KEYWORD("rec"), l1) :: _ if kwStr === "let" =>
                consume
                S(true)
              case c => if (kwStr === "fun") N else S(false)
            }
            val (v, success) = yeetSpaces match {
              case (IDENT(idStr, false), l1) :: _ =>
                consume
                (Var(idStr).withLoc(S(l1)), true)
              case c =>
                val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                err((
                  // msg"Expected a function name; found ${"[TODO]"} instead" -> N :: Nil))
                  msg"Expected a function name; found ${tkstr} instead" -> loc :: Nil))
                consume
                // R(errExpr)
                (Var("<error>").withLoc(curLoc.map(_.left)), false)
            }
            foundErr || !success pipe { implicit fe =>
              val ps = funParams
              val asc = yeetSpaces match {
                case (KEYWORD(":"), _) :: _ =>
                  consume
                  S(typ)
                case _ => N
              }
              yeetSpaces match {
                case (KEYWORD("="), _) :: _ =>
                  consume
                  val body = expr(0)
                  val annotatedBody = asc.fold(body)(ty => Asc(body, ty))
                  R(NuFunDef(isLetRec, v, Nil, L(ps.foldRight(annotatedBody)((i, acc) => Lam(i, acc)))))
                case c =>
                  asc match {
                    case S(ty) =>
                      R(NuFunDef(isLetRec, v, Nil, R(PolyType(Nil, ps.foldRight(ty)((p, r) => Function(p.toType match {
                        case L(diag) => raise(diag); Top // TODO better
                        case R(tp) => tp
                      }, r)))))) // TODO rm PolyType after FCP is merged
                    case N =>
                      // TODO dedup:
                      val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                      err((
                        msg"Expected ':' or '=' followed by a function body or signature; found ${tkstr} instead" -> loc :: Nil))
                      consume
                      R(NuFunDef(isLetRec, v, Nil, L(ps.foldRight(errExpr: Term)((i, acc) => Lam(i, acc)))))
                  }
              }
            }
          case _ =>
            exprOrIf(0, allowSpace = false)
        }
        cur match {
          case (NEWLINE, _) :: _ => consume; t :: block
          case _ => t :: Nil
        }
    }
  
  private def yeetSpaces: Ls[TokLoc] =
    cur.dropWhile(_._1 === SPACE && { consume; true })
  
  def funParams(implicit et: ExpectThen, fe: FoundErr, l: Line): Ls[Tup] = wrap(()) { l =>
    yeetSpaces match {
      case (KEYWORD("=" | ":"), _) :: _ => Nil
      case Nil => Nil
      case (KEYWORD("of"), _) :: _ =>
        consume
        Tup(args(false) // TODO
          ) :: funParams
      case (br @ BRACKETS(Round, toks), loc) :: _ =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()) // TODO
        Tup(as).withLoc(S(loc)) :: funParams
      case (tk, l0) :: _ =>
        err((
          // msg"Expected a function name; found ${"[TODO]"} instead" -> N :: Nil))
          msg"Expected function parameter list; found ${tk.describe} instead" -> S(l0) :: Nil))
        consume
        Nil
    }
  }
  
  def expr(prec: Int, allowSpace: Bool = true)(implicit fe: FoundErr, l: Line): Term = wrap(prec,allowSpace) { l =>
    exprOrIf(prec, allowSpace)(et = false, fe = fe, l = implicitly) match {
      case R(e) => e
      case L(e) =>
        err(msg"Expected an expression; found a 'then'/'else' clause instead" -> e.toLoc :: Nil)
        errExpr
    }
  }
  
  private def warnDbg(msg: Any, loco: Opt[Loc] = curLoc): Unit =
    raise(WarningReport(msg"[${cur.headOption.map(_._1).mkString}] ${""+msg}" -> loco :: Nil))
  
  def exprOrIf(prec: Int, allowSpace: Bool = true)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(prec, allowSpace) { l =>
    cur match {
      case (SPACE, l0) :: _ if allowSpace => // Q: do we really need the `allowSpace` flag?
        consume
        exprOrIf(prec, allowSpace)
      case (br @ BRACKETS(Indent, toks), _) :: _ if (toks.headOption match { // TODO factor
        case S((KEYWORD("then" | "else"), _)) => false
        case _ => true
      }) =>
        consume
        val ts = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.block)
        val es = ts.map { case L(t) => return L(IfBlock(ts)); case R(e) => e }
        R(Blk(es))
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec, allowNewlines = false)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme).withLoc(S(l0)), prec, allowNewlines = false)
      case (br @ BRACKETS(bk @ (Round | Square | Curly), toks), loc) :: _ =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()) // TODO
        val bra = if (bk === Curly) Bra(true, Rcd(res.map {
          case S(n) -> fld => n -> fld
          case N -> (fld @ Fld(_, _, v: Var)) => v -> fld
          case N -> fld =>
            err((
              msg"Record field should have a name" -> fld.value.toLoc :: Nil))
            Var("<error>") -> fld
        }))
        else Bra(false, Tup(res))
        exprCont(bra.withLoc(S(loc)), prec, allowNewlines = false)
      case (KEYWORD("let"), l0) :: _ =>
        consume
        val bs = bindings(Nil)
        val body = yeetSpaces match {
          case (KEYWORD("in") | KEYWORD(";"), _) :: _ =>
            consume
            exprOrIf(0)
          case (NEWLINE, _) :: _ =>
            consume
            exprOrIf(0)
          case _ =>
            R(UnitLit(true))
        }
        bs.foldRight(body) {
          case ((v, r), R(acc)) => R(Let(false, v, r, acc))
          case ((v, r), L(acc)) => L(IfLet(false, v, r, acc))
        }
      case (KEYWORD("new"), l0) :: c =>
        consume
        val body = expr(0)
        val head = body match {
          case Var(clsNme) =>
            S(TypeName(clsNme).withLocOf(body) -> Tup(Nil))
          case App(Var(clsNme), Tup(N -> Fld(false, false, UnitLit(true)) :: Nil)) =>
            S(TypeName(clsNme).withLocOf(body) -> Tup(Nil))
          case App(Var(clsNme), arg) =>
            S(TypeName(clsNme).withLocOf(body) -> arg)
          case UnitLit(true) =>
            N
          case _ =>
            err((
              msg"Unexpected ${body.describe} after `new` keyword" -> body.toLoc :: Nil))
            N
        }
        R(New(head, curlyTypingUnit).withLoc(S(head.foldLeft(l0)((l, h) => l ++ h._1.toLoc ++ h._2.toLoc))))
      case (KEYWORD("else"), l0) :: _ =>
        consume
        val e = expr(0)
        L(IfElse(e).withLoc(S(l0 ++ e.toLoc)))
      case (KEYWORD("if"), l0) :: _ =>
        consume
        cur match {
          case _ =>
            exprOrIf(0)(et = true, fe = fe, l = implicitly) match {
            case L(body) =>
              val els = yeetSpaces match {
                case (KEYWORD("else"), _) :: _ =>
                  consume
                  S(expr(0))
                case (NEWLINE, _) :: (KEYWORD("else"), _) :: _ =>
                  consume
                  consume
                  S(expr(0))
                case (br @ BRACKETS(Indent, (KEYWORD("else"), _) :: toks), _) :: _ =>
                  consume
                  val nested = rec(toks, S(br.innerLoc), br.describe)
                  S(nested.concludeWith(_.expr(0)))
                case _ => N
              }
              R(If(body, els))
            case R(e) =>
              yeetSpaces match {
                case (br @ BRACKETS(Indent, (KEYWORD("then"), _) :: toks), _) :: _ =>
                  consume
                  val nested = rec(toks, S(br.innerLoc), br.describe)
                  val thn = nested.expr(0)
                  val els = nested.yeetSpaces match {
                    case (KEYWORD("else"), _) :: _ =>
                      nested.consume
                      S(nested.concludeWith(_.expr(0)))
                    case (NEWLINE, _) :: (KEYWORD("else"), _) :: _ =>
                      nested.consume
                      nested.consume
                      // S(thn, S(nested.concludeWith(_.expr(0))))
                      S(nested.concludeWith(_.expr(0)))
                    case _ =>
                      nested.concludeWith(_.nil)
                      // S(thn, N)
                      N
                  }
                  R(If(IfThen(e, thn), els))
                case _cur =>
                  val (found, loc) = _cur match {
                    case (tk, l1) :: _ => (msg"${e.describe} followed by ${tk.describe}",
                      S(e.toLoc.foldRight(l1)(_ ++ _)))
                    case Nil => (msg"${e.describe}", e.toLoc)
                  }
                  err((msg"Expected 'then'/'else' clause; found $found instead" -> loc ::
                    msg"Note: 'if' expression started here:" -> S(l0) :: Nil))
                  R(If(IfThen(e, errExpr), N))
              }
          }
        }
        
      case Nil =>
        err(msg"Unexpected end of $description; an expression was expected here" -> lastLoc :: Nil)
        R(errExpr)
      case ((KEYWORD(";") /* | NEWLINE */ /* | BRACKETS(Curly, _) */, _) :: _) =>
        R(UnitLit(true))
        // R(errExpr) // TODO
      case (tk, l0) :: _ =>
        err(msg"Unexpected ${tk.describe} in expression position" -> S(l0) :: Nil)
        consume
        exprOrIf(prec)(et = et, fe = true, l = implicitly)
  }}
  
  private def errExpr =
    // Tup(Nil).withLoc(lastLoc) // TODO FIXME produce error term instead
    UnitLit(true).withLoc(lastLoc) // TODO FIXME produce error term instead
  
  def exprCont(acc: Term, prec: Int, allowNewlines: Bool)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(prec, s"`$acc`", allowNewlines) { l =>
    cur match {
      case (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        val v = Var(opStr).withLoc(S(l0))
        // printDbg(s">>> $opStr ${opPrec(opStr)}")
        exprOrIf(opPrec(opStr)._2) match {
          case L(rhs) =>
            L(IfOpApp(acc, v, rhs))
          case R(rhs) =>
            opStr match {
              case "=>" => {
                exprCont(rhs, prec, allowNewlines) match {
                  case R(p) => R(Lam(toParams(acc), p))
                  case L(b) => err(msg"Unexpected ifBody" -> b.toLoc :: Nil); L(b)
                }
              }
              case _ =>
                exprCont(App(App(v, toParams(acc)), toParams(rhs)), prec, allowNewlines)
            }
        }
      case (SPACE, l0) :: _ =>
        consume
        exprCont(acc, prec, allowNewlines)
      case (SELECT(name), l0) :: _ => // TODO precedence?
        consume
        exprCont(Sel(acc, Var(name).withLoc(S(l0))), prec, allowNewlines)
      // case (br @ BRACKETS(Indent, (SELECT(name), l0) :: toks), _) :: _ =>
      case (br @ BRACKETS(Indent, (SELECT(name), l0) :: toks), _) :: _ if prec <= 1 =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.exprCont(Sel(acc, Var(name).withLoc(S(l0))), 0, allowNewlines = true))
        if (allowNewlines) res match {
          case L(ifb) => L(ifb) // TODO something else?
          case R(res) => exprCont(res, 0, allowNewlines)
        }
        else res
      case (br @ BRACKETS(Indent, (IDENT(opStr, true), l0) :: toks), _) :: _ =>
        consume
        rec(toks, S(br.innerLoc), br.describe).concludeWith(_.opBlock(acc, opStr, l0))
      case Nil => R(acc)
      case (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
      // case (KEYWORD("then"), _) :: _ if /* expectThen && */ prec <= 1 =>
        consume
        val e = expr(0)
        L(IfThen(acc, e))
      case (NEWLINE, _) :: (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
        consume
        consume
        val e = expr(0)
        L(IfThen(acc, e))
      case (NEWLINE, _) :: _ if allowNewlines =>
        consume
        exprCont(acc, 0, allowNewlines)
      case (COMMA | NEWLINE | KEYWORD("then" | "else" | "in" | ";" | "=")
        | IDENT(_, true) | BRACKETS(Curly, _), _) :: _ => R(acc)
      
      case (KEYWORD("of"), _) :: _ if prec <= 1 =>
        consume
        val as = argsMaybeIndented()
        val res = App(acc, Tup(as))
        exprCont(res, prec, allowNewlines)
      case (br @ BRACKETS(Indent, (KEYWORD("of"), _) :: toks), _) :: _ if prec <= 1 =>
        consume
        // 
        // val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        // val res = App(acc, Tup(as))
        // exprCont(res, 0, allowNewlines = true) // ?!
        // 
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith { nested =>
          val as = nested.argsMaybeIndented()
          nested.exprCont(App(acc, Tup(as)), 0, allowNewlines = true)
        }
        // if (allowNewlines) 
        res match {
          case L(ifb) => L(ifb) // TODO something else?
          case R(res) => exprCont(res, 0, allowNewlines)
        }
        // else res
        
      case (BRACKETS(Indent, (KEYWORD("then"|"else"), _) :: toks), _) :: _ => R(acc)
      
      /* 
      case (br @ BRACKETS(Indent, toks), _) :: _ 
      if prec === 0 && !toks.dropWhile(_._1 === SPACE).headOption.map(_._1).contains(KEYWORD("else")) // FIXME
      =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.blockTerm)
        R(App(acc, res))
      */
      // case (br @ BRACKETS(Indent, (BRACKETS(Round | Square, toks1), _) :: toks2), _) :: _ =>
      case (br @ BRACKETS(Indent, toks @ (BRACKETS(Round | Square, _), _) :: _), _) :: _ if prec <= 1 =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.exprCont(acc, 0, allowNewlines = true))
        res match {
          case L(ifb) => L(ifb) // TODO something else?
          case R(res) => exprCont(res, 0, allowNewlines)
        }
        
      case (br @ BRACKETS(Angle, toks), loc) :: _ =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        // val res = TyApp(acc, as.map(_.mapSecond.to))
        val res = TyApp(acc, as.map {
          case (N, Fld(false, false, trm)) => trm.toType match {
            case L(d) => raise(d); Top // TODO better
            case R(ty) => ty
          }
          case _ => ???
        })
        exprCont(res, 0, allowNewlines)
        
      case (br @ BRACKETS(Square, toks), loc) :: _ =>
        consume
        val idx = rec(toks, S(br.innerLoc), "subscript").concludeWith(_.expr(0))
        val res = Subs(acc, idx.withLoc(S(loc)))
        exprCont(res, 0, allowNewlines)
        
        case (br @ BRACKETS(Round, toks), loc) :: _ =>
          consume
          val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
          val res = App(acc, Tup(as).withLoc(S(loc)))
          exprCont(res, 0, allowNewlines)
        case (KEYWORD("of"), _) :: _ =>
          consume
          val as = argsMaybeIndented()
          // val as = argsOrIf(Nil) // TODO
          val res = App(acc, Tup(as))
          exprCont(res, 0, allowNewlines)
          
      case c @ (h :: _) if (h._1 match {
        case KEYWORD(";" | "of") | BRACKETS(Round | Square, _)
          | BRACKETS(Indent, (
              KEYWORD(";" | "of")
              | BRACKETS(Round | Square, _)
              | SELECT(_)
            , _) :: _)
          => false
        case _ => true
      }) =>
        val as = argsMaybeIndented()
        val res = App(acc, Tup(as))
        raise(WarningReport(msg"Paren-less applications should use the 'of' keyword"
          -> res.toLoc :: Nil))
        exprCont(res, 0, allowNewlines)
        
      case _ => R(acc)
    }
  }
  
  def opBlock(acc: Term, opStr: Str, opLoc: Loc)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(s"`$acc`", opStr) { l =>
      val opv = Var(opStr).withLoc(S(opLoc))
      val rhs = exprOrIf(0)
      // val rhs = exprOrIf(1)
      rhs match {
        case R(rhs) =>
          val res = App(App(opv, acc), rhs)
          cur match {
            case (NEWLINE, _) :: c => // TODO allow let bindings...
              consume
              c match {
                case (IDENT(opStr2, true), opLoc2) :: _ =>
                  consume
                  opBlock(res, opStr2, opLoc2)
                case (tk, lo) :: _ =>
                  err(msg"Unexpected ${tk.describe} in operator block" -> S(lo) :: Nil)
                  consume
                  R(res)
                case Nil =>
                  R(res)
              }
            case _ =>
              R(res)
          }
        case L(rhs) =>
          L(IfOpsApp(acc, opIfBlock(opv -> rhs :: Nil)))
      }
  }
  def opIfBlock(acc: Ls[Var -> IfBody])(implicit et: ExpectThen, fe: FoundErr): Ls[Var -> IfBody] = wrap(acc) { l =>
      cur match {
        case (NEWLINE, _) :: c => // TODO allow let bindings...
          consume
          c match {
            case (IDENT(opStr2, true), opLoc2) :: _ =>
              consume
              val rhs = exprOrIf(0)
              // val rhs = exprOrIf(1)
              rhs match {
                case R(rhs) => ???
                case L(rhs) =>
                  opIfBlock(Var(opStr2).withLoc(S(opLoc2)) -> rhs :: acc)
              }
            case _ =>
              // printDbg(c)
              ???
          }
        case _ =>
          acc.reverse
      }
  }
  
  def tyArgs(implicit fe: FoundErr, et: ExpectThen): Opt[Ls[Type]] =
    cur match {
      case (IDENT("<", true), l0) :: _ => ???
      case _ => ???
    }
  
  def argsMaybeIndented()(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> Fld] =
    cur match {
      case (br @ BRACKETS(Indent, toks), _) :: _ if (toks.headOption match {
        case S((KEYWORD("then" | "else"), _)) => false
        case _ => true
      }) =>
        consume
        rec(toks, S(br.innerLoc), br.describe).concludeWith(_.args(true))
      case _ => args(false)
    }
  
  // TODO support comma-less arg blocks...?
  def args(allowNewlines: Bool, prec: Int = NoElsePrec)(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> Fld] =
    // argsOrIf(Nil).map{case (_, L(x))=> ???; case (n, R(x))=>n->x} // TODO
    argsOrIf(Nil, Nil, allowNewlines, prec).flatMap{case (n, L(x))=> 
        err(msg"Unexpected 'then'/'else' clause" -> x.toLoc :: Nil)
        n->Fld(false, false, errExpr)::Nil
      case (n, R(x))=>n->x::Nil} // TODO
  /* 
  def argsOrIf2()(implicit fe: FoundErr, et: ExpectThen): IfBlock \/ Ls[Opt[Var] -> Fld] = {
    // argsOrIf(Nil).partitionMap(identity).mapFirst(ifbods => ???)
    argsOrIf(Nil) match {
      case n -> L(ib) =>
        
      case n -> R(tm) =>
      case Nil => R(Nil)
    }
  }
  */
  def argsOrIf(acc: Ls[Opt[Var] -> (IfBody \/ Fld)], seqAcc: Ls[Statement], allowNewlines: Bool, prec: Int = NoElsePrec)
        (implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> (IfBody \/ Fld)] =
      wrap(acc, seqAcc) { l =>
    
    cur match {
      case Nil =>
        seqAcc match {
          case res :: seqAcc => 
            (N -> R(Fld(false, false, Blk((res :: seqAcc).reverse))) :: acc).reverse
          case Nil =>
            acc.reverse
        }
      case (SPACE, _) :: _ =>
        consume
        argsOrIf(acc, seqAcc, allowNewlines, prec)
      case (NEWLINE | IDENT(_, true), _) :: _ => // TODO: | ...
        assert(seqAcc.isEmpty)
        acc.reverse
      case _ =>
    
    // val blck = block
    
    val argMut = cur match {
      case (KEYWORD("mut"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argSpec = cur match {
      case (KEYWORD("#"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argName = cur match {
      case (IDENT(idStr, false), l0) :: (KEYWORD(":"), _) :: _ => // TODO: | ...
        consume
        consume
        S(Var(idStr).withLoc(S(l0)))
      case _ => N
    }
    // val e = expr(NoElsePrec) -> argMut.isDefined
    val e = exprOrIf(prec).map(Fld(argMut.isDefined, argSpec.isDefined, _))
    
    def mkSeq = if (seqAcc.isEmpty) argName -> e else e match {
      case L(_) => ???
      case R(Fld(m, s, res)) =>
        argName -> R(Fld(m, s, Blk((res :: seqAcc).reverse)))
    }
    
    cur match {
      case (COMMA, l0) :: (NEWLINE, l1) :: _ =>
        consume
        consume
        argsOrIf(mkSeq :: acc, Nil, allowNewlines)
      case (COMMA, l0) :: _ =>
        consume
        argsOrIf(mkSeq :: acc, Nil, allowNewlines)
      case (NEWLINE, l1) :: _ if allowNewlines =>
        consume
        argName match {
          case S(nme) =>
            err(msg"Unexpected named argument name here" -> nme.toLoc :: Nil)
          case N =>
        }
        e match {
          case L(_) => ???
          case R(Fld(false, false, res)) =>
            argsOrIf(acc, res :: seqAcc, allowNewlines)
          case R(_) => ???
        }
      case _ =>
        (mkSeq :: acc).reverse
    }
    
  }
  }
  
  def bindings(acc: Ls[Var -> Term])(implicit fe: FoundErr): Ls[Var -> Term] = 
    cur match {
      case (SPACE, _) :: _ =>
        consume
        bindings(acc)
      case (NEWLINE | IDENT(_, true) | KEYWORD(";"), _) :: _ => // TODO: | ...
        acc.reverse
      case (IDENT(id, false), l0) :: _ =>
        consume
        val (success, _) = skip(KEYWORD("=")) // TODO kw?
        val rhs = expr(0)(fe = foundErr || !success, l = implicitly)
        // cur.dropWhile(_ === SPACE) match {
        //   case (KEYWORD("in"), _) :: _ =>
        //     acc.reverse
        //   case _ => ???
        // }
        val v = Var(id).withLoc(S(l0))
        cur match {
          case (COMMA, l1) :: _ =>
            consume
            bindings((v -> rhs) :: acc)
          case _ =>
            ((v -> rhs) :: acc).reverse
        }
      case _ =>
        Nil
  }
  
  
  
}

