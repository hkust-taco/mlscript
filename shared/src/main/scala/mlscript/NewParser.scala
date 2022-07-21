package mlscript

import scala.util.chaining._
import scala.annotation.tailrec
import sourcecode.{Name, Line}

import utils._, shorthands._
import mlscript.Message._


object NewParser {
  
  type ExpectThen >: Bool
  type FoundErr >: Bool  // may be better done as:  class FoundErr(var found: Bool)
  
  def expectThen(implicit ptr: ExpectThen): Bool = ptr === true
  def foundErr(implicit ptr: FoundErr): Bool = ptr === true
  
  // def parse(ts: Iterable[Token], debug: Boolean = false): Term = {
  //   val p = new NewParser(ts.iterator, debug)
  //   val t = p.expr(0)
  //   // printDbg(p.cur)
  //   if (p.cur.nonEmpty) fail(p.cur.toList ++ p.rest)
  //   t
  // }
  
  // val prec: Map[Char,Int] = """
  //   =
  //   @
  //   :
  //   |
  //   ^
  //   &
  //   < >
  //   + -
  //   * / %
  //   !
  // """.split('\n').zipWithIndex.flatMap { (cs, i) =>
  //     cs.filterNot(_.isWhitespace).map(_ -> i)
  // }.toMap.withDefaultValue(Int.MaxValue) // prec('~') == 2147483647
}
import NewParser._

abstract class NewParser(origin: Origin, tokens: Ls[Token -> Loc], raiseFun: Diagnostic => Unit, val dbg: Bool) {
  
  def raise(mkDiag: => Diagnostic)(implicit fe: FoundErr = false): Unit =
    if (!foundErr) raiseFun(mkDiag)
  
  def mkLoc(l: Int, r: Int): Loc =
    Loc(l, r, origin)

  protected def printDbg(msg: => Any): Unit
  protected var indent = 0
  private def wrap[R](args: Any)(mkRes: Unit => R)(implicit l: Line, n: Name): R = try {
    // printDbg(s"@ ${n.value}${if (args.isInstanceOf[Product]) args else s"($args)"}    [at l.${l.value}]")
    printDbg(s"@ ${n.value}${args match {
      case _: Product => args
      case it: Iterable[_] => it.mkString("(", ",", ")")
      case _ => s"($args)"
    }}    [at l.${l.value}]")
    indent += 1
    // mkRes
    mkRes(())
  } finally indent -= 1
  
  def parseAll[R](parser: => R): R = {
    // val t = expr(0, allowSpace = false)
    val res = parser
    // printDbg(p.cur)
    // if (cur.nonEmpty) fail(cur)
    cur match {
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        raise(CompilationError(msg"Expected end of input; found ${relevantToken.describe} instead" -> S(rl) :: Nil))
      case Nil => ()
    }
    res
  }
  
  // def fail(ts: List[TokLoc]): Unit =
  //   // throw new IllegalArgumentException("Parse failure on: " + ts.mkString("|")) // TODO
  //   raise(CompilationError(msg"Parse failure on: ${ts.mkString("|")}" -> N :: Nil))
  
  type TokLoc = (Token, Loc)
  
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
  
  def pe(msg: Message, l: Loc, rest: (Message, Opt[Loc])*): Unit =
    raise(CompilationError(msg -> S(l) :: rest.toList)) // TODO parse err
  
  
  
  private var _cur: Ls[TokLoc] = tokens
  
  private def summarizeCur =
    NewLexer.printTokens(_cur.take(5)) + (if (_cur.size > 5) "..." else "")
  
  private def cur(implicit l: Line, n: Name) = {
    // if (dbg) printDbg(s"l.${l.value} => ${n.value}\t\tinspects ${NewLexer printTokens _cur}")
    if (dbg) printDbg(s"? ${n.value}\t\tinspects ${summarizeCur}    [at l.${l.value}]")
    _cur
  }
  
  // val accept: Ls[TokLoc] => Unit =
  //   cur = _
  
  // def block(ts: LTL): (AST, LTL) =
  //   cur match {
  //     case t :: accept() => ???
  //     case _ => ???
  //   }
  
  // def next(implicit n: Name): Option[Token] = {
  //   if (dbg) printDbg(s"=> ${n.value}\t\tinspects next ${_next}")
  //   _next
  // }
  def consume(implicit l: Line, n: Name): Unit = {
    // if (dbg) printDbg(s"=> ${n.value}\t\tconsumes ${NewLexer printTokens _cur}")
    // if (dbg) printDbg(s"! ${n.value}\t\tconsumes ${summarizeCur}    [at l.${l.value}]")
    // if (dbg) printDbg(s"! ${n.value}\t\tconsumes ${_cur.headOption.fold("X")(_._1.toString)}    [at l.${l.value}]")
    if (dbg) printDbg(s"! ${n.value}\t\tconsumes ${NewLexer.printTokens(_cur.take(1))}    [at l.${l.value}]")
    _cur = _cur.tailOption.getOrElse(Nil) // FIXME throw error if empty?
    // _next = ite.nextOption
  }
  def skip(tk: Token, ignored: Set[Token] = Set(SPACE), allowEnd: Bool = false, note: => Ls[Message -> Opt[Loc]] = Nil)
        // (implicit n: Name): Loc \/ Opt[Loc] = {
        (implicit fe: FoundErr): (Bool, Opt[Loc]) = wrap(tk, ignored, allowEnd) { l =>
    require(!ignored(tk))
    // if (!cur.headOption.forall(_._1 === tk)) {
    //   // fail(cur)
    //   raise(CompilationError(msg"Expected: ${tk.describe}; found: ${ts.mkString("|")}" -> N :: Nil))
    // }
    val res = cur match {
      case (b @ CLOSE_BRACKET(_), l2) :: _ if tk =/= b && allowEnd => return (true, S(l2.left))
      case (tk2, l2) :: _ =>
        if (ignored(tk2)) {
          consume
          return skip(tk, ignored, allowEnd, note)
        } else if (tk2 =/= tk) {
          if (!foundErr) raise(CompilationError(
            msg"Expected ${tk.describe}; found ${tk2.describe} instead" -> S(l2) :: note))
          (false, S(l2))
        } else (true, S(l2))
      case Nil =>
        if (!allowEnd)
          if (!foundErr) raise(CompilationError(
            msg"Expected ${tk.describe}; found end of input instead" -> lastLoc :: note))
        (allowEnd, N)
    }
    consume
    res
  }
  // private def skipDeindent: Loc \/ Opt[Loc] = 
  // private def skipDeindent(allowNewline: Bool = true)(implicit l: Line): (Bool, Opt[Loc]) = wrap(()) { l =>
  private def skipDeindent(allowNewlineOn: Ls[TokLoc] => Bool = _ => true)(implicit l: Line): (Bool, Opt[Loc]) = wrap(()) { l =>
    cur match {
      case (DEINDENT, l0) :: _ => consume; (true, S(l0))
      // case (NEWLINE, l0) :: _ if allowNewline => consume; _cur ::= (INDENT, l0); (true, N)
      case (NEWLINE, l0) :: c if allowNewlineOn(c) => consume; _cur ::= (INDENT, l0); (true, N)
      case Nil => (true, N)
      case (tk, l0) :: _ =>
        raise(CompilationError(msg"Expected end of indented block; found ${tk.describe} instead" -> S(l0) :: Nil))
        (false, S(l0))
    }
  }
  
  import BracketKind._
  
  private lazy val lastLoc =
    tokens.lastOption.map(_._2.right)
  
  private def curLoc = _cur.headOption.map(_._2)
  
  def blockTerm: Blk = {
    val ts = block(false, false)
    // skip(DEINDENT, allowEnd = true, note =
    //   msg"Note: unmatched indentation is here:" -> S(l0) :: Nil)
    // R(Blk(ts)) // TODO
    val es = ts.map {
      case L(t) =>
        raise(CompilationError(msg"Unexpected 'then'/'else' clause" -> t.toLoc :: Nil))
        errExpr
      case R(e) => e
    }
    Blk(es)
  }
  def typingUnit: TypingUnit = {
    val ts = block(false, false)
    val es = ts.map {
      case L(t) =>
        raise(CompilationError(msg"Unexpected 'then'/'else' clause" -> t.toLoc :: Nil))
        L(errExpr)
      case R(d: NuDecl) => R(d)
      case R(e: Term) => L(e)
    }
    TypingUnit(es)
  }
  
  def toParams(t: Term): Tup = t match {
    case t: Tup => t
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
      case (DEINDENT, _) :: _ => Nil
      case (NEWLINE, _) :: _ => consume; block
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
            // val (tn, success) = c.dropWhile(_._1 === SPACE && { consume; true }) match {
            val (tn, success) = yeetSpaces match {
              case (IDENT(idStr, false), l1) :: _ =>
                consume
                (TypeName(idStr).withLoc(S(l1)), true)
              case c =>
                val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                raise(CompilationError(
                  msg"Expected a type name; found ${tkstr} instead" -> loc :: Nil))
                consume
                // R(errExpr)
                (TypeName("<error>").withLoc(curLoc.map(_.left)), false)
            }
            def parents(Sep: Token): Ls[NamedType] = yeetSpaces match {
              case (Sep, _) :: _ =>
                consume
                // val ty = typ
                (typ match {
                  case nt: NamedType => nt
                  // case at: AppliedType => at
                  // case tn: TypeName => AppliedType(tn, Nil)
                  case _ =>
                    ??? // TODO raise
                    AppliedType(TypeName("<error>"), Nil)
                }) :: parents(COMMA)
              case _ => Nil
            }
            val ps = parents(KEYWORD(":"))
            // val body = typingUnit()
            val body = cur.dropWhile(_._1 === SPACE && { consume; true }) match {
              case (OPEN_BRACKET(Curly), l1) :: _ =>
                consume
                val res = yeetSpaces match {
                  case (INDENT, _) :: _ =>
                    consume
                    val res = typingUnit
                    skipDeindent()
                    res
                  case _ => typingUnit
                }
                skip(CLOSE_BRACKET(Curly), ignored = Set(SPACE, NEWLINE, INDENT))
                res
              case _ =>
                // println(c)
                TypingUnit(Nil)
            }
            R(NuTypeDef(kind, tn, Nil, Nil, ps, body))
          case (KEYWORD("fun"), l0) :: c => // TODO support rec?
            consume
            val (v, success) = c.dropWhile(_._1 === SPACE && { consume; true }) match {
              case (IDENT(idStr, false), l1) :: _ =>
                consume
                (Var(idStr).withLoc(S(l1)), true)
              case c =>
                val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                raise(CompilationError(
                  // msg"Expected a function name; found ${"[TODO]"} instead" -> N :: Nil))
                  msg"Expected a function name; found ${tkstr} instead" -> loc :: Nil))
                consume
                // R(errExpr)
                (Var("<error>").withLoc(curLoc.map(_.left)), false)
            }
            foundErr || !success pipe { implicit fe =>
              val ps = funParams
              // skip(KEYWORD("="))
              val asc = yeetSpaces match {
                case (KEYWORD(":"), _) :: _ =>
                  consume
                  // val e = expr(0)
                  // S(e)
                  S(typ)
                // case (KEYWORD("="), _) =>
                case _ => N
              }
              yeetSpaces match {
                case (KEYWORD("="), _) :: _ =>
                  consume
                  val body = expr(0)
                  // val annotatedBody = asc.fold(body)(ty => Asc(body, ty.toType match {
                  //   case R(ty) => ty
                  //   case L(d) => ???
                  // }))
                  val annotatedBody = asc.fold(body)(ty => Asc(body, ty))
                  // R(Def(false, v, L(ps.foldRight(body)((i, acc) => Lam(toParams(i), acc)))))
                  // R(Def(false, v, L(ps.foldRight(annotatedBody)((i, acc) => Lam(i, acc)))))
                  R(NuFunDef(v, Nil, L(ps.foldRight(annotatedBody)((i, acc) => Lam(i, acc)))))
                case c =>
                  asc match {
                    case S(ty) =>
                    // case S(tytrm) =>
                    //   // val (ty, ds) = tytrm.toType
                    //   // ds.foreach(raise)
                    //   val ty = tytrm.toType match {
                    //     case L(d) => raise(d); Top // TODO better
                    //     case R(ty) => ty
                    //   }
                      // R(Def(false, v, R(PolyType(Nil, ty)))) // TODO rm PolyType after FCP is merged
                      R(NuFunDef(v, Nil, R(PolyType(Nil, ty)))) // TODO rm PolyType after FCP is merged
                    case N =>
                      // TODO dedup:
                      val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                      raise(CompilationError(
                        msg"Expected ':' or '=' followed by a function body or signature; found ${tkstr} instead" -> loc :: Nil))
                      consume
                      // R(Def(false, v, L(ps.foldRight(errExpr: Term)((i, acc) => Lam(i, acc)))))
                      R(NuFunDef(v, Nil, L(ps.foldRight(errExpr: Term)((i, acc) => Lam(i, acc)))))
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
        // Tup(args(Nil).map{case (_, L(x))=> ???; case (n, R(x))=>n->x} // TODO
        //   ) :: funParams
        Tup(args() // TODO
          ) :: funParams
      case (OPEN_BRACKET(Round), _) :: _ =>
        consume
        val as = args() // TODO
        skip(CLOSE_BRACKET(Round), ignored = Set(SPACE, NEWLINE, INDENT))
        Tup(as) :: funParams
      case (tk, l0) :: _ =>
        // val e = expr(0)
        // e :: funParams
        // ???
        raise(CompilationError(
          // msg"Expected a function name; found ${"[TODO]"} instead" -> N :: Nil))
          msg"Expected function parameter list; found ${tk.describe} instead" -> S(l0) :: Nil))
        consume
        Nil
    }
  }
  
  // def expr(prec: Int, allowSpace: Bool = true)(implicit fe: FoundErr): Term =
  def expr(prec: Int, allowSpace: Bool = true)(implicit fe: FoundErr, l: Line): Term = wrap(prec,allowSpace) { l =>
    exprOrIf(prec, allowSpace)(et = false, fe = fe, l = implicitly) match {
      case R(e) => e
      case L(e) =>
        // ??? // TODO
        raise(CompilationError(msg"Expected an expression; found a 'then'/'else' clause instead" -> e.toLoc :: Nil))
        errExpr
    }
  }
  
  private def warnDbg(msg: Any, loco: Opt[Loc] = curLoc): Unit =
    raise(Warning(msg"[${cur.headOption.map(_._1).mkString}] ${""+msg}" -> loco :: Nil))
  
  def exprOrIf(prec: Int, allowSpace: Bool = true)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(prec, allowSpace) { l =>
    // implicit val n: Name = Name(s"exprOrIf($prec,$et)")
    // if (prec > 10) ???
    cur match {
      case (SPACE, l0) :: _ if allowSpace =>
        consume
        exprOrIf(prec, allowSpace)
      case (INDENT, l0) :: _ if allowSpace =>
        consume
        val ts = block
        skip(DEINDENT, allowEnd = true, note =
          // msg"Note: unmatched indentation is here:" -> S(l0) :: Nil)
          msg"Note: indented block starts here:" -> S(l0) :: Nil)
        // R(Blk(ts)) // TODO
        val es = ts.map { case L(t) => return L(IfBlock(ts)); case R(e) => e }
        R(Blk(es))
      // case (NEWLINE, l0) :: _ =>
      //   Tup(Nil).withLoc(lastLoc)
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme).withLoc(S(l0)), prec)
      case (OPEN_BRACKET(bk @ (Round | Square)), l0) :: _ =>
        consume
        // val res = expr(0)
        val res = args()
        val (success, l1) = skip(CLOSE_BRACKET(bk), ignored = Set(SPACE, NEWLINE, INDENT), note =
          msg"Note: unmatched ${bk.name} was opened here:" -> S(l0) :: Nil)
        exprCont(Bra(bk === Curly, Tup(res)).withLoc(S(l0 ++ l1)), prec)
      // case Oper(opStr) :: _ if isPrefix(opStr) && opPrec(opStr)._1 > prec =>
      // case (IDENT(opStr, true), l0) :: _ if isPrefix(opStr) =>
      //   consume
      //   val rhs = expr(opPrec(opStr)._2)
      //   exprCont(Prefix(opStr, rhs), prec)
      case (KEYWORD("let"), l0) :: _ =>
        consume
        val bs = bindings(Nil)
        // Let(false, )
        // ???
        val body = cur.dropWhile(_._1 === SPACE && { consume; true }) match {
          // case (KEYWORD("in") | IDENT(";", true), _) :: _ =>
          case (KEYWORD("in") | KEYWORD(";"), _) :: _ =>
            consume
            exprOrIf(0)
          case (NEWLINE, _) :: _ =>
            // UnitLit(true)
            consume
            exprOrIf(0)
          case _ =>
            R(UnitLit(true))
        }
        // R(bs.foldRight(body) { case ((v, r), acc) => Let(false, v, r, acc) })
        bs.foldRight(body) {
          case ((v, r), R(acc)) => R(Let(false, v, r, acc))
          case ((v, r), L(acc)) => L(IfLet(false, v, r, acc))
        }
      case (KEYWORD("else"), l0) :: _ =>
        consume
        val e = expr(0)
        L(IfElse(e).withLoc(S(l0 ++ e.toLoc)))
      case (KEYWORD("if"), l0) :: _ =>
        consume
        /* 
        val cond = expr(0)
        skip(KEYWORD("then"), ignored = Set(SPACE, NEWLINE), note =
          msg"Note: unmatched if here:" -> S(l0) :: Nil)
        val thn = expr(0)
        */
        val body = exprOrIf(0)(et = true, fe = fe, l = implicitly) match {
          case L(b) => b
          case R(e) =>
            // ??? // TODO
            /* 
            val (desc, loc) = _cur match {
              case (tk, l1) :: _ => (tk.describe, S(l1))
              case Nil => (e.describe, e.toLoc)
            }
            raise(CompilationError(msg"Expected 'then'/'else' clause; found ${desc} instead" -> 
                // e.toLoc ::
                // curLoc ::
                loc ::
              msg"Note: 'if' expression started here:" -> S(l0) :: Nil))
            */
            val (found, loc) = _cur.dropWhile(_._1 === SPACE && { consume; true }) match {
              case (tk, l1) :: _ => (msg"${e.describe} followed by ${tk.describe}",
                // e.toLoc.fold(S(l1))(_ ++ l1 |> some))
                // e.toLoc.fold(S(l1))(_ ++ l1 |> some))
                S(e.toLoc.fold(l1)(_ ++ l1)))
                // e.toLoc.orElse(S(l1)))
              case Nil => (msg"${e.describe}", e.toLoc)
            }
            raise(CompilationError(msg"Expected 'then'/'else' clause; found $found instead" -> loc ::
              msg"Note: 'if' expression started here:" -> S(l0) :: Nil))
            IfThen(e, errExpr)
        }
        // warnDbg("huh")
        
        // val els = cur match {
        //   case (KEYWORD("else"), _) :: _ => 
        //   case _ => N
        // }
        val (hasEls, hasIndent) = cur match {
          case (SPACE, _) :: (KEYWORD("else"), _) :: _ => consume; (true, false) // no changes?
          case (KEYWORD("else"), _) :: _ => consume; (true, false)
          case (NEWLINE, _) :: (KEYWORD("else"), _) :: _ => consume; consume; (true, false)
          case (INDENT, _) :: (KEYWORD("else"), _) :: _ => consume; consume; (true, true) // FIXME consume matching DEINDENT
          case _ => (false, false)
        }
        // raiseDbg(hasEls)
        val els = Option.when(hasEls)(expr(0))
        // R(If(IfThen(cond, thn), els))
        // 
        if (hasIndent) skipDeindent(allowNewlineOn = _ => false)
        // R(If(body, els))
        // 
        // if (hasIndent) {
        //   val (success, _) = skipDeindent()
        //   if (success) {
        //     res match {
        //       case L(res) => 
        //         L(res)
        //       case R(res) =>
        //         exprCont(res, 0)
        //     }
        //   }
        //   else
        //   res
        // }
        // else R(If(body, els))
        // 
        cur match {
          case (INDENT, lind) :: _ =>
            // consume
            exprCont(If(body, els), 0)
          case _ => R(If(body, els))
        }
      case Nil =>
        raise(CompilationError(msg"Unexpected end of input; an expression was expected here" -> lastLoc :: Nil))
        R(errExpr)
      case //Nil | 
      // ((CLOSE_BRACKET(_) | COMMA | KEYWORD(";") /* | NEWLINE | DEINDENT */, _) :: _) =>
      ((CLOSE_BRACKET(_) | KEYWORD(";") /* | NEWLINE | DEINDENT */, _) :: _) =>
        R(UnitLit(true))
        // R(errExpr) // TODO
      case (tk, l0) :: _ =>
        // fail(cur)
        raise(CompilationError(msg"Unexpected ${tk.describe} in expression position" -> S(l0) :: Nil))
        consume
        exprOrIf(prec)(et = et, fe = true, l = implicitly)
  }}
  
  private def errExpr =
    // Tup(Nil).withLoc(lastLoc) // TODO FIXME produce error term instead
    UnitLit(true).withLoc(lastLoc) // TODO FIXME produce error term instead
  
  def exprCont(acc: Term, prec: Int)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(prec, s"`$acc`") { l =>
    // implicit val n: Name = Name(s"exprCont($prec,$et)")
    cur match {
      case (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        // val rhs = expr(opPrec(opStr)._2)
        // // exprCont(Infix(acc, opStr, rhs), prec)
        // exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
        val v = Var(opStr).withLoc(N/*TODO*/)
        // printDbg(s">>> $opStr ${opPrec(opStr)}")
        exprOrIf(opPrec(opStr)._2) match {
          case L(rhs) =>
            L(IfOpApp(acc, v, rhs))
          case R(rhs) =>
            exprCont(App(App(v, acc), rhs), prec)
        }
      // case Oper(opStr) :: _ if isPostfix(opStr) =>
      // case Oper(opStr) :: _ if isPostfix(opStr) && opPrec(opStr)._1 > prec =>
      //   consume
      //   exprCont(Postfix(acc, opStr), prec)
      case (SPACE, l0) :: _ =>
        consume
        exprCont(acc, prec)
      // case (SPACE, l0) :: _ =>
      /* 
      // case (NEWLINE, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
      case (NEWLINE, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ prec === 0 =>
        // ??? // TODO
        consume
        consume
        // // val rhs = expr(opPrec(opStr)._2) // TODO if
        // val rhs = expr(1) // TODO if
        // exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)
        opBlock(acc, opStr, l0)
      */
      // case (NEWLINE, _) :: (INDENT, _) :: (IDENT(opStr, true), l0) :: _ =>
      // case (INDENT, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
      case (INDENT, _) :: (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ prec === 0 =>
        // consume
        // ??? // TODO
        consume
        consume
        /* 
        // val rhs = expr(opPrec(opStr)._2) // TODO if
        val rhs = expr(1) // TODO if
        val (success, _) = skipDeindent()
        exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)(et = et, fe = foundErr || !success)
        */
        val res = opBlock(acc, opStr, l0)
        // skipDeindent()
        val (success, _) = skipDeindent()
        if (success) {
          res match {
            case L(res) => 
              L(res)
            case R(res) =>
              exprCont(res, 0)
          }
        }
        else
        res
        // val rhs = exprOrIf(0)
        // val (success, _) = skipDeindent()
        // rhs match {
        //   case R(rhs) => 
        //     exprCont(App(App(Var(opStr).withLoc(N/*TODO*/), acc), rhs), prec)(et = et, fe = foundErr || !success)
        //   case L(rhs) => ???
        // }
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
      case (INDENT, _) :: (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
        consume
        consume
        val e = expr(0)
        // skip(DEINDENT)
        // skipDeindent(allowNewline = false)
        skipDeindent(allowNewlineOn = {
          case (KEYWORD("else"), _) :: _ => true
          case _ => false
        })
        L(IfThen(acc, e))
        // val (success, _) = skipDeindent()
        // if (success) 
        // else L(IfThen(acc, e))
      case (DEINDENT | COMMA | NEWLINE | KEYWORD("then" | "else" | "in" | ";" | "=")
        | CLOSE_BRACKET(Round) | IDENT(_, true) | OPEN_BRACKET(Curly), _) :: _ => R(acc)
      
      // case (INDENT, _) :: (KEYWORD("of"), _) :: _ if prec === 0 =>
      case (INDENT, _) :: (KEYWORD("of"), _) :: _ if prec <= 1 =>
        consume
        consume
        // TODO allow indent before the args... indented allow arg block
        val as = args()
        val res = App(acc, Tup(as))
        val (success, _) = skipDeindent(allowNewlineOn = {
          case (KEYWORD("of"), _) :: _ => true
          case _ => false
        })
        if (success) {
          // res match {
          //   case L(res) => 
          //     L(res)
          //   case R(res) =>
          //     exprCont(res, 0)
          // }
          exprCont(res, 0)
        }
        else
        R(res)
        
      // case c =>
      // case c @ ((KEYWORD("of"), _) :: _ | (OPEN_BRACKET(Round), _) :: _) =>
      // case c @ (h :: _) if h._1 =/= INDENT =>
      case c @ (h :: _) if (h._1 match {
        case INDENT => false
        case CLOSE_BRACKET(_) => false
        case KEYWORD(";") => false
        case _ => true
      }) =>
        val ofLess = c match {
          case (KEYWORD("of"), _) :: _ =>
            consume
            false
          case _ =>
            true
        }
        // val ofKw = curLoc
        val openedPar = cur match {
          case (OPEN_BRACKET(Round), l0) :: _ => consume; S(l0)
          case (SPACE, _) :: (OPEN_BRACKET(Round), l0) :: _ => consume; consume; S(l0)
          case _ => N
        }
        val as = args()
        // val as = argsOrIf(Nil) // TODO
        // val res = App(acc, Tup(as.map(_.mapSecond(_ -> false))))
        val res = App(acc, Tup(as))
        openedPar match {
          case S(l0) =>
            val (success, _) = skip(CLOSE_BRACKET(Round), ignored = Set(SPACE, NEWLINE, INDENT), note =
              msg"Note: unmatched application parenthesis was opened here:" -> S(l0) :: Nil)
            exprCont(res, 0)(et = et, fe = foundErr || !success, l = implicitly)
          case N =>
            if (ofLess)
              raise(Warning(msg"Paren-less applications should use the 'of' keyword"
                // -> ofKw :: Nil))
                -> res.toLoc :: Nil))
            // R(res)
            exprCont(res, 0)
        }
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
                case _ => ???
              }
            case _ =>
              R(res)
          }
        case L(rhs) =>
          // val res = IfOpsApp(acc, opv -> rhs :: Nil)
          // ???
          // opIfBlock(acc, opv -> rhs :: Nil)
          L(IfOpsApp(acc, opIfBlock(opv -> rhs :: Nil)))
      }
  }
  // def opIfBlock(acc: Term, opsApp: Ls[Var -> IfBody])(implicit et: ExpectThen, fe: FoundErr): Ls[Var -> IfBody] = wrap(acc, prec) {
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
          // R(res)
          // ???
          acc.reverse
      }
      /* 
      val rhs = exprOrIf(0)
      rhs match {
        case R(rhs) =>
          ???
        case L(rhs) =>
          val res = App(App(opv, acc), rhs)
          cur match {
            case (NEWLINE, _) :: c => // TODO allow let bindings...
              consume
              c match {
                case (IDENT(opStr2, true), opLoc2) :: _ =>
                  opBlock(acc, opStr2, opLoc2)
                case _ => ???
              }
            case _ =>
              R(res)
          }
          val res = IfOpsApp(acc, opv -> rhs :: Nil)
          ???
      }
      */
  }
  
  // TODO support comma-less arg blocks...
  def args()(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> Fld] =
    // argsOrIf(Nil).map{case (_, L(x))=> ???; case (n, R(x))=>n->x} // TODO
    argsOrIf(Nil).flatMap{case (n, L(x))=> 
        raise(CompilationError(msg"Unexpected 'then'/'else' clause" -> x.toLoc :: Nil))
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
  def argsOrIf(acc: Ls[Opt[Var] -> (IfBody \/ Fld)])(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> (IfBody \/ Fld)] =
    cur match {
      case (SPACE, _) :: _ =>
        consume
        argsOrIf(acc)
      case (NEWLINE | IDENT(_, true), _) :: _ => // TODO: | ...
        acc.reverse
      case _ =>
    // }
    // {
    
    val argMut = cur match {
      case (KEYWORD("mut"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argName = cur match {
      // case (IDENT(idStr, false), l0) :: (IDENT(":", true), _) :: _ =>
      case (IDENT(idStr, false), l0) :: (KEYWORD(":"), _) :: _ => // TODO: | ...
        consume
        consume
        S(Var(idStr).withLoc(S(l0)))
      case _ => N
    }
    // val e = expr(NoElsePrec) -> argMut.isDefined
    val e = exprOrIf(NoElsePrec).map(Fld(argMut.isDefined, false, _))
    cur match {
      case (COMMA, l0) :: _ =>
        consume
        argsOrIf((argName -> e) :: acc)
      case _ =>
        ((argName -> e) :: acc).reverse
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
        // skip(EQUALS)
        // skip(IDENT("=", true)) // TODO kw?
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

