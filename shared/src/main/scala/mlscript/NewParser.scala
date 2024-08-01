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
  
  final def expectThen(implicit ptr: ExpectThen): Bool = ptr === true
  final def foundErr(implicit ptr: FoundErr): Bool = ptr === true
  
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
      "",
      // ^ for keywords
      // ";",
      ",",
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
      "", // Precedence of application
      ".",
    ).zipWithIndex.flatMap {
      case (cs, i) => cs.filterNot(_ === ' ').map(_ -> (i + 1))
    }.toMap.withDefaultValue(Int.MaxValue)
  
  private val AppPrec = prec('.') - 1
  
  final def opCharPrec(opChar: Char): Int = prec(opChar)
  final def opPrec(opStr: Str): (Int, Int) = opStr match {
    case "is" => (4, 4)
    case "and" => (3, 3)
    case "or" => (2, 2)
    case "=>" =>
      // * The lambda operator is special:
      // *  it should associate very strongly on the left and very loosely on the right
      // *  so that we can write things like `f() |> x => x is 0` ie `(f()) |> (x => (x is 0))`
      val eqPrec = prec('.') // * We pick the tightest precedence
      (eqPrec, 1)
      // * Note: we used to do this instead which broke the example above on both sides:
      // val eqPrec = prec('=')
      // (eqPrec, eqPrec - 1)
    case "+." | "-." | "*." =>
      (prec(opStr.head), prec(opStr.head))
    case _ if opStr.exists(_.isLetter) =>
      (5, 5)
    case _ =>
      val r = opStr.last
      (prec(opStr.head), prec(r) - (if (r === '@' || r === '/' || r === ',' || r === ':') 1 else 0))
  }
  
}
import NewParser._

abstract class NewParser(origin: Origin, tokens: Ls[Stroken -> Loc], newDefs: Bool, raiseFun: Diagnostic => Unit, val dbg: Bool, fallbackLoc: Opt[Loc], description: Str = "input") {
  outer =>
  
  private var freshCnt: Int = 0
  final def freshVar: Var = {
    val res = Var("_$" + freshCnt)
    freshCnt += 1
    res
  }
  
  object Spaces {
    def unapply(xs: Ls[Stroken -> Loc]): S[(() => Unit, Ls[Stroken -> Loc])] = xs match {
      case (SPACE, _) :: Spaces(cons, rest) => S((() => {cons(); consume}, rest))
      case _ => S(() => (), xs)
    }
  }
  
  final def rec(tokens: Ls[Stroken -> Loc], fallbackLoc: Opt[Loc], description: Str): NewParser =
    new NewParser(origin, tokens, newDefs, raiseFun, dbg, fallbackLoc, description) {
      def doPrintDbg(msg: => Str): Unit = outer.printDbg("> " + msg)
    }
  
  final def raise(mkDiag: => Diagnostic)(implicit fe: FoundErr = false): Unit =
    if (!foundErr) raiseFun(mkDiag)
  
  final def err(msgs: Ls[Message -> Opt[Loc]]): Unit =
    raise(ErrorReport(msgs, newDefs = true, source = Diagnostic.Parsing))
  
  final def mkLoc(l: Int, r: Int): Loc =
    Loc(l, r, origin)

  protected def doPrintDbg(msg: => Str): Unit
  protected def printDbg(msg: => Any): Unit =
    doPrintDbg("│ " * this.indent + msg)
  protected var indent = 0
  private def wrap[R](args: => Any)(mkRes: Unit => R)(implicit l: Line, n: Name): R = {
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
  
  final def parseAll[R](parser: => R): R = {
    val res = parser
    cur match {
      case c @ (tk, tkl) :: _ =>
        val (relevantToken, rl) = c.dropWhile(_._1 === SPACE).headOption.getOrElse(tk, tkl)
        err(msg"Expected end of input; found ${relevantToken.describe} instead" -> S(rl) :: Nil)
      case Nil => ()
    }
    res
  }
  
  final def concludeWith[R](f: this.type => R): R = {
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
  
  // def pe(msg: Message, l: Loc, rest: (Message, Opt[Loc])*): Unit =
  //   err((msg -> S(l) :: rest.toList)) // TODO parse err
  
  
  
  private var _cur: Ls[TokLoc] = tokens
  private var _modifiersCache: ModifierSet = ModifierSet.empty
  def resetCur(newCur: Ls[TokLoc]): Unit = {
    _cur = newCur
    _modifiersCache = ModifierSet.empty
  }
  
  private def summarizeCur =
    NewLexer.printTokens(_cur.take(5)) + (if (_cur.sizeIs > 5) "..." else "")
  
  private def cur(implicit l: Line, n: Name) = {
    if (dbg) printDbg(s"? ${n.value}\t\tinspects ${summarizeCur}    [at l.${l.value}]")
    while (!_cur.isEmpty && (_cur.head._1 match {
      case COMMENT(_) => true
      case _ => false
    })) consume
    _cur
  }
  
  final def consume(implicit l: Line, n: Name): Unit = {
    if (dbg) printDbg(s"! ${n.value}\t\tconsumes ${NewLexer.printTokens(_cur.take(1))}    [at l.${l.value}]")
    resetCur(_cur.tailOption.getOrElse(Nil)) // FIXME throw error if empty?
  }
  
  // TODO simplify logic – this is no longer used much
  final def skip(tk: Stroken, ignored: Set[Stroken] = Set(SPACE), allowEnd: Bool = false, note: => Ls[Message -> Opt[Loc]] = Nil)
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
  final def blockTerm: Blk = {
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
  
  final def typingUnit: TypingUnit = {
    val ts = block(false, false)
    val es = ts.map {
      case L(t) =>
        err(msg"Unexpected 'then'/'else' clause" -> t.toLoc :: Nil)
        errExpr
      case R(d: NuDecl) => d
      case R(e: Term) => e
      case R(c: Constructor) => c
      case _ => ???
    }
    TypingUnit(es)
  }
  final def typingUnitMaybeIndented(implicit fe: FoundErr): TypingUnit = yeetSpaces match {
    case (br @ BRACKETS(Indent, toks), _) :: _ =>
      consume
      rec(toks, S(br.innerLoc), br.describe).concludeWith(_.typingUnit)
    case _ => typingUnit
  }
  final def curlyTypingUnit(implicit fe: FoundErr): Opt[TypingUnit] = yeetSpaces match {
    case (br @ BRACKETS(Curly, toks), l1) :: _ =>
      consume
      S(rec(toks, S(br.innerLoc), br.describe).concludeWith(_.typingUnitMaybeIndented).withLoc(S(l1)))
    case _ =>
      N
  }
  
  final def toParamsTy(t: Type): Tuple = t match {
    case t: Tuple => t
    case _ => Tuple((N, Field(None, t)) :: Nil)
  }
  final def typ(prec: Int = 0)(implicit fe: FoundErr, l: Line): Type =
    mkType(expr(prec))
  
  case class ModifierSet(mods: Map[Str, Loc]) {
    def handle(mod: Str): (Opt[Loc], ModifierSet) =
      mods.get(mod) -> copy(mods = mods - mod)
    def done: Unit = mods.foreachEntry { (mod, loc) =>
      err(msg"Unrecognized modifier `${mod}` in this position" -> S(loc) :: Nil)
    }
  }
  object ModifierSet {
    val empty: ModifierSet = ModifierSet(Map.empty)
    private def go(acc: ModifierSet): ModifierSet = cur match {
      case (KEYWORD(kw), l0) :: c if acc.mods.contains(kw) =>
        err(msg"Repeated modifier `${kw}`" -> S(l0) :: Nil)
        consume
        yeetSpaces
        go(acc)
      case (KEYWORD("declare"), l0) :: c =>
        consume
        yeetSpaces
        go(acc.copy(acc.mods + ("declare" -> l0)))
      case (KEYWORD("virtual"), l0) :: c =>
        consume
        yeetSpaces
        go(acc.copy(acc.mods + ("virtual" -> l0)))
      case (KEYWORD("mut"), l0) :: c =>
        consume
        yeetSpaces
        go(acc.copy(acc.mods + ("mut" -> l0)))
      case (KEYWORD("abstract"), l0) :: c =>
        consume
        yeetSpaces
        go(acc.copy(acc.mods + ("abstract" -> l0)))
      case _ if acc.mods.isEmpty => acc
      case (KEYWORD("class" | "infce" | "trait" | "mixin" | "type" | "namespace" | "module" | "fun" | "val" | "let"), l0) :: _ =>
        acc
      case (tok, loc) :: _ =>
        // TODO support indented blocks of modified declarations...
        err(msg"Unexpected ${tok.describe} token after modifier${if (acc.mods.sizeIs > 1) "s" else ""}" -> S(loc) :: Nil)
        acc
      case Nil =>
        ??? // TODO:
    }
    def unapply(__ : Ls[TokLoc]): S[ModifierSet -> Ls[TokLoc]] = {
      val res = go(_modifiersCache)
      _modifiersCache = res
      S(res, _cur)
    }
  }
  final def block(implicit et: ExpectThen, fe: FoundErr): Ls[IfBody \/ Statement] = {
    val annotations = parseAnnotations(true)

    cur match {
      case Nil => Nil
      case (NEWLINE, _) :: _ => consume; block
      case (SPACE, _) :: _ => consume; block
      case (KEYWORD("constructor"), l0) :: _ =>
        consume
        val res = yeetSpaces match {
          case (br @ BRACKETS(Round, toks), loc) :: _ =>
            consume
            val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()) // TODO
            val body = curlyTypingUnit.getOrElse(TypingUnit(Nil))
            Constructor(Tup(as).withLoc(S(loc)), Blk(body.entities).withLocOf(body))
          case _ =>
            err(msg"Expect parameter list for the constructor" -> S(l0) :: Nil)
            Constructor(Tup(Nil), Blk(Nil))
        }
        R(res.withLoc(S(l0 ++ res.getLoc))) :: block
      case c =>
        val t = c match {
          case ModifierSet(mods, (KEYWORD(k @ ("class" | "infce" | "trait" | "mixin" | "type" | "module")), l0) :: c) =>
            consume
            val (isDecl, mods2) = mods.handle("declare")
            val (isAbs, mods3) = mods2.handle("abstract")
            mods3.done
            val kind = k match {
              case "class" => Cls
              case "trait" => Trt
              case "mixin" => Mxn
              case "type" => Als
              case "module" => Mod
              case _ => die
            }
            val (tn, success) = yeetSpaces match {
              case (IDENT(idStr, _), l1) :: _ =>
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
              case (br @ BRACKETS(Angle | Square, toks), loc) :: _ =>
                consume
                /* 
                val ts = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()).map {
                  case (N, Fld(false, false, v @ Var(nme))) =>
                    TypeName(nme).withLocOf(v)
                  case nmeo -> param =>
                    err(msg"unsupported type parameter shape (${param.describe})" ->
                      param.value.toLoc :: Nil)
                    TypeName(nmeo.fold("<error>")(_.name)).withLocOf(param.value)
                }
                ts
                */
                rec(toks, S(br.innerLoc), br.describe).concludeWith(_.maybeIndented((p, _) => p.typeParams))
              case _ => Nil
            }
            val params = yeetSpaces match {
              case (br @ BRACKETS(Round, toks), loc) :: _ =>
                consume
                val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()) // TODO
                S(Tup(as).withLoc(S(loc)))
              case _ => N
            }
            def otherParents: Ls[Term] = yeetSpaces match {
              case (COMMA, _) :: _ =>
                consume
                expr(prec(',')) :: otherParents // we don't want to parse parent lists as including comma expressions
              case _ => Nil
            }
            val sigTrm = yeetSpaces match {
              case (KEYWORD("="), _) :: _ if kind is Als =>
                consume
                S(expr(0))
              case (KEYWORD(":"), _) :: _ if !(kind is Als) =>
                consume
                S(expr(0))
              case _ => N
            }
            val ps = yeetSpaces match {
              // case (KEYWORD("="), _) :: _ if kind is Als =>
              //   consume
              //   expr(0) :: otherParents
              case (KEYWORD("extends"), _) :: _ =>
                consume
                expr(prec(',')) :: otherParents // we don't want to parse parent lists as including comma expressions
              case _ => Nil
            }
            val (sigTrm2, ps2, fullTu) = curlyTypingUnit.fold {
              ps.lastOption match {
                case S(Rft(bse, tu)) => (sigTrm, (bse :: ps.reverse.tail).reverse, tu)
                case _ =>
                  sigTrm match {
                    case S(Rft(bse, tu)) => (S(bse), ps, tu)
                    case _ =>
                      (sigTrm, ps, TypingUnit(Nil))
                  }
              }
            }(tu => (sigTrm, ps, tu))
            val sig = sigTrm2.map(mkType(_))
            val (ctors, bodyStmts) = fullTu.entities.partitionMap {
              case c: Constructor => L(c)
              case t => R(t)
            }
            val tu = TypingUnit(bodyStmts).withLocOf(fullTu)
            if (ctors.lengthIs > 1) {
              err(msg"A class may have at most one explicit constructor" -> S(l0) :: Nil)
              N
            }
            val ctor = ctors.headOption
            val res =
              NuTypeDef(kind, tn, tparams, params, ctor, sig, ps2, N, N, tu)(isDecl, isAbs, annotations)
            R(res.withLoc(S(l0 ++ tn.getLoc ++ res.getLoc)))
            R(res.withLoc(S(l0 ++ res.getLoc)))
          
          case ModifierSet(mods, (KEYWORD(kwStr @ ("fun" | "val" | "let")), l0) :: c) => // TODO support rec?
            consume
            val (isDecl, mods2) = mods.handle("declare")
            val (isVirtual, mods3) = mods2.handle("virtual")
            val (isMut, mods4) = mods3.handle("mut")
            mods4.done
            val genField = kwStr =/= "let"
            val isLetRec = yeetSpaces match {
              case (KEYWORD("rec"), l1) :: _ if kwStr === "let" =>
                consume
                S(true)
              case c => if (kwStr === "fun") N else S(false)
            }
            val opStr = yeetSpaces match {
              case (BRACKETS(Round, ts), brackloc) :: _ =>
                ts match {
                  case (IDENT(opStr, true), l1) :: rest =>
                    consume
                    rest.dropWhile(_._1 === SPACE) match {
                      case Nil =>
                      case (tok, loc) :: ts =>
                        err((msg"Unexpected ${tok.describe} after symbolic name" -> S(loc) :: Nil))
                    }
                    S(Var(opStr).withLoc(S(l1)))
                  case (tok, loc) :: _ =>
                    consume
                    err((msg"Expected a symbolic name, found ${tok.describe} instead" -> S(loc) :: Nil))
                    N
                  case Nil =>
                    consume
                    err((msg"Expected a symbolic name between brackets, found nothing" -> S(brackloc) :: Nil))
                    N
                }
              case _ => N
            }
            val (v, success) = yeetSpaces match {
              case (IDENT(idStr, false), l1) :: _ =>
                consume
                (Var(idStr).withLoc(S(l1)), true)
              case c =>
                val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                err((msg"Expected a function name; found ${tkstr} instead" -> loc :: Nil))
                consume
                // R(errExpr)
                (Var("<error>").withLoc(curLoc.map(_.left)), false)
            }
            foundErr || !success pipe { implicit fe =>
              val tparams = if (kwStr === "let") Ls[TypeName]() else yeetSpaces match {
                case (br @ BRACKETS(Angle | Square, toks), loc) :: _ =>
                  consume
                  val ts = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()).map {
                    case (N, Fld(FldFlags(false, false, _), v @ Var(nme))) =>
                      TypeName(nme).withLocOf(v)
                    case _ => ???
                  }
                  ts
                case _ => Nil
              }
              val (ps, transformBody) = yeetSpaces match {
                case (br @ BRACKETS(Round, Spaces(cons, (KEYWORD("override"), ovLoc) :: rest)), loc) :: rest2 =>
                  resetCur(BRACKETS(Round, rest)(br.innerLoc) -> loc :: rest2)
                  funParams match {
                    case ps @ Tup(N -> Fld(FldFlags(false, false, gen), pat) :: Nil) :: Nil =>
                      val fv = freshVar
                      (Tup(N -> Fld(FldFlags(false, false, gen), fv) :: Nil) :: Nil, S(
                        (body: Term) => If(IfOpApp(fv, Var("is"), IfThen(pat, body)), S(
                          App(Sel(Super().withLoc(S(ovLoc)), v), Tup(N -> Fld(FldFlags(false, false, gen), fv) :: Nil))
                        ))
                      ))
                    case r =>
                      err(msg"Unsupported 'override' parameter list shape" -> S(br.innerLoc) :: Nil)
                      (r, N)
                  }
                case _ =>
                  (funParams, N)
              }
              val asc = yeetSpaces match {
                case (KEYWORD(":"), _) :: _ =>
                  consume
                  // S(typ(2))
                  S(typ(0))
                case _ => N
              }
              yeetSpaces match {
                case (KEYWORD("="), _) :: _ =>
                  consume
                  val body = expr(0)
                  val newBody = transformBody.fold(body)(_(body))
                  val annotatedBody = asc.fold(newBody)(ty => Asc(newBody, ty))
                  yeetSpaces match {
                    case (KEYWORD("in"), l1) :: _ if kwStr === "let" =>
                      consume
                      if (tparams.nonEmpty) err(msg"Unsupported type parameters on 'let' binding" -> S(l1) :: Nil)
                      val rest = expr(0)
                      R(Let(isLetRec.getOrElse(die), v, body, rest).withLoc(S(l0 ++ annotatedBody.toLoc)))
                    case _ =>
                      R(NuFunDef(
                          isLetRec, v, opStr, tparams, L(ps.foldRight(annotatedBody)((i, acc) => Lam(i, acc)))
                        )(isDecl, isVirtual, isMut, N, N, genField, annotations).withLoc(S(l0 ++ annotatedBody.toLoc)))
                  }
                case c =>
                  asc match {
                    case S(ty) =>
                      if (transformBody.nonEmpty) die // TODO
                      R(NuFunDef(isLetRec, v, opStr, tparams, R(PolyType(Nil, ps.foldRight(ty)((p, r) => Function(p.toType match {
                        case L(diag) => raise(diag); Top // TODO better
                        case R(tp) => tp
                      }, r)))))(isDecl, isVirtual, isMut, N, N, genField, annotations).withLoc(S(l0 ++ ty.toLoc)))
                      // TODO rm PolyType after FCP is merged
                    case N =>
                      // TODO dedup:
                      val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
                      err((
                        msg"Expected ':' or '=' followed by a function body or signature; found ${tkstr} instead" -> loc :: Nil))
                      consume
                      val bod = errExpr
                      R(NuFunDef(
                          isLetRec, v, opStr, Nil, L(ps.foldRight(bod: Term)((i, acc) => Lam(i, acc)))
                        )(isDecl, isVirtual, isMut, N, N, genField, annotations).withLoc(S(l0 ++ bod.toLoc)))
                  }
              }
            }
          case _ =>
            exprOrIf(0, allowSpace = false, annotations = annotations)
        }
        val finalTerm = yeetSpaces match {
          case (KEYWORD("="), l0) :: _ => t match {
            case R(v: Var) =>
              consume
              R(Eqn(v, expr(0)))
            case R(App(v: Var, args)) =>
              consume
              R(Eqn(v, Lam(args, expr(0))))
            case _ => t
          }
          case _ => t
        }
              
        yeetSpaces match {
          case (SEMI, _) :: _ => consume; finalTerm :: block
          case (NEWLINE, _) :: _ => consume; finalTerm :: block
          case _ => finalTerm :: Nil
        }
    }
  }

  private def parseAnnotations(allowNewLines: Bool): Ls[Term] = {
    @tailrec
    def rec(acc: Ls[Term]): Ls[Term] = cur match {
      case (SPACE, _) :: c => 
        consume
        rec(acc)
      case (NEWLINE, _) :: c if allowNewLines =>
        consume
        rec(acc)
      case (IDENT("@", true), l0) :: c => {
        consume
        val (name, loc) = c match {
          case (IDENT(nme, false), l1) :: next => (nme, l1)
          case c =>
            val (tkstr, loc) = c.headOption.fold(("end of input", lastLoc))(_.mapFirst(_.describe).mapSecond(some))
            err((msg"Expected an identifier; found ${tkstr} instead" -> loc :: Nil))
            ("<error>", l0)
        }
        consume

        val annotation = Var(name).withLoc(S(loc))
        rec(annotation :: acc)
      }
      case _ => acc.reverse
    }
    rec(Nil)
  }
  
  private def yeetSpaces: Ls[TokLoc] =
    cur.dropWhile(tkloc =>
      (tkloc._1 === SPACE
      || tkloc._1.isInstanceOf[COMMENT] // TODO properly retrieve and sotre all comments in AST?
      ) && { consume; true })
  
  final def funParams(implicit et: ExpectThen, fe: FoundErr, l: Line): Ls[Tup] = wrap(()) { l =>
    yeetSpaces match {
      case (KEYWORD("=" | ":"), _) :: _ => Nil
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
      case Nil => Nil
    }
  }
  
  private def unexpectedThenElse(loc: Opt[Loc]) = {
    err(msg"Expected an expression; found a 'then'/'else' clause instead" -> loc :: Nil)
    errExpr
  }

  private def unsupportedQuote(loc: Opt[Loc]) = {
    err(msg"This quote syntax is not supported yet" -> loc :: Nil)
    errExpr
  }
  
  final def expr(prec: Int, allowSpace: Bool = true)(implicit fe: FoundErr, l: Line): Term = wrap(prec,allowSpace) { l =>
    exprOrIf(prec, allowSpace)(et = false, fe = fe, l = implicitly) match {
      case R(e) => e
      case L(e) => unexpectedThenElse(e.toLoc)
    }
  }
  
  def exprOrBlockContinuation(implicit et: ExpectThen, fe: FoundErr, l: Line): Term =
    yeetSpaces match {
      case (NEWLINE, l0) :: _ =>
        consume
        val stmts = block
        val es = stmts.map { case L(t) => unexpectedThenElse(t.toLoc); case R(e) => e }
        Blk(es)
      case _ => expr(0)
    }
  
  private def warnDbg(msg: Any, loco: Opt[Loc] = curLoc): Unit =
    raise(WarningReport(msg"[${cur.headOption.map(_._1).mkString}] ${""+msg}" -> loco :: Nil,
      newDefs = true))
  
  private def letBindings(genQuote: Bool)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = {
    val bs = bindings(Nil)
    val body =
      if (genQuote) yeetSpaces match {
        case (QUOTE, l1) :: (KEYWORD("in"), l2) :: _ =>
          consume
          consume
          exprOrIf(0)(et, fe, implicitly)
        case (NEWLINE, _) :: _ =>
          consume
          val stmts = block
          val es = stmts.map { case L(t) => unexpectedThenElse(t.toLoc); case R(e) => e }
          R(Blk(es))
        case (tk, loc) :: _ =>
          err(msg"Expected '`in'; found ${tk.describe} instead" -> S(loc) :: Nil)
          R(errExpr)
        case Nil =>
          err(msg"Expected '`in'; found end of input instead" -> lastLoc :: Nil)
          R(errExpr)
      }
      else yeetSpaces match {
        case (KEYWORD("in") | SEMI, _) :: _ =>
          consume
          exprOrIf(0)(et, fe, implicitly)
        case (NEWLINE, _) :: _ =>
          consume
          exprOrIf(0)(et, fe, implicitly)
        case _ =>
          R(UnitLit(true).withLoc(curLoc.map(_.left)))
      }
    bs.foldRight(body) {
      case ((v, r), R(acc)) if genQuote => R(Quoted(Let(false, v, Unquoted(r), Unquoted(acc))))
      case ((v, r), R(acc)) => R(Let(false, v, r, acc))
      case ((v, r), L(acc)) if genQuote => R(unsupportedQuote(acc.toLoc))
      case ((v, r), L(acc)) => L(IfLet(false, v, r, acc))
    }
  }

  final def exprOrIf(prec: Int, allowSpace: Bool = true, annotations: Ls[Term] = Nil)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(prec, allowSpace) { l =>
    val moreAnnotations: Ls[Term] = parseAnnotations(false)

    if (moreAnnotations.nonEmpty) {
      yeetSpaces
    }

    val allAnns = annotations ++ moreAnnotations
    
    val res = cur match {
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
      case (QUOTE, loc) :: _ =>
        consume
        cur match {
          case (IDENT(nme, false), l0) :: _ =>
            consume
            exprCont(Quoted(Var(nme)).withLoc(S(loc ++ l0)), prec, allowNewlines = false)
          case (LITVAL(lit), l0) :: _ =>
            consume
            exprCont(Quoted(lit.withLoc(S(l0))).withLoc(S(loc ++ l0)), prec, allowNewlines = false)
          case (KEYWORD("let"), l0) :: _ =>
            consume
            letBindings(true) match {
              case R(bd) => R(bd.withLoc(S(loc ++ bd.toLoc)))
              case _ => R(unsupportedQuote(S(l0)))
            }
          case (KEYWORD("if"), l0) :: _ =>
            val term = exprOrIf(prec, allowSpace)
            term match {
              case R(it @ If(IfThen(cond, body), els)) =>
                R(Quoted(If(IfThen(Unquoted(cond), Unquoted(body)), els.map(els => Unquoted(els)))).withLoc(S(loc ++ it.toLoc)))
              case _ => R(unsupportedQuote(S(l0)))
            }
          case (br @ BRACKETS(bk @ Round, toks), loc) :: _ =>
            consume
            val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()) match {
              case (N, Fld(FldFlags(false, false, _), elt)) :: Nil => Quoted(Bra(false, elt)).withLoc(S(loc ++ elt.toLoc))
              case _ => unsupportedQuote(S(loc))
            }
            exprCont(res, prec, allowNewlines = false)
          case _ => R(unsupportedQuote(S(loc)))
        }
      case (LITVAL(lit), l0) :: _ =>
        consume
        exprCont(lit.withLoc(S(l0)), prec, allowNewlines = false)
      case (KEYWORD(kwStr @ ("undefined" | "null")), l0) :: _ =>
        consume
        exprCont(UnitLit(kwStr === "undefined").withLoc(S(l0)), prec, allowNewlines = false)
      case (IDENT(nme, false), l0) :: _ =>
        consume
        exprCont(Var(nme).withLoc(S(l0)), prec, allowNewlines = false)
      case (br @ BRACKETS(Quasiquote | QuasiquoteTriple, toks), loc) :: _ =>
        consume
        val body = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.expr(0))
        exprCont(Quoted(body).withLoc(S(loc)), prec, allowNewlines = false)
      case (br @ BRACKETS(Unquote, toks), loc) :: _ =>
        consume 
        val body = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.expr(0))
        exprCont(Unquoted(body).withLoc(S(loc)), prec, allowNewlines = false)
      case (KEYWORD("super"), l0) :: _ =>
        consume
        exprCont(Super().withLoc(S(l0)), prec, allowNewlines = false)
      case (IDENT("~", _), l0) :: _ =>
        consume
        val rest = expr(prec, allowSpace = true)
        exprCont(App(Var("~").withLoc(S(l0)), rest).withLoc(S(l0 ++ rest.toLoc)), prec, allowNewlines = false)
      case (BRACKETS(Round, (IDENT(opStr, true), l1) :: Nil), l0) :: _ =>
        consume
        exprCont(Var(opStr).withLoc(S(l1)), prec, allowNewlines = false)
      case (br @ BRACKETS(bk @ (Round | Square | Curly), toks), loc) :: _ =>
        consume
        val res = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        val bra = (bk, res) match {
          case (Curly, _) =>
            Bra(true, Rcd(res.map {
              case S(n) -> fld => n -> fld
              case N -> (fld @ Fld(_, v: Var)) => v -> fld
              case N -> fld =>
                err((
                  msg"Record field should have a name" -> fld.value.toLoc :: Nil))
                Var("<error>") -> fld
            }))
          case (Round, (N, Fld(FldFlags(false, false, _), elt)) :: Nil) =>
            Bra(false, elt)
          case (Round, _) =>
            yeetSpaces match {
              case (KEYWORD(opStr @ "=>"), l1) :: (NEWLINE, l2) :: _ /* if opPrec(opStr)._1 > prec */ =>
                consume
                val rhs = Blk(typingUnit.entities)
                Lam(Tup(res), rhs)
              case (KEYWORD("=>"), l1) :: _ =>
                consume
                val e = expr(NewParser.opPrec("=>")._2)
                Lam(Tup(res), e)
              case (QUOTE, l0) :: (KEYWORD("=>"), l1) :: _ =>
                exprCont(Tup(res), 0, true) match {
                  case L(t) => unsupportedQuote(t.toLoc)
                  case R(t) => t
                }
              case (IDENT("->", true), l1) :: _ =>
                consume
                val rhs = expr(opPrec("->")._2)
                Lam(Tup(res), rhs)
              case _ =>
                res match {
                  case Nil =>
                    UnitLit(true)
                  case _ =>
                    res.map {
                      case N -> Fld(FldFlags.empty, t) => t
                      case no -> Fld(_, t) =>
                        err((msg"Illegal position for field specification" -> Loc(no.toList :+ t) :: Nil))
                        t
                    }.reduceRight((t, acc) =>
                      App(Var(",").withLoc(Loc(t :: acc :: Nil)), PlainTup(t, acc)))
                }
            }
          case _ =>
            Tup(res)
        }
        exprCont(bra.withLoc(S(loc)), prec, allowNewlines = false)
      case (KEYWORD("forall"), l0) :: _ =>
        consume
        def getIdents: Ls[TypeVar] = yeetSpaces match {
          case (IDENT(nme, false), l0) :: _ =>
            consume
            val res = TypeVar(R(nme), N).withLoc(S(l0))
            yeetSpaces match {
              case (COMMA, _) :: _ =>
                consume
                res :: getIdents
              case _ => res :: Nil
            }
          case _ => Nil
        }
        val idents = getIdents
        val rest = cur match {
          case (KEYWORD(":"), l0) :: _ =>
            consume
            expr(0)
          case _ =>
            err((msg"Expected `:` after `forall` section" -> curLoc.orElse(lastLoc) :: Nil))
            errExpr
        }
        R(Forall(idents, rest))
      case (KEYWORD("while"), l0) :: _ =>
        consume
        val cond = expr(0)
        val (success, _) = skip(KEYWORD("do")) // TODO kw?
        val body = expr(0)
        exprCont(While(cond, body).withLoc(S(l0 ++ body.toLoc)), prec, allowNewlines = false)
      case (KEYWORD("set"), l0) :: _ =>
        consume
        val lhs = expr(0)
        val (success, _) = skip(KEYWORD("=")) // TODO kw?
        val rhs = expr(0)(fe = foundErr || !success, l = implicitly)
        exprCont(Assign(lhs, rhs).withLoc(S(l0 ++ rhs.toLoc)), prec, allowNewlines = false)
      case (KEYWORD("let"), l0) :: _ =>
        consume
        letBindings(false)
      case (KEYWORD("new"), l0) :: c =>
        consume
        val body = expr(NewParser.prec('.'))
        exprCont(NuNew(body).withLoc(S(l0 ++ body.toLoc)), prec, allowNewlines = false)
      case (KEYWORD("else"), l0) :: _ =>
        consume
        yeetSpaces match {
          case (NEWLINE, l0) :: _ =>
            consume
            ??? // TODO
          case _ =>
            val e = expr(0)
            L(IfElse(e).withLoc(S(l0 ++ e.toLoc)))
        }
      case (KEYWORD("case"), l0) :: _ =>
        consume
        exprOrIf(0)(et = true, fe = fe, l = implicitly) match {
          case L(body) =>
            R(Lam(PlainTup(Var("case$scrut")), If(IfOpApp(Var("case$scrut"), Var("is"), body), N)))
          case R(rhs) =>
            err((msg"Expected 'then'/'else' clause after 'case'; found ${rhs.describe} instead" -> rhs.toLoc ::
              msg"Note: 'case' expression starts here:" -> S(l0) :: Nil))
            R(Lam(PlainTup(Var("case$scrut")), If(IfElse(rhs), N)))
        }
        
      case (KEYWORD("if"), l0) :: _ =>
        consume
        exprOrIf(0)(et = true, fe = fe, l = implicitly) match {
          case L(body) =>
            val els = yeetSpaces match {
              case (KEYWORD("else"), _) :: _ =>
                consume
                S(exprOrBlockContinuation)
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
                    nested.concludeWith(_ => ())
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
                err((msg"Expected 'then'/'else' clause after 'if'; found $found instead" -> loc ::
                  msg"Note: 'if' expression starts here:" -> S(l0) :: Nil))
                R(If(IfThen(e, errExpr), N))
            }
        }
        
      case Nil =>
        err(msg"Unexpected end of $description; an expression was expected here" -> lastLoc :: Nil)
        R(errExpr)
      case ((SEMI /* | NEWLINE */ /* | BRACKETS(Curly, _) */, l0) :: _) =>
        R(UnitLit(true).withLoc(S(l0)))
        // R(errExpr) // TODO
      case (IDENT("-", true), l0) :: _ /*if opPrec("-")._1 > prec*/ => // Unary minus
        consume
        val v = Var("-").withLoc(S(l0))
        expr(opPrec("-")._2) match {
          case IntLit(i) => // Special case for negative literals
            exprCont(IntLit(-i), prec, false)
          case rhs: Term => // General case
            exprCont(
              if (newDefs) App(v, PlainTup(IntLit(BigInt(0)), rhs))
              else App(App(v, PlainTup(IntLit(BigInt(0)))), PlainTup(rhs))
            , prec, false)
        }
      case (tk, l0) :: _ =>
        err(msg"Unexpected ${tk.describe} in expression position" -> S(l0) :: Nil)
        consume
        exprOrIf(prec)(et = et, fe = true, l = implicitly)
    }
    
    if (allAnns.isEmpty) res
    else res match {
      case Left(body) => body match {
        case IfThen(expr, rhs) =>
          Left(IfThen(wrapAnns(expr, allAnns), rhs))
        case _ =>
          err(msg"Unexpected annotation" -> allAnns.head.toLoc :: Nil)
          L(body) // discard annotations for now
      }

      case Right(term) => R(wrapAnns(term, allAnns))
    }
  }

  private def wrapAnns(trm: Term, anns: List[Term]) =
    anns.foldRight(trm)(Ann(_, _))
  
  private def errExpr =
    // Tup(Nil).withLoc(lastLoc) // TODO FIXME produce error term instead
    UnitLit(true).withLoc(lastLoc) // TODO FIXME produce error term instead
  
  final def exprCont(acc: Term, prec: Int, allowNewlines: Bool)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(prec, s"`$acc`", allowNewlines) { l =>
    cur match {
      case (QUOTE, l) :: _ => cur match {
        case _ :: (KEYWORD(opStr @ "=>"), l0) :: _ if opPrec(opStr)._1 > prec =>
          consume
          consume
          exprCont(Quoted(Lam(acc match {
            case t: Tup => t
            case _ => PlainTup(acc)
          }, Unquoted(expr(1)(fe, implicitly)))), prec, allowNewlines)
        case _ :: (br @ BRACKETS(Round, toks), loc) :: _ =>
          consume
          consume
          val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented()).map {
            case nme -> Fld(flgs, t) => nme -> Fld(flgs, Unquoted(t))
          }
          val res = App(Unquoted(acc), Tup(as).withLoc(S(loc)))
          exprCont(Quoted(res), prec, allowNewlines)
        case _ :: (IDENT(opStr, true), l0) :: _ =>
          if (opPrec(opStr)._1 > prec) {
            consume
            consume
            val v = Var(opStr).withLoc(S(l0))
            yeetSpaces match {
              case (NEWLINE, l0) :: _ => consume
              case _ =>
            }
            exprOrIf(opPrec(opStr)._2) match {
              case L(rhs) => R(unsupportedQuote(S(l0)))
              case R(rhs) => exprCont(opStr match {
                case "with" => unsupportedQuote(S(l0))
                case _ => Quoted(App(v, PlainTup(Unquoted(acc), Unquoted(rhs))))
              }, prec, allowNewlines)
            }
          }
          else R(acc)
        case _ :: (KEYWORD("in"), _) :: _ =>
          R(acc)
        case _ =>
          consume
          unsupportedQuote(acc.toLoc)
          R(acc)
      }
      case (COMMA, l0) :: _ if prec === 0 =>
        consume
        yeetSpaces match {
          case (NEWLINE, _) :: _ => consume
          case _ =>
        }
        val rhs = expr(prec) // TODO support exprOrIf for comma operators
        R(App(Var(",").withLoc(S(l0)), PlainTup(acc, rhs)))
      case (KEYWORD(opStr @ "=>"), l0) :: (NEWLINE, l1) :: _ if opPrec(opStr)._1 > prec =>
        consume
        val rhs = Blk(typingUnit.entities)
        R(Lam(PlainTup(acc), rhs))
      case (KEYWORD(opStr @ "=>"), l0) :: _ if opPrec(opStr)._1 > prec =>
        consume
        val rhs = expr(1)
        val res = Lam(PlainTup(acc), rhs)
        exprCont(res, prec, allowNewlines)
      case (IDENT(".", _), l0) :: (br @ BRACKETS(Square, toks), l1) :: _ =>
        consume
        consume
        val idx = rec(toks, S(br.innerLoc), br.describe)
          .concludeWith(_.expr(0, allowSpace = true))
        val newAcc = Subs(acc, idx).withLoc(S(l0 ++ l1 ++ idx.toLoc))
        exprCont(newAcc, prec, allowNewlines)
      case (IDENT(opStr, true), l0) :: _ if /* isInfix(opStr) && */ opPrec(opStr)._1 > prec =>
        consume
        val v = Var(opStr).withLoc(S(l0))
        yeetSpaces match {
          case (NEWLINE, l0) :: _ => consume
          case _ =>
        }
        exprOrIf(opPrec(opStr)._2) match {
          case L(rhs) =>
            L(IfOpApp(acc, v, rhs))
          case R(rhs) =>
            exprCont(opStr match {
              case "with" =>
                rhs match {
                  case rhs: Rcd =>
                    With(acc, rhs)//.withLocOf(term)
                  case Bra(true, rhs: Rcd) =>
                    With(acc, rhs)//.withLocOf(term)
                  case _ =>
                    err(msg"record literal expected here; found ${rhs.describe}" -> rhs.toLoc :: Nil)
                    acc
                }
              case _ =>
                if (newDefs) App(v, PlainTup(acc, rhs))
                else App(App(v, PlainTup(acc)), PlainTup(rhs))
            }, prec, allowNewlines)
        }
      case (KEYWORD(":"), l0) :: _ if prec <= NewParser.prec(':') =>
        consume
        R(Asc(acc, typ(0)))
      case (KEYWORD("where"), l0) :: _ if prec <= 1 =>
        consume
        val tu = typingUnitMaybeIndented
        val res = Where(acc, tu.entities).withLoc(S(l0))
        exprCont(res, prec, allowNewlines = false)
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
      case (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
      // case (KEYWORD("then"), _) :: _ if /* expectThen && */ prec <= 1 =>
        consume
        L(IfThen(acc, exprOrBlockContinuation))
      case (NEWLINE, _) :: (KEYWORD("then"), _) :: _ if /* expectThen && */ prec === 0 =>
        consume
        consume
        L(IfThen(acc, exprOrBlockContinuation))
      case (NEWLINE, _) :: _ if allowNewlines =>
        consume
        exprCont(acc, 0, allowNewlines)
        
      case (br @ BRACKETS(Curly, toks), loc) :: _ if prec <= AppPrec =>
        consume
        val tu = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.typingUnitMaybeIndented).withLoc(S(loc))
        exprCont(Rft(acc, tu), prec, allowNewlines)
        
      case (COMMA | SEMI | NEWLINE | KEYWORD("then" | "else" | "in" | "=" | "do")
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
        
      case (br @ BRACKETS(Angle | Square, toks), loc) :: _ =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        // val res = TyApp(acc, as.map(_.mapSecond.to))
        val res = TyApp(acc, as.map {
          case (N, Fld(FldFlags(false, false, _), trm)) => trm.toType match {
            case L(d) => raise(d); Top // TODO better
            case R(ty) => ty
          }
          case _ => ???
        }).withLoc(acc.toLoc.fold(some(loc))(_ ++ loc |> some))
        exprCont(res, prec, allowNewlines)
        
      /*case (br @ BRACKETS(Square, toks), loc) :: _ => // * Currently unreachable because we match Square brackets as tparams
        consume
        val idx = rec(toks, S(br.innerLoc), "subscript").concludeWith(_.expr(0))
        val res = Subs(acc, idx.withLoc(S(loc)))
        exprCont(res, prec, allowNewlines)*/
      
      case (br @ BRACKETS(Round, toks), loc) :: _ if prec <= AppPrec =>
        consume
        val as = rec(toks, S(br.innerLoc), br.describe).concludeWith(_.argsMaybeIndented())
        val res = App(acc, Tup(as).withLoc(S(loc)))
        exprCont(res, prec, allowNewlines)
        
      case (KEYWORD("of"), _) :: _ =>
        consume
        val as = argsMaybeIndented()
        // val as = argsOrIf(Nil) // TODO
        val res = App(acc, Tup(as))
        exprCont(res, prec, allowNewlines)
        
      case c @ (h :: _) if (h._1 match {
        case KEYWORD(":" | "of" | "where" | "extends") | SEMI | BRACKETS(Round | Square, _)
          | BRACKETS(Indent, (
              KEYWORD("of") | SEMI
              | BRACKETS(Round | Square, _)
              | SELECT(_)
            , _) :: _)
          => false
        case _ => true
      }) =>
        val as = argsMaybeIndented()
        val res = App(acc, Tup(as))
        raise(WarningReport(msg"Paren-less applications should use the 'of' keyword"
          -> res.toLoc :: Nil, newDefs = true))
        exprCont(res, prec, allowNewlines)
        
      case _ => R(acc)
    }
  }
  
  final def opBlock(acc: Term, opStr: Str, opLoc: Loc)(implicit et: ExpectThen, fe: FoundErr, l: Line): IfBody \/ Term = wrap(s"`$acc`", opStr) { l =>
      val opv = Var(opStr).withLoc(S(opLoc))
      val rhs = exprOrIf(0)
      // val rhs = exprOrIf(1)
      rhs match {
        case R(rhs) =>
          val res = App(opv, PlainTup(acc, rhs))
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
          val (opsRhss, els) = opIfBlock(opv -> rhs :: Nil)
          val opsApp = IfOpsApp(acc, opsRhss)
          L(els.fold[IfBody](opsApp)(trm => IfBlock(L(opsApp) :: L(IfElse(trm)) :: Nil)))
      }
  }
  final def opIfBlock(acc: Ls[Var -> IfBody])(implicit et: ExpectThen, fe: FoundErr): (Ls[Var -> IfBody], Opt[Term]) = wrap(acc) { l =>
      cur match {
        case (NEWLINE, _) :: c => // TODO allow let bindings...
          consume
          c match {
            case (IDENT("_", false), wcLoc) :: _ =>
              exprOrIf(0) match {
                case R(rhs) =>
                  err(msg"expect an operator branch" -> S(wcLoc) :: Nil)
                  (acc.reverse, N)
                case L(IfThen(_, els)) => (acc.reverse, S(els))
                case L(rhs) =>
                  err(msg"expect 'then' after the wildcard" -> rhs.toLoc :: Nil)
                  (acc.reverse, N)
              }
            case (IDENT(opStr2, true), opLoc2) :: _ =>
              consume
              val rhs = exprOrIf(0)
              // val rhs = exprOrIf(1)
              rhs match {
                case R(rhs) => ???
                case L(rhs) =>
                  opIfBlock(Var(opStr2).withLoc(S(opLoc2)) -> rhs :: acc)
              }
            case (KEYWORD("else"), elseLoc) :: tail =>
              consume
              exprOrIf(0) match {
                case R(rhs) => (acc.reverse, S(rhs))
                case L(rhs) =>
                  err(msg"expect a term" -> rhs.toLoc :: Nil)
                  (acc.reverse, N)
              }
            case (_, headLoc) :: _ =>
              // printDbg(c)
              err(msg"expect an operator" -> S(headLoc) :: Nil)
              (acc.reverse, N)
            case Nil =>
              (acc.reverse, N)
          }
        case _ =>
          (acc.reverse, N)
      }
  }
  
  final def tyArgs(implicit fe: FoundErr, et: ExpectThen): Opt[Ls[Type]] =
    cur match {
      case (IDENT("<", true), l0) :: _ => ???
      case _ => ???
    }
  
  // TODO support line-broken param lists; share logic with args/argsOrIf
  def typeParams(implicit fe: FoundErr, et: ExpectThen): Ls[(Opt[VarianceInfo], TypeName)] = {
    val vinfo = yeetSpaces match {
      case (KEYWORD("in"), l0) :: (KEYWORD("out"), l1) :: _ =>
        consume
        S(VarianceInfo.in, l0 ++ l1)
      case (KEYWORD("in"), l0) :: _ =>
        consume
        S(VarianceInfo.contra, l0)
      case (KEYWORD("out"), l0) :: _ =>
        consume
        S(VarianceInfo.co, l0)
      case _ => N
    }
    yeetSpaces match {
      case (IDENT(nme, false), l0) :: _ =>
        consume
        val tyNme = TypeName(nme).withLoc(S(l0))
        yeetSpaces match {
          case (COMMA, l0) :: _ =>
            consume
            vinfo.map(_._1) -> tyNme :: typeParams
          case _ =>
            vinfo.map(_._1) -> tyNme :: Nil
        }
      case _ =>
        vinfo match {
          case S((_, loc)) =>
            err(msg"dangling variance information" -> S(loc) :: Nil)
          case N =>
        }
        Nil
    }
  }
  
  
  final def maybeIndented[R](f: (NewParser, Bool) => R)(implicit fe: FoundErr, et: ExpectThen): R =
    cur match {
      case (br @ BRACKETS(Indent, toks), _) :: _ if (toks.headOption match {
        case S((KEYWORD("then" | "else"), _)) => false
        case _ => true
      }) =>
        consume
        rec(toks, S(br.innerLoc), br.describe).concludeWith(f(_, true))
      case _ => f(this, false)
    }
  
  final def argsMaybeIndented()(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> Fld] =
    maybeIndented(_.args(_))
  // final def argsMaybeIndented()(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> Fld] =
  //   cur match {
  //     case (br @ BRACKETS(Indent, toks), _) :: _ if (toks.headOption match {
  //       case S((KEYWORD("then" | "else"), _)) => false
  //       case _ => true
  //     }) =>
  //       consume
  //       rec(toks, S(br.innerLoc), br.describe).concludeWith(_.args(true))
  //     case _ => args(false)
  //   }
  
  // TODO support comma-less arg blocks...?
  final def args(allowNewlines: Bool, prec: Int = NoElsePrec)(implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> Fld] =
    // argsOrIf(Nil).map{case (_, L(x))=> ???; case (n, R(x))=>n->x} // TODO
    argsOrIf(Nil, Nil, allowNewlines, prec).flatMap{case (n, L(x))=> 
        err(msg"Unexpected 'then'/'else' clause" -> x.toLoc :: Nil)
        n->Fld(FldFlags.empty, errExpr)::Nil
      case (n, R(x))=>n->x::Nil} // TODO
  /* 
  final def argsOrIf2()(implicit fe: FoundErr, et: ExpectThen): IfBlock \/ Ls[Opt[Var] -> Fld] = {
    // argsOrIf(Nil).partitionMap(identity).mapFirst(ifbods => ???)
    argsOrIf(Nil) match {
      case n -> L(ib) =>
        
      case n -> R(tm) =>
      case Nil => R(Nil)
    }
  }
  */
  final def argsOrIf(acc: Ls[Opt[Var] -> (IfBody \/ Fld)], seqAcc: Ls[Statement], allowNewlines: Bool, prec: Int = NoElsePrec)
        (implicit fe: FoundErr, et: ExpectThen): Ls[Opt[Var] -> (IfBody \/ Fld)] =
      wrap(acc, seqAcc) { l =>
      
    val anns = parseAnnotations(false)
    
    cur match {
      case Nil =>
        seqAcc match {
          case res :: seqAcc => 
            (N -> R(Fld(FldFlags.empty, Blk((res :: seqAcc).reverse))) :: acc).reverse
          case Nil =>
            acc.reverse
        }
      case (SPACE, _) :: _ =>
        consume
        argsOrIf(acc, seqAcc, allowNewlines, prec)
      case (NEWLINE, _) :: _ => // TODO: | ...
        assert(seqAcc.isEmpty)
        acc.reverse
      case (IDENT(nme, true), _) :: _ if nme =/= "-" => // TODO: | ...
        assert(seqAcc.isEmpty)
        acc.reverse
      case _ =>
    
    // val blck = block
    
    val argVal = yeetSpaces match {
      case (KEYWORD("val"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argMut = yeetSpaces match {
      case (KEYWORD("mut"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argSpec = yeetSpaces match {
      case (KEYWORD("#"), l0) :: _ =>
        consume
        S(l0)
      case _ => N
    }
    val argName = yeetSpaces match {
      case (IDENT(idStr, false), l0) :: (KEYWORD(":"), _) :: _ => // TODO: | ...
        consume
        consume
        S(Var(idStr).withLoc(S(l0)))
      case (LITVAL(IntLit(i)), l0) :: (KEYWORD(":"), _) :: _ => // TODO: | ...
        consume
        consume
        S(Var(i.toString).withLoc(S(l0)))
      case _ => N
    }

    // val e = expr(NoElsePrec) -> argMut.isDefined
    val e = exprOrIf(prec, true, anns).map(Fld(FldFlags(argMut.isDefined, argSpec.isDefined, argVal.isDefined), _))
    
    def mkSeq = if (seqAcc.isEmpty) argName -> e else e match {
      case L(_) => ???
      case R(Fld(flags, res)) =>
        argName -> R(Fld(flags, Blk((res :: seqAcc).reverse)))
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
          case R(Fld(FldFlags(false, false, _), res)) =>
            argsOrIf(acc, res :: seqAcc, allowNewlines)
          case R(_) => ???
        }
      case _ =>
        (mkSeq :: acc).reverse
    }
    
  }
  }
  
  final def bindings(acc: Ls[Var -> Term])(implicit fe: FoundErr): Ls[Var -> Term] = 
    cur match {
      case (SPACE, _) :: _ =>
        consume
        bindings(acc)
      case (NEWLINE | IDENT(_, true) | SEMI, _) :: _ => // TODO: | ...
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
  
  final def mkType(trm: Term): Type = trm.toType match {
    case L(d) => raise(d); Top // TODO better
    case R(ty) => ty
  }
  
  
}

