package mlscript

import scala.annotation.tailrec
import utils._, shorthands._

import Message.MessageContext
import Diagnostic.{Lexing, Parsing}

import NewLexer._

class NewLexer(origin: Origin, raise: Diagnostic => Unit, dbg: Bool) {
  
  val bytes: Array[Char] = origin.fph.blockStr.toArray
  private val length = bytes.length
  type State = Int
  
  private val isOpChar = Set(
    '!', '#', '%', '&', '*', '+', '-', '/', ':', '<', '=', '>', '?', '@', '\\', '^', '|', '~' , '.',
    // ',', 
    ';'
  )
  def isIdentFirstChar(c: Char): Bool =
    c.isLetter || c === '_' || c === '\''
  def isIdentChar(c: Char): Bool =
    isIdentFirstChar(c) || isDigit(c) || c === '\''
  def isHexDigit(c: Char): Bool =
    isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
  def isOctDigit(c: Char): Bool =
    c >= '0' && c <= '7'
  def isBinDigit(c: Char): Bool =
    c === '0' || c === '1'
  def isDigit(c: Char): Bool =
    c >= '0' && c <= '9'
  
  /* // TODO remove (unused)
  private val isNonStickyKeywordChar = Set(
    ',',
    ':',
    ';',
  )
  */
  
  private val isSymKeyword = Set(
    // "->",
    "=>",
    "=",
    ":",
    ";;",
    "#",
    // ".",
    // "<",
    // ">",
  )
  
  private val isAlphaOp = alpahOp
  
  @tailrec final
  def takeWhile(i: Int, cur: Ls[Char] = Nil)(pred: Char => Bool): (Str, Int) =
    if (i < length && pred(bytes(i))) takeWhile(i + 1, bytes(i) :: cur)(pred)
    else (cur.reverseIterator.mkString, i)

  final def num(i: Int): (Lit, Int) = {
    def test(i: Int, p: Char => Bool): Bool = i < length && p(bytes(i))
    def zero: IntLit = IntLit(BigInt(0))
    /** Take a sequence of digits interleaved with underscores. */
    def takeDigits(i: Int, pred: Char => Bool): (Opt[Str], Int) = {
      @tailrec def rec(i: Int, acc: Ls[Char], firstSep: Bool, lastSep: Bool): (Str, Bool, Bool, Int) =
        if (i < length) {
          val c = bytes(i)
          if (pred(c)) rec(i + 1, c :: acc, firstSep, false)
          else if (c === '_') rec(i + 1, acc, acc.isEmpty, true)
          else (acc.reverseIterator.mkString, firstSep, lastSep, i)
        }
        else (acc.reverseIterator.mkString, firstSep, lastSep, i)
      val (str, firstSep, lastSep, j) = rec(i, Nil, false, false)
      if (firstSep)
        raise(WarningReport(
          msg"Leading separator is not allowed" -> S(loc(i - 1, i)) :: Nil,
          newDefs = true, source = Lexing))
      if (lastSep)
        raise(WarningReport(
          msg"Trailing separator is not allowed" -> S(loc(j - 1, j)) :: Nil,
          newDefs = true, source = Lexing))
      (if (str.isEmpty) N else S(str), j)
    }
    /** Take an integer and coverts to `BigInt`. Also checks if it is empty. */
    def integer(i: Int, radix: Int, desc: Str, pred: Char => Bool): (IntLit, Int) = {
      takeDigits(i, pred) match {
        case (N, j) =>
          raise(ErrorReport(msg"Expect at least one $desc digit" -> S(loc(i, i + 2)) :: Nil,
            newDefs = true, source = Lexing))
          (zero, j)
        case (S(str), j) => (IntLit(BigInt(str, radix)), j)
      }
    }
    def isDecimalStart(ch: Char) = ch === '.' || ch === 'e' || ch === 'E'
    /** Take a fraction part with an optional exponent part. Call at periods. */
    def decimal(i: Int, integral: Str): (DecLit, Int) = {
      val (fraction, j) = if (test(i, _ === '.')) {
        takeDigits(i + 1, isDigit) match {
          case (N, j) =>
            raise(ErrorReport(msg"Expect at least one digit after the decimal point" -> S(loc(i + 1, i + 2)) :: Nil,
              newDefs = true, source = Lexing))
            ("", j)
          case (S(digits), j) => ("." + digits, j)
        }
      } else ("", i)
      val (exponent, k) = if (test(j, ch => ch === 'e' || ch === 'E')) {
        val (sign, k) = if (test(j + 1, ch => ch === '+' || ch === '-')) {
          (bytes(j + 1), j + 2)
        } else {
          ('+', j + 1)
        }
        takeDigits(k, isDigit) match {
          case (N, l) =>
            raise(ErrorReport(msg"Expect at least one digit after the exponent sign" -> S(loc(l - 1, l)) :: Nil,
              newDefs = true, source = Lexing))
            ("", l)
          case (S(digits), l) => ("E" + sign + digits, l)
        }
      } else {
        ("", j)
      }
      (DecLit(BigDecimal(integral + fraction + exponent)), k)
    }
    if (i < length) {
      bytes(i) match {
        case '0' if i + 1 < length => bytes(i + 1) match {
          case 'x' => integer(i + 2, 16, "hexadecimal", isHexDigit)
          case 'o' => integer(i + 2, 8, "octal", isOctDigit)
          case 'b' => integer(i + 2, 2, "binary", isBinDigit)
          case '.' | 'E' | 'e' => decimal(i + 1, "0")
          case _ => integer(i, 10, "decimal", isDigit)
        }
        case '0' => (zero, i + 1)
        case _ => takeDigits(i, isDigit) match {
          case (N, j) =>
            raise(ErrorReport(msg"Expect a numeric literal" -> S(loc(i, i + 1)) :: Nil,
              newDefs = true, source = Lexing))
            (zero, i)
          case (S(integral), j) =>
            if (j < length && isDecimalStart(bytes(j))) decimal(j, integral)
            else (IntLit(BigInt(integral)), j)
        }
      }
    } else {
      raise(ErrorReport(msg"Expect a numeric literal instead of end of input" -> S(loc(i, i + 1)) :: Nil,
        newDefs = true, source = Lexing))
      (zero, i)
    }
  }

  @tailrec final
  def str(i: Int, escapeMode: Bool, cur: Ls[Char] = Nil): (Str, Int) =
    if (escapeMode)
      if (i < length)
        bytes(i) match {
          case '\\' => str(i + 1, false, '\\' :: cur)
          case '"' => str(i + 1, false, '"' :: cur)
          case 'n' => str(i + 1, false, '\n' :: cur)
          case 't' => str(i + 1, false, '\t' :: cur)
          case 'r' => str(i + 1, false, '\r' :: cur)
          case 'b' => str(i + 1, false, '\b' :: cur)
          case 'f' => str(i + 1, false, '\f' :: cur)
          case ch =>
            raise(WarningReport(msg"Found invalid escape character" -> S(loc(i, i + 1)) :: Nil,
              newDefs = true, source = Lexing))
            str(i + 1, false, ch :: cur)
        }
      else {
        raise(ErrorReport(msg"Expect an escape character" -> S(loc(i, i + 1)) :: Nil,
          newDefs = true, source = Lexing))
        (cur.reverseIterator.mkString, i)
      }
    else {
      if (i < length)
        bytes(i) match {
          case '\\' => str(i + 1, true, cur)
          case '"' | '\n' => (cur.reverseIterator.mkString, i)
          case ch => str(i + 1, false, ch :: cur)
        }
      else
        (cur.reverseIterator.mkString, i)
    }
  
  def loc(start: Int, end: Int): Loc = Loc(start, end, origin)
  
  @tailrec final
  def lex(i: Int, ind: Ls[Int], acc: Ls[TokLoc]): Ls[TokLoc] = if (i >= length) acc.reverse else {
    val c = bytes(i)
    def pe(msg: Message): Unit =
      // raise(ParseError(false, msg -> S(loc(i, i + 1)) :: Nil))
      raise(ErrorReport(msg -> S(loc(i, i + 1)) :: Nil, newDefs = true, source = Lexing))
    // @inline 
    // def go(j: Int, tok: Token) = lex(j, ind, (tok, loc(i, j)) :: acc)
    def next(j: Int, tok: Token) = (tok, loc(i, j)) :: acc
    def isIdentEscape(i: Int): Bool = i + 2 < length && bytes(i) === 'i' && bytes(i + 1) === 'd' && bytes(i + 2) === '"'
    def takeIdentFromEscape(i: Int, ctor: Str => Token) = {
      val (n, j) = takeWhile(i + 3)(_ != '"')
      if (j < length && bytes(j) === '"') (ctor(n), j + 1)
      else { pe(msg"unfinished identifier escape"); (ERROR, j + 1) }
    }

    c match {
      case ' ' =>
        val (_, j) = takeWhile(i)(_ === ' ')
        // go(j, SPACE)
        lex(j, ind, next(j, SPACE))
      case ',' =>
        val j = i + 1
        // go(j, COMMA)
        lex(j, ind, next(j, COMMA))
      case '"' =>
        val j = i + 1
        val (chars, k) = str(j, false)
        val k2 = if (bytes.lift(k) === Some('"')) k + 1 else {
          pe(msg"unclosed quotation mark")
          k
        }
        // go(k2, LITVAL(StrLit(chars)))
        lex(k2, ind, next(k2, LITVAL(StrLit(chars))))
      case '/' if bytes.lift(i + 1).contains('/') =>
        val j = i + 2
        val (txt, k) =
          takeWhile(j)(c => c =/= '\n')
        // go(k, COMMENT(txt))
        lex(k, ind, next(k, COMMENT(txt)))
      case '/' if bytes.lift(i + 1).contains('*') => // multiple-line comment
        val j = i + 2
        var prev1 = '/'; var prev2 = '*'
        val (txt, k) =
          takeWhile(j)(c => {
            val res = prev1 =/= '*' || prev2 =/= '/'
            prev1 = prev2; prev2 = c
            res
          })
        // go(k, COMMENT(txt.dropRight(2)))
        lex(k, ind, next(k, COMMENT(txt.dropRight(2))))
      // case BracketKind(Left(k)) => go(i + 1, OPEN_BRACKET(k))
      // case BracketKind(Right(k)) => go(i + 1, CLOSE_BRACKET(k))
      case BracketKind(Left(k)) => lex(i + 1, ind, next(i + 1, OPEN_BRACKET(k)))
      case BracketKind(Right(k)) => lex(i + 1, ind, next(i + 1, CLOSE_BRACKET(k)))
      case '\n' =>
        val j = i + 1
        val (space, k) =
          takeWhile(j)(c => c === ' ' || c === '\n')
        val nextInd = space.reverseIterator.takeWhile(_ =/= '\n').size
        if (ind.headOption.forall(_ < nextInd) && nextInd > 0)
          lex(k, nextInd :: ind, (INDENT, loc(j, k)) :: acc)
        else {
          val newIndBase = ind.dropWhile(_ > nextInd)
          val droppedNum = ind.size - newIndBase.size
          val hasNewIndent = newIndBase.headOption.forall(_ < nextInd) && nextInd > 0
          val newInd = if (hasNewIndent) nextInd :: newIndBase else newIndBase
          if (dbg) {
            println("dbg: " + bytes.drop(i).take(10).map(escapeChar).mkString+"...")
            println((ind, nextInd, newIndBase, droppedNum, hasNewIndent, newInd))
          }
          lex(k, newInd,
            if (droppedNum > 0) {
              if (hasNewIndent) (INDENT, loc(j, k))
              else (NEWLINE, loc(i, k))
            } :: List.fill(droppedNum)((DEINDENT, loc(j-1, k))) ::: acc
            else (NEWLINE, loc(i, k)) :: acc
          )
        }
      case _ if isIdentEscape(i) =>
        val (tok, n) = takeIdentFromEscape(i, s => IDENT(s, false))
        lex(n, ind, next(n, tok))
      case _ if isIdentFirstChar(c) =>
        val (n, j) = takeWhile(i)(isIdentChar)
        // go(j, if (keywords.contains(n)) KEYWORD(n) else IDENT(n, isAlphaOp(n)))
        lex(j, ind, next(j, if (keywords.contains(n)) KEYWORD(n) else IDENT(n, isAlphaOp(n))))
      case _ if isOpChar(c) =>
        val (n, j) = takeWhile(i)(isOpChar)
        if (n === "." && j < length) {
          val nc = bytes(j)
          if (isIdentFirstChar(bytes(j)) && isIdentEscape(j)) {
            val (body, m) = takeIdentFromEscape(j, SELECT)
            lex(m, ind, next(m, body))
          }
          else if (isIdentFirstChar(nc)) {
            val (name, k) = takeWhile(j)(isIdentChar)
            // go(k, SELECT(name))
            lex(k, ind, next(k, SELECT(name)))
          }
          else if (
            // The first character is '0' and the next character is not a digit
            (nc === '0' && !(j + 1 < length && isDigit(bytes(j + 1)))) ||
            ('0' < nc && nc <= '9') // The first character is a digit other than '0'
          ) {
            val (name, k) = takeWhile(j)(isDigit)
            // go(k, SELECT(name))
            lex(k, ind, next(k, SELECT(name)))
          }
          else lex(j, ind, next(j, if (isSymKeyword.contains(n)) KEYWORD(n) else IDENT(n, true)))
        }
        // else go(j, if (isSymKeyword.contains(n)) KEYWORD(n) else IDENT(n, true))
        else lex(j, ind, next(j, if (isSymKeyword.contains(n)) KEYWORD(n) else IDENT(n, true)))
      case _ if isDigit(c) =>
        val (lit, j) = num(i)
        // go(j, LITVAL(IntLit(BigInt(str))))
        lex(j, ind, next(j, LITVAL(lit)))
      case _ =>
        pe(msg"unexpected character '${escapeChar(c)}'")
        // go(i + 1, ERROR)
        lex(i + 1, ind, next(i + 1, ERROR))
    }
  }
 
  def escapeChar(ch: Char): String = ch match {
    case '\b' => "\\b"
    case '\t' => "\\t"
    case '\n' => "\\n"
    case '\f' => "\\f"
    case '\r' => "\\r"
    case '"'  => "\\\""
    case '\'' => "\\\'"
    case '\\' => "\\\\"
    case _    => if (ch.isControl) "\\0" + Integer.toOctalString(ch.toInt) 
                else              String.valueOf(ch)
  }
  
  
  lazy val tokens: Ls[Token -> Loc] = lex(0, Nil, Nil)
  
  /** Converts the lexed tokens into structured tokens. */
  lazy val bracketedTokens: Ls[Stroken -> Loc] = {
    import BracketKind._
    def go(toks: Ls[Token -> Loc], canStartAngles: Bool, stack: Ls[BracketKind -> Loc -> Ls[Stroken -> Loc]], acc: Ls[Stroken -> Loc]): Ls[Stroken -> Loc] =
      toks match {
        case (OPEN_BRACKET(k), l0) :: rest =>
          go(rest, false, k -> l0 -> acc :: stack, Nil)
        case (CLOSE_BRACKET(k1), l1) :: rest =>
          stack match {
            case ((Indent, loc), oldAcc) :: _ if k1 =/= Indent =>
              go(CLOSE_BRACKET(Indent) -> l1.left :: toks, false, stack, acc)
            case ((Indent, loc), oldAcc) :: stack
            if k1 === Indent && acc.forall { case (SPACE | NEWLINE, _) => true; case _ => false } =>
              // * Ignore empty indented blocks:
              go(rest, false, stack, oldAcc)
            case ((k0, l0), oldAcc) :: stack =>
              if (k0 =/= k1)
                raise(ErrorReport(msg"Mistmatched closing ${k1.name}" -> S(l1) ::
                  msg"does not correspond to opening ${k0.name}" -> S(l0) :: Nil, newDefs = true,
                  source = Parsing))
              go(rest, true, stack, BRACKETS(k0, acc.reverse)(l0.right ++ l1.left) -> (l0 ++ l1) :: oldAcc)
            case Nil =>
              raise(ErrorReport(msg"Unexpected closing ${k1.name}" -> S(l1) :: Nil,
                newDefs = true, source = Parsing))
              go(rest, false, stack, acc)
          }
        case (INDENT, loc) :: rest =>
          go(OPEN_BRACKET(Indent) -> loc :: rest, false, stack, acc)
        case (DEINDENT, loc) :: rest =>
          go(CLOSE_BRACKET(Indent) -> loc :: rest, false, stack, acc)
        case (IDENT("<", true), loc) :: rest if canStartAngles =>
          go(OPEN_BRACKET(Angle) -> loc :: rest, false, stack, acc)
        case (IDENT(">", true), loc) :: rest if canStartAngles && (stack match {
          case ((Angle, _), _) :: _ => true
          case _ => false
        }) =>
          go(CLOSE_BRACKET(Angle) -> loc :: rest, false, stack, acc)
        case (IDENT(id, true), loc) :: rest
        if (canStartAngles && id.forall(_ == '>') && id.length > 1 && (stack match {
          case ((Angle, _), _) :: _ => true
          case _ => false
        })) => // split  `>>` to `>` and `>` so that code like `A<B<C>>` can be parsed correctly
          go((CLOSE_BRACKET(Angle) -> loc.left) :: (IDENT(id.drop(1), true) -> loc) :: rest, false, stack, acc)
        case ((tk @ IDENT(">", true), loc)) :: rest if canStartAngles =>
          raise(WarningReport(
            msg"This looks like an angle bracket, but it does not close any angle bracket section" -> S(loc) ::
            msg"Add spaces around it if you intended to use `<` as an operator" -> N :: Nil,
            newDefs = true, source = Parsing))
          go(rest, false, stack, tk -> loc :: acc)
        case (tk: Stroken, loc) :: rest =>
          go(rest, tk match {
            case SPACE | NEWLINE => false
            case _ => true
          }, stack, tk -> loc :: acc)
        case Nil =>
          stack match {
            case ((Indent, loc), oldAcc) :: _ =>
              go(CLOSE_BRACKET(Indent) -> loc/*FIXME not proper loc...*/ :: Nil, false, stack, acc)
            case ((k, l0), oldAcc) :: stack =>
              raise(ErrorReport(msg"Unmatched opening ${k.name}" -> S(l0) :: (
                if (k === Angle)
                  msg"Note that `<` without spaces around it is considered as an angle bracket and not as an operator" -> N :: Nil
                else Nil
              ), newDefs = true, source = Parsing))
              (oldAcc ::: acc).reverse
            case Nil => acc.reverse
          }
      }
    
    go(tokens, false, Nil, Nil)
    
  }
  
}

object NewLexer {
  
  type TokLoc = (Token, Loc)
  
  val keywords: Set[Str] = Set(
    "if",
    "then",
    "else",
    "case",
    "fun",
    "val",
    "var",
    // "is",
    // "as",
    "of",
    // "and",
    // "or",
    "let",
    "rec",
    "in",
    // "any",
    // "all",
    "mut",
    "declare",
    "export",
    "class",
    "trait",
    "mixin",
    "interface",
    "extends",
    "override",
    "super",
    "new",
    "namespace",
    "module",
    "type",
    "where",
    "forall",
    "exists",
    "in",
    "out",
    "weak",
    "import",
    "null",
    "undefined",
    "abstract",
    "constructor",
    "virtual",
    "unsupported"
  )

  val alpahOp: Set[Str] = Set(
    "with",
    "and",
    "or",
    "is",
    "as",
  )
  
  def printToken(tl: TokLoc): Str = tl match {
    case (SPACE, _) => " "
    case (COMMA, _) => ","
    case (NEWLINE, _) => "↵"
    case (INDENT, _) => "→"
    case (DEINDENT, _) => "←"
    case (ERROR, _) => "<error>"
    case (LITVAL(lv), _) => lv.idStr
    case (KEYWORD(name: String), _) => "#" + name
    case (IDENT(name: String, symbolic: Bool), _) => name
    case (SELECT(name: String), _) => "." + name
    case (OPEN_BRACKET(k), _) => k.beg.toString
    case (CLOSE_BRACKET(k), _) => k.end.toString
    case (BRACKETS(k @ BracketKind.Indent, contents), _) =>
      k.beg.toString + printTokens(contents) + k.end.toString
    case (BRACKETS(k, contents), _) =>
      k.beg.toString + printTokens(contents) + k.end.toString
    case (COMMENT(text: String), _) => "/*" + text + "*/"
  }
  def printTokens(ts: Ls[TokLoc]): Str =
    ts.iterator.map(printToken).mkString("|", "|", "|")
  
  

}
