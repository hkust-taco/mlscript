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
  def isDigit(c: Char): Bool =
    c >= '0' && c <= '9'
  
  private val isNonStickyKeywordChar = Set(
    ',',
    ':',
    ';',
  )
  
  private val isSymKeyword = Set(
    "->",
    "=",
    ":",
    ";",
    "#",
    // "<",
    // ">",
  )
  
  private val isAlphaOp = Set(
    "and",
    "or",
    "is",
    "as",
  )
  
  @tailrec final
  def takeWhile(i: Int, cur: Ls[Char] = Nil)(pred: Char => Bool): (Str, Int) =
    if (i < length && pred(bytes(i))) takeWhile(i + 1, bytes(i) :: cur)(pred)
    else (cur.reverseIterator.mkString, i)
  
  def loc(start: Int, end: Int): Loc = Loc(start, end, origin)
  
  // @tailrec final
  def lex(i: Int, ind: Ls[Int], acc: Ls[TokLoc]): Ls[TokLoc] = if (i >= length) acc.reverse else {
    val c = bytes(i)
    def pe(msg: Message): Unit =
      // raise(ParseError(false, msg -> S(loc(i, i + 1)) :: Nil))
      raise(ErrorReport(msg -> S(loc(i, i + 1)) :: Nil, source = Lexing)) // TODO parse error
    // @inline 
    def go(j: Int, tok: Token) = lex(j, ind, (tok, loc(i, j)) :: acc)
    c match {
      case ' ' =>
        val (_, j) = takeWhile(i)(_ === ' ')
        go(j, SPACE)
      case ',' =>
        val j = i + 1
        go(j, COMMA)
      case '"' =>
        val j = i + 1
        val (chars, k) = takeWhile(j)(c => c =/= '"' && c =/= '\n')
        val k2 = if (bytes.lift(k) === Some('"')) k + 1 else {
          pe(msg"unclosed quotation mark")
          k
        }
        go(k2, LITVAL(StrLit(chars)))
      case '/' if bytes.lift(i + 1).contains('/') =>
        val j = i + 2
        val (txt, k) =
          takeWhile(j)(c => c =/= '\n')
        go(k, COMMENT(txt))
      case '/' if bytes.lift(i + 1).contains('*') => // multiple-line comment
        val j = i + 2
        var prev1 = '/'; var prev2 = '*'
        val (txt, k) =
          takeWhile(j)(c => {
            val res = prev1 =/= '*' || prev2 =/= '/'
            prev1 = prev2; prev2 = c
            res
          })
        go(k, COMMENT(txt.dropRight(2)))
      case BracketKind(Left(k)) => go(i + 1, OPEN_BRACKET(k))
      case BracketKind(Right(k)) => go(i + 1, CLOSE_BRACKET(k))
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
      case _ if isIdentFirstChar(c) =>
        val (n, j) = takeWhile(i)(isIdentChar)
        go(j, if (keywords.contains(n)) KEYWORD(n) else IDENT(n, isAlphaOp(n)))
      case _ if isOpChar(c) =>
        val (n, j) = takeWhile(i)(isOpChar)
        if (n === "." && j < length && isIdentFirstChar(bytes(j))) {
          val (name, k) = takeWhile(j)(isIdentChar)
          go(k, SELECT(name))
        }
        else go(j, if (isSymKeyword.contains(n)) KEYWORD(n) else IDENT(n, true))
      case _ if isDigit(c) =>
        val (str, j) = takeWhile(i)(isDigit)
        go(j, LITVAL(IntLit(BigInt(str))))
      case _ =>
        pe(msg"unexpected character '${escapeChar(c)}'")
        go(i + 1, ERROR)
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
                  msg"does not correspond to opening ${k0.name}" -> S(l0) :: Nil, source = Parsing))
              go(rest, true, stack, BRACKETS(k0, acc.reverse)(l0.right ++ l1.left) -> (l0 ++ l1) :: oldAcc)
            case Nil =>
              raise(ErrorReport(msg"Unexpected closing ${k1.name}" -> S(l1) :: Nil, source = Parsing))
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
          raise(WarningReport(msg"This looks like an angle bracket, but it does not close any angle bracket section" -> S(loc) ::
            msg"Add spaces around it if you intended to use `<` as an operator" -> N :: Nil, source = Parsing))
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
              ), source = Parsing))
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
    "fun",
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
    "class",
    "trait",
    "interface",
    "new",
    "namespace",
    "type"
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
