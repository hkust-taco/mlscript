package mlscript

import fastparse._
import fastparse.NoWhitespace._

/** Inspired by and adapted from:
  *   scalaparse: https://github.com/lihaoyi/fastparse/tree/master/scalaparse
  *   pythonparse: https://github.com/lihaoyi/fastparse/tree/master/pythonparse
  */
@SuppressWarnings(Array("org.wartremover.warts.All"))
object Lexer {
  
  def kw[p: P](s: String) = s ~ !(letter | digit | "_")
  def comment[p: P] = P( "//" ~ CharsWhile(_ != '\n', /*min =*/ 0) )
  def wscomment[p: P] = P( (CharsWhileIn(" \n") | Lexer.comment | "\\\n").rep )
  def nonewlinewscomment[p: P] = P( (CharsWhileIn(" ") | Lexer.comment | "\\\n").rep )
  
  def identifier[p: P]: P[String] =
    P( (letter|"_"|"`") ~ (letter | digit | "_" | "-" | "'" | "!" | "?").rep ).!.filter(!keywordList.contains(_))
  def letter[p: P]     = P( lowercase | uppercase )
  def lowercase[p: P]  = P( CharIn("a-z") )
  def uppercase[p: P]  = P( CharIn("A-Z") )
  def digit[p: P]      = P( CharIn("0-9") )
  
  //def operator[p: P]: P[String] =
  //  P( ("_" | "-" | opchar).rep ).!.filter(!keywordList.contains(_))
  def operator[p: P]: P[Unit] = P(
    !symbolicKeywords ~ (!StringIn("/*", "//") ~ (CharsWhile(OpCharNotSlash) | "/")).rep(1)
  ).opaque("operator")
  
  val OpCharNotSlash = NamedFunction(x => isOpChar(x) && x != '/')
  val NotBackTick = NamedFunction(_ != '`')
  case class NamedFunction(f: Char => Boolean)
                          (implicit name: sourcecode.Name) extends (Char => Boolean){
    def apply(t: Char) = f(t)
    override def toString() = name.value
  }
  
  def OpChar[p: P] = P ( CharPred(isOpChar) )
  
  val isOpChar = NamedFunction{
    case '!' | '#' | '%' | '&' | '*' | '+' | '-' | '/'
       | ':' | '<' | '=' | '>' | '?' | '@' | '\\' | '^' | '|' | '~'  | '.'
    => true
    //case c => isOtherSymbol(c) || isMathSymbol(c)
    case c => false
  }
  
  val keywordList = Set(
    "and",
    "or",
    // "not",
    "is",
    "as",
    "with",
    "if",
    "then",
    "else",
    "yield",
    "import",
    "class",
    "interface",
    "trait",
    "object",
    "let",
    "rec",
    "in",
    "of",
    "val",
    "data",
    "type",
  )
  
  def symbolicKeywords[p: P] = P{
    StringIn(
      //":", 
      ";", "=>", "=", "->", "<-", 
      ":", "/",
      //"<:", "<%", ">:", 
      "#", "@", "\\", "\u21d2", "\u2190"
    ) ~ !OpChar
  }.opaque("SymbolicKeywords")
  
  def stringliteral[p: P]: P[String] = P( stringprefix.? ~ (longstring | shortstring) )
  def stringprefix[p: P]: P[Unit] = identifier
  def shortstring[p: P]: P[String] = P( shortstring0("'") | shortstring0("\"") )
  def shortstring0[p: P](delimiter: String) = P( delimiter ~ shortstringitem(delimiter).rep.! ~ delimiter)
  def shortstringitem[p: P](quote: String): P[Unit] = P( shortstringchar(quote) | escapeseq )
  def shortstringchar[p: P](quote: String): P[Unit] = P( CharsWhile(!s"\\\n${quote(0)}".contains(_)) )
  
  def longstring[p: P]: P[String] = P( longstring0("'''") | longstring0("\"\"\"") )
  def longstring0[p: P](delimiter: String) = P( delimiter ~ longstringitem(delimiter).rep.! ~ delimiter)
  def longstringitem[p: P](quote: String): P[Unit] = P( longstringchar(quote) | escapeseq | !quote ~ quote.take(1)  )
  def longstringchar[p: P](quote: String): P[Unit] = P( CharsWhile(!s"\\${quote(0)}".contains(_)) )
  
  def escapeseq[p: P]: P[Unit] = P( "\\" ~ AnyChar )
  
  def negatable[T, _P: P](p: => P[T])(implicit ev: Numeric[T]) = (
    //("+" | "-") // '+' is useless and causes problems, e.g., f +1 and f+1 parsed as f (+1)...
    "-"
  .?.! ~ p).map {
    case ("-", i) => ev.negate(i)
    case (_, i) => i
  }
  
  def longinteger[p: P]: P[BigInt] = P( integer ~ ("l" | "L") )
  def integer[p: P]: P[BigInt] = negatable[BigInt, Any](P( octinteger | hexinteger | bininteger | decimalinteger))
  def decimalinteger[p: P]: P[BigInt] = P( nonzerodigit ~ digit.rep | "0" ).!.map(scala.BigInt(_))
  def octinteger[p: P]: P[BigInt] = P( "0" ~ ("o" | "O") ~ octdigit.rep(1).! | "0" ~ octdigit.rep(1).! ).map(scala.BigInt(_, 8))
  def hexinteger[p: P]: P[BigInt] = P( "0" ~ ("x" | "X") ~ hexdigit.rep(1).! ).map(scala.BigInt(_, 16))
  def bininteger[p: P]: P[BigInt] = P( "0" ~ ("b" | "B") ~ bindigit.rep(1).! ).map(scala.BigInt(_, 2))
  def nonzerodigit[p: P]: P[Unit] = P( CharIn("1-9") )
  def octdigit[p: P]: P[Unit] = P( CharIn("0-7") )
  def bindigit[p: P]: P[Unit] = P( "0" | "1" )
  def hexdigit[p: P]: P[Unit] = P( digit | CharIn("a-f", "A-F") )
  
  
  def floatnumber[p: P]: P[BigDecimal] = negatable[BigDecimal, Any](P( pointfloat | exponentfloat ))
  def pointfloat[p: P]: P[BigDecimal] = P( intpart.? ~ fraction | intpart ~ "." ).!.map(BigDecimal(_))
  def exponentfloat[p: P]: P[BigDecimal] = P( (intpart | pointfloat) ~ exponent ).!.map(BigDecimal(_))
  def intpart[p: P]: P[BigDecimal] = P( digit.rep(1) ).!.map(BigDecimal(_))
  def fraction[p: P]: P[Unit] = P( "." ~ digit.rep(1) )
  def exponent[p: P]: P[Unit] = P( ("e" | "E") ~ ("+" | "-").? ~ digit.rep(1) )
  
  
}
