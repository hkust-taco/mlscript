package hkmc2

import scala.util.chaining.scalaUtilChainingOps

import mlscript.utils.*, shorthands.*


extension (s: String)
  def escaped: String =
    s.iterator.flatMap:
      case '\b' => "\\b"
      case '\t' => "\\t"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\f' => "\\f"
      case '"' => "\\\""
      case '\\' => "\\\\"
      case c if c.isControl => f"\\u${c.toInt}%04x"
      case c => c.toString
    .mkString("\"", "", "\"")


import hkmc2.semantics.TermDefFlags
import hkmc2.semantics.FldFlags
import hkmc2.semantics.ParamListFlags
import scala.collection.mutable.Buffer
import mlscript.utils.StringOps
import hkmc2.semantics.Resolvable

trait ProductWithTail extends Product

trait ProductWithExtraInfo extends Product:
  def extraInfo: Str

extension (t: Product)
  def showAsTree(using post: Product => String = Function.const("")): String =
    showAsTree(false)
  def showAsTree(inTailPos: Bool)(using post: Product => String): String =
    def aux(v: Any, inTailPos: Bool = false): String = v match
      case Some(v) => "S of " + aux(v)
      case None => "N"
      case Nil => "Nil"
      case xs: List[_] => "Ls of \n" + xs.iterator.map(aux(_)).mkString("\n").indent("  ")
      case xs: Vector[_] => "Vector of \n" + xs.iterator.map(aux(_)).mkString("\n").indent("  ")
      case s: String => s.escaped
      case TermDefFlags(isMethod) =>
        val flags = Buffer.empty[String]
        if isMethod then flags += "method"
        flags.mkString("(", ", ", ")")
      case FldFlags(mut, spec, genGetter, pat, value) =>
        val flags = Buffer.empty[String]
        if mut then flags += "mut"
        if spec then flags += "spec"
        if genGetter then flags += "gen"
        if pat then flags += "pat"
        if value then flags += "val"
        flags.mkString("(", ", ", ")")
      case ParamListFlags(ctx) =>
        val flags = Buffer.empty[String]
        if ctx then flags += "ctx"
        flags.mkString("(", ", ", ")")
      case Loc(start, end, origin) =>
        val (sl, _, sc) = origin.fph.getLineColAt(start)
        val (el, _, ec) = origin.fph.getLineColAt(end)
        s"Loc at :$sl:$sc-$el:$ec"
      
      case t: Product => t.showAsTree(inTailPos)
      case v => v.toString
    val postfix = post(t)
    val midfix = t match
      case t: ProductWithExtraInfo => t.extraInfo match
        case "" => ""
        case str => "{" + str + "}"
      case _ => ""
    val prefix = t.productPrefix + midfix + (if postfix.isEmpty then "" else s" ($postfix)")
    
    val productArity = t match
      case t: Resolvable if t.iargsLs.forall(_.nonEmpty) => t.productArity + 1
      case _ => t.productArity
    
    productArity match
      case 0 => prefix
      case 1 => prefix + " of " + aux(t.productElement(0))
      case a =>
        var args = t.productIterator.zipWithIndex.map:
          case (v, i) => t.productElementName(i) + " = " + aux(v, t.isInstanceOf[ProductWithTail] && i === a - 1)
        t match
          case t: Resolvable if t.iargsLs.forall(_.nonEmpty) =>
            args = args ++ Iterator:
              "iargsLs = " + aux(t.iargsLs)
          case _ =>
        prefix + locally:
          if inTailPos then ": \\\n" + args.mkString("\n")
          else ":\n" + args.mkString("\n").indent("  ")

extension [A](self: Opt[A])
  def mapConserve[B](f: A => A): Opt[A] =
    self match
      case S(v) =>
        val v2 = f(v)
        if v2 is v then self
        else S(v2)
      case N => N

extension [A](ls: Ls[A])
  /** Apply a special function for lists with one element. */
  def foldSingleton[B](no: Ls[A] => B)(yes: A => B): B = ls match
    case x :: Nil => yes(x)
    case Nil | _ :: _ => no(ls)

extension (n: Int)
  /** Converts a number to its English word representation. */
  def spelled: String = n match
    case 0 => "zero"  case 1 => "one"       case 2 => "two"
    case 3 => "three" case 4 => "four"      case 5 => "five"
    case 6 => "six"   case 7 => "seven"     case 8 => "eight"
    case 9 => "nine"  case _ => n.toString

extension (str: String)
  /** Converts a singular noun to its plural form using English pluralization
   *  rules. The rules should be updated as needed. */
  def pluralize: String =
    // This is not a complete list (nor is it intended to be).
    val irregularPlurals = Map("datum" -> "data", "index" -> "indices")
    val ves = Set("proof") // Add more as needed.
    val o = Set("zero") // Add more as needed.
    irregularPlurals.get(str).getOrElse:
      // -s, -sh, -ch, -x, -z -> +es
      if str.matches(".*[sxz]$") || str.endsWith("sh") || str.endsWith("ch") then str + "es"
      // -[^aeiou]y -> -ies
      else if str.matches(".*[^aeiou]y$") then str.dropRight(1) + "ies"
      // -f -> -ves (with some exceptions)
      else if str.endsWith("f") && !ves.contains(str) then str.dropRight(1) + "ves"
      // -fe -> -ves
      else if str.endsWith("fe") then str.dropRight(2) + "ves"
      // -o -> -es (with some exceptions)
      else if str.endsWith("o") && !o.contains(str) then str.dropRight(1) + "es"
      else str + "s"
  
  /** Formats a number and a noun as a human-readable string. */
  infix def countBy(n: Int): String =
    s"${n.spelled} ${if n === 1 then str else str.toLowerCase.pluralize}"
