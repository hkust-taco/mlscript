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
    showAsTree(false, identity(_))
  def showAsTree(inTailPos: Bool, pre: PartialFunction[Product, Product])(using post: Product => String): String =
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
      case FldFlags(mut, spec, pat, value) =>
        val flags = Buffer.empty[String]
        if mut then flags += "mut"
        if spec then flags += "spec"
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
      
      case t: Product => t.showAsTree(inTailPos, pre)
      case v => v.toString
    
    val tt = pre.applyOrElse(t, identity)
    val postfix = post(tt)
    val midfix = tt match
      case t: ProductWithExtraInfo => t.extraInfo match
        case "" => ""
        case str => "{" + str + "}"
      case _ => ""
    val prefix = tt.productPrefix + midfix + (if postfix.isEmpty then "" else s" ($postfix)")
    
    tt.productArity match
      case 0 => prefix
      case 1 => prefix + " of " + aux(tt.productElement(0))
      case a =>
        var args = tt.productIterator.zipWithIndex.map:
          case (v, i) => tt.productElementName(i) + " = " + aux(v, tt.isInstanceOf[ProductWithTail] && i === a - 1)
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

object English:
  // These lists are not complete (nor are they intended to be). Please add
  // necessary words as needed.
  val irregularPlurals = Map("datum" -> "data", "index" -> "indices")
  val ves = Set("proof")
  val o = Set("zero")

extension (str: String)
  /** Converts a singular noun to its plural form using English pluralization
   *  rules. The rules should be updated as needed. */
  def pluralize: String = English.irregularPlurals.getOrElse(str,
    if str.isEmpty then str else str(str.size - 1) match
      // -s, -sh, -ch, -x, -z -> +es; e.g., bus -> buses, box -> boxes
      case 's' | 'x' | 'z' => str + "es"
      // -sh, -ch -> +es; e.g., brush -> brushes, church -> churches
      case 'h' if str.size > 1 && (str(str.size - 2) === 's' || str(str.size - 2) === 'c') =>
        str + "es"
      // -o -> +es (with some exceptions); e.g., potato -> potatoes
      case 'o' if !English.o.contains(str) => str + "es"
      // -[^aeiou]y -> -ies; e.g., city -> cities, but not toy -> toys
      case 'y' if str.size > 1 => str(str.size - 2) match
        case 'a' | 'e' | 'i' | 'o' | 'u' => str + "s" // Vowel before 'y'
        case _ => str.dropRight(1) + "ies" // Consonant before 'y'
      // -f -> -ves (with exceptions); e.g., leaf -> leaves
      case 'f' if !English.ves.contains(str) => str.dropRight(1) + "ves"
      // -fe -> -ves; e.g., knife -> knives
      case 'e' if str.size > 1 && str(str.size - 2) === 'f' => str.dropRight(2) + "ves"
      // Default case: just add 's'
      case _ => str + "s")
  
  /** Formats a number and a noun as a human-readable string. */
  infix def countBy(n: Int): String =
    s"${n.spelled} ${if n === 1 then str else str.toLowerCase.pluralize}"
