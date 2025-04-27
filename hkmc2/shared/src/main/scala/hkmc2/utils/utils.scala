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

