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


import hkmc2.semantics.FldFlags
import scala.collection.mutable.Buffer
import mlscript.utils.StringOps

trait ProductWithTail extends Product

extension (t: Product)
  def showAsTree(using post: Product => String = Function.const("")): String =
    showAsTree(false)
  def showAsTree(inTailPos: Bool)(using post: Product => String): String =
    def aux(v: Any, inTailPos: Bool = false): String = v match
      case Some(v) => "S of " + aux(v)
      case None => "N"
      case Nil => "Nil"
      case xs: List[_] => "Ls of \n" + xs.iterator.map(aux(_)).mkString("\n").indent("  ")
      case s: String => s.escaped
      case FldFlags(mut, spec, genGetter) =>
        val flags = Buffer.empty[String]
        if mut then flags += "mut"
        if spec then flags += "spec"
        if genGetter then flags += "gen"
        if flags.isEmpty then "()" else flags.mkString("(", ", ", ")")
      case t: Product => t.showAsTree(inTailPos)
      case v => v.toString
    val postfix = post(t)
    val prefix = t.productPrefix + (if postfix.isEmpty then "" else s" ($postfix)")
    t.productArity match
      case 0 => prefix
      case 1 => prefix + " of " + aux(t.productElement(0))
      case a =>
        val args = t.productIterator.zipWithIndex.map:
          case (v, i) => t.productElementName(i) + " = " + aux(v, t.isInstanceOf[ProductWithTail] && i === a - 1)
        prefix + locally:
          if inTailPos then ": \\\n" + args.mkString("\n")
          else ":\n" + args.mkString("\n").indent("  ")

