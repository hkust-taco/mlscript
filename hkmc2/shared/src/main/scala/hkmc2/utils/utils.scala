package hkmc2.utils


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

extension (t: Product)
  def showAsTree: String =
    def aux(v: Any): String = v match
      case Some(v) => "S of " + aux(v)
      case None => "N"
      case Nil => "Nil"
      case xs: List[_] => "Ls of \n" + xs.iterator.map(aux).mkString("\n").indent("  ")
      case s: String => s.escaped
      case FldFlags(mut, spec, genGetter) =>
        val flags = Buffer.empty[String]
        if mut then flags += "mut"
        if spec then flags += "spec"
        if genGetter then flags += "gen"
        if flags.isEmpty then "()" else flags.mkString("(", ", ", ")")
      case t: Product => t.showAsTree
      case v => v.toString
    t.productArity match
      case 0 => t.productPrefix
      case 1 => t.productPrefix + " of " + aux(t.productElement(0))
      case _ =>
        val args = t.productIterator.zipWithIndex.map:
          case (v, i) => t.productElementName(i) + " = " + aux(v)
        t.productPrefix + ":\n" + args.mkString("\n").indent("  ")

