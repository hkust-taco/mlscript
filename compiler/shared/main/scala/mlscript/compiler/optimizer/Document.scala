package mlscript.compiler.optimizer

enum Document:
  case Indented(content: Document)
  case Unindented(content: Document)
  case Stacked(docs: List[Document], emptyLines: Boolean = false)
  case Lined(docs: List[Document], separator: Document)
  case Raw(s: String)

  def <:>(other: Document) = line(List(this, other))
  def <#>(other: Document) = line(List(this, other), sep = "")

  override def toString(): String = print

  def print: String = {
    val sb = StringBuffer()

    def rec(d: Document)(implicit ind: Int, first: Boolean): Unit = d match {
      case Raw(s) =>
        if (first && s.nonEmpty) sb.append("  " * ind)
        sb.append(s)
      case Indented(doc) =>
        rec(doc)(ind + 1, first)
      case Unindented(doc) =>
        assume(ind > 0)
        rec(doc)(ind - 1, first)
      case Lined(Nil, _) => // skip
      case Lined(docs, sep) =>
        rec(docs.head)
        docs.tail foreach { doc =>
          rec(sep)(ind, false)
          rec(doc)(ind, false)
        }
      case Stacked(Nil, _) => // skip
      case Stacked(docs, emptyLines) =>
        rec(docs.head)
        docs.tail foreach { doc =>
          sb.append("\n")
          if (emptyLines) sb.append("\n")
          rec(doc)(ind, true)
        }
    }

    rec(this)(0, true)
    sb.toString
  }

def stack(docs: Document*) = Document.Stacked(docs.toList)
def stack_list(docs: List[Document]) = Document.Stacked(docs)
def line(docs: List[Document], sep: String = " ") = Document.Lined(docs, Document.Raw(sep))
def raw(s: String) = Document.Raw(s)
def indent(doc: Document) = Document.Indented(doc)
