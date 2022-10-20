package mlscript

class CodeGenTestHelpers(file: os.Path, output: String => Unit) {
  def showGeneratedCode(testCode: JSTestBackend.TestCode): Unit = {
    val JSTestBackend.TestCode(prelude, queries) = testCode
    if (!prelude.isEmpty) {
      output("// Prelude")
      prelude foreach { line =>
        output(line)
      }
    }
    queries.zipWithIndex foreach {
      case (JSTestBackend.CodeQuery(prelude, code, _), i) =>
        output(s"// Query ${i + 1}")
        prelude foreach { output(_) }
        code foreach { output(_) }
      case (JSTestBackend.AbortedQuery(reason), i) =>
        output(s"// Query ${i + 1} aborted: $reason")
      case (JSTestBackend.EmptyQuery, i) =>
        output(s"// Query ${i + 1} is empty")
    }
    output("// End of generated code")
  }
  def showReplPrelude(
    sourceLines: List[String],
    preludeReply: Option[ReplHost.Reply],
    blockLineNum: Int,
  ): Unit = {
    output(s"┌ Block at ${file.last}:${blockLineNum}")
    if (sourceLines.isEmpty) {
      output(s"├── No prelude")
    } else {
      output(s"├─┬ Prelude")
      output(s"│ ├── Code")
      sourceLines.iterator.foreach { line => output(s"│ │   $line") }
    }
    preludeReply.foreach {
      // Display successful results in multiple lines.
      // Display other results in single line.
      case ReplHost.Result(content, intermediate) =>
        intermediate.foreach { value =>
          output(s"│ ├── Intermediate")
          value.linesIterator.foreach { line => output(s"│ │   $line") }  
        }
        output(s"│ └── Reply")
        content.linesIterator.foreach { line => output(s"│     $line") }  
      case other => output(s"│ └── Reply $other")
    }
  }
  def showReplContent(
    queries: List[JSTestBackend.Query],
    replies: List[ReplHost.Reply],
  ): Unit = {
    if (queries.isEmpty) {
      output(s"└── No queries")
    } else {
      val length = queries.length // We assume that queries.length === replies.length
      queries.iterator.zip(replies).zipWithIndex.foreach {
        case ((JSTestBackend.CodeQuery(preludeLines, codeLines, res), reply), i) =>
          val p0 = if (i + 1 == length) "  " else "│ "
          val p1 = if (i + 1 == length) "└─" else "├─"
          output(s"$p1┬ Query ${i + 1}/${queries.length}")
          if (preludeLines.isEmpty) {
            output(s"$p0├── Prelude: <empty>")
          } else {
            output(s"$p0├── Prelude:")
            preludeLines.foreach { line => output(s"$p0├──   $line") }
          }
          output(s"$p0├── Code:")
          codeLines.foreach { line => output(s"$p0├──   $line") }
          // Show the intermediate reply if possible.
          reply match {
            case ReplHost.Result(_, Some(intermediate)) =>
              output(s"$p0├── Intermediate: $intermediate")
            case _ => ()
          }
          val p2 = if (i + 1 == length) "  └──" else s"$p0└──"
          output(s"$p2 Reply: $reply")
        case ((JSTestBackend.AbortedQuery(reason), _), i) =>
          val prefix = if (i + 1 == queries.length) "└──" else "├──"
          output(s"$prefix Query ${i + 1}/${queries.length}: <aborted: $reason>")
        case ((JSTestBackend.EmptyQuery, _), i) =>
          val prefix = if (i + 1 == queries.length) "└──" else "├──"
          output(s"$prefix Query ${i + 1}/${queries.length}: <empty>")
      }
    }
  }
}