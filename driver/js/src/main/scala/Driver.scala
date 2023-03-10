import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.collection.mutable.{Map => MutMap}

class Driver(options: DriverOptions) {
  import Driver._

  lazy val timeStampCache =
    readFile(s"${options.outputDir}/.temp/.tsc.temp") match {
      case Some(content) => content.split("\n").foldLeft(MutMap[String, String]())((mp, rc) => {
        val data = rc.split(",")
        if (data.length < 2) mp
        else mp += (data(0) -> data(1))
      })
      case _ => MutMap[String, String]()
    }

  def flush(): Unit = {
    val res = timeStampCache.foldLeft("")((s, r) => s"$s${r._1},${r._2}\n")
    writeFile(s"${options.outputDir}/.temp", ".tsc.temp", res)
  }

  def execute: Unit =
    try {
      compile(options.filename)
    }
    catch {
      case err: Diagnostic =>
        report(err)
    } 
  
  private def compile(filename: String): Unit = {
    val mtime = getModificationTime(filename)
    if (timeStampCache.getOrElse(filename, () => "") =/= mtime) {
      readFile(filename) match {
        case Some(content) => {
          import fastparse._
          import fastparse.Parsed.{Success, Failure}
          import mlscript.{NewLexer, NewParser, ErrorReport, Origin}

          val lines = content.splitSane('\n').toIndexedSeq
            val fph = new mlscript.FastParseHelpers(content, lines)
            val origin = Origin("<input>", 1, fph)
            val lexer = new NewLexer(origin, throw _, dbg = false)
            val tokens = lexer.bracketedTokens
            val parser = new NewParser(origin, tokens, throw _, dbg = false, None) {
              def doPrintDbg(msg: => String): Unit = if (dbg) println(msg)
            }

            parser.parseAll(parser.typingUnit) match {
              case tu => {
                val beginIndex = filename.lastIndexOf("/") + 1
                val endIndex = filename.lastIndexOf(".")
                val prefixName = filename.substring(beginIndex, endIndex)
                typeCheck(tu, prefixName)
                generate(Pgrm(tu.entities), prefixName)
              }
            }
        }
        case _ => report(s"can not open file $filename")
      }

      timeStampCache += (filename -> mtime)
    }
  }

  private def typeCheck(tu: TypingUnit, filename: String): Unit = {
    val typer = new mlscript.Typer(
        dbg = false,
        verbose = false,
        explainErrors = false
      ) {
        newDefs = true
      }

    import typer._

    implicit val raise: Raise = throw _
    implicit var ctx: Ctx = Ctx.init
    implicit val extrCtx: Opt[typer.ExtrCtx] = N

    val vars: Map[Str, typer.SimpleType] = Map.empty
    val tpd = typer.typeTypingUnit(tu, allowPure = true)(ctx.nest, raise, vars)
    val comp = tpd.force()(raise)
    
    object SimplifyPipeline extends typer.SimplifyPipeline {
      def debugOutput(msg: => Str): Unit =
        // if (mode.dbgSimplif) output(msg)
        println(msg)
    }
    val sim = SimplifyPipeline(comp, all = false)(ctx)
    val exp = typer.expandType(sim)(ctx)
    val expStr = exp.showIn(ShowCtx.mk(exp :: Nil), 0)
    writeFile(s"${options.outputDir}/.temp", s"$filename.mlsi", expStr)
  }

  private def generate(program: Pgrm, filename: String): Unit = {
    val backend = new JSCompilerBackend()
    val lines = backend(program)
    val code = lines.mkString("\n")
    writeFile(options.outputDir, s"$filename.js", code)
  }
}

object Driver {
  def apply(options: DriverOptions) = new Driver(options)

  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  private def readFile(filename: String) =
    if (!fs.existsSync(filename)) None
    else Some(fs.readFileSync(filename).toString)

  private def writeFile(dir: String, filename: String, content: String) = {
    if (!fs.existsSync(dir)) fs.mkdirSync(dir, js.Dictionary("recursive" -> true))
    fs.writeFileSync(s"$dir/$filename", content)
  }

  private def getModificationTime(filename: String): String =
    if (!fs.existsSync(filename)) ""
    else {
      val state = fs.statSync(filename)
      state.mtime.toString
    }

  private def report(msg: String): Unit =
    System.err.println(msg)

  private def report(diag: Diagnostic): Unit = {
    val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
    val headStr = diag match {
      case ErrorReport(msg, loco, src) =>
        src match {
          case Diagnostic.Lexing =>
            s"╔══[LEXICAL ERROR] "
          case Diagnostic.Parsing =>
            s"╔══[PARSE ERROR] "
          case _ => // TODO customize too
            s"╔══[ERROR] "
        }
      case WarningReport(msg, loco, src) =>
        s"╔══[WARNING] "
    }
    val lastMsgNum = diag.allMsgs.size - 1
    diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
      val isLast = msgNum =:= lastMsgNum
      val msgStr = msg.showIn(sctx)
      if (msgNum =:= 0) report(headStr + msgStr)
      else report(s"${if (isLast && loco.isEmpty) "╙──" else "╟──"} ${msgStr}")
      if (loco.isEmpty && diag.allMsgs.size =:= 1) report("╙──")
      loco.foreach { loc =>
        val (startLineNum, startLineStr, startLineCol) =
          loc.origin.fph.getLineColAt(loc.spanStart)
        val (endLineNum, endLineStr, endLineCol) =
          loc.origin.fph.getLineColAt(loc.spanEnd)
        var l = startLineNum
        var c = startLineCol
        while (l <= endLineNum) {
          val globalLineNum = loc.origin.startLineNum + l - 1
          val shownLineNum = "l." + globalLineNum
          val prepre = "║  "
          val pre = s"$shownLineNum: "
          val curLine = loc.origin.fph.lines(l - 1)
          report(prepre + pre + "\t" + curLine)
          val tickBuilder = new StringBuilder()
          tickBuilder ++= (
            (if (isLast && l =:= endLineNum) "╙──" else prepre)
            + " " * pre.length + "\t" + " " * (c - 1))
          val lastCol = if (l =:= endLineNum) endLineCol else curLine.length + 1
          while (c < lastCol) { tickBuilder += ('^'); c += 1 }
          if (c =:= startLineCol) tickBuilder += ('^')
          report(tickBuilder.toString)
          c = 1
          l += 1
        }
      }
    }
    if (diag.allMsgs.isEmpty) report("╙──")
    ()
  }
}
