import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.collection.mutable.{ListBuffer,Map => MutMap}
import mlscript.codegen._
import mlscript.{NewLexer, NewParser, ErrorReport, Origin, Diagnostic}

class Driver(options: DriverOptions) {
  import Driver._

  private val typer =
    new mlscript.Typer(
      dbg = false,
      verbose = false,
      explainErrors = false
    ) {
      newDefs = true
    }

  import typer._

  private object SimplifyPipeline extends typer.SimplifyPipeline {
    def debugOutput(msg: => Str): Unit =
      println(msg)
  }

  def execute: Unit =
    try {
      implicit var ctx: Ctx = Ctx.init
      implicit val raise: Raise = report
      implicit val extrCtx: Opt[typer.ExtrCtx] = N
      implicit val vars: Map[Str, typer.SimpleType] = Map.empty
      implicit val stack = List[String]()
      compile(options.filename)
      if (Driver.totalErrors > 0)
        js.Dynamic.global.process.exit(-1)
    }
    catch {
      case err: Diagnostic =>
        report(err)
        js.Dynamic.global.process.exit(-1)
    }
  
  def genPackageJson(): Unit = {
    val content = """{ "type": "module" }""" // TODO: more settings?
    writeFile(options.outputDir, "package.json", content)
  }

  private def compile(
    filename: String,
    exported: Boolean = false
  )(
    implicit ctx: Ctx,
    raise: Raise,
    extrCtx: Opt[typer.ExtrCtx],
    vars: Map[Str, typer.SimpleType],
    stack: List[String]
  ): Boolean =
    if (stack.contains(filename))
      throw
        ErrorReport(Ls((s"cycle dependence on $filename", None)), Diagnostic.Compilation)
    else {
      val beginIndex = filename.lastIndexOf("/")
      val endIndex = filename.lastIndexOf(".")
      val prefixName = filename.substring(beginIndex + 1, endIndex)
      val path = filename.substring(0, beginIndex + 1)

      System.out.println(s"compiling $filename...")
      readFile(filename) match {
        case Some(content) => {
          import fastparse._
          import fastparse.Parsed.{Success, Failure}

          val moduleName = prefixName.substring(prefixName.lastIndexOf("/") + 1)
          val lines = content.splitSane('\n').toIndexedSeq
          val fph = new mlscript.FastParseHelpers(content, lines)
          val origin = Origin(filename, 1, fph)
          val lexer = new NewLexer(origin, throw _, dbg = false)
          val tokens = lexer.bracketedTokens

          val parser = new NewParser(origin, tokens, throw _, dbg = false, None) {
            def doPrintDbg(msg: => String): Unit = if (dbg) println(msg)
          }

          parser.parseAll(parser.typingUnit) match {
            case tu => {
              def getAllImport(top: Ls[Import], tu: TypingUnit): Ls[Import] =
                tu.entities.foldLeft(top)((res, ett) => ett match {
                  case nudef: NuTypeDef => res ::: nudef.body.depList
                  case _ => res
                })
              val importsList = getAllImport(tu.depList, tu)
              val depList = importsList.map {
                case Import(path) => path
              }

              val needRecomp = depList.foldLeft(false)((nr, dp) => nr || {
                // We need to create another new context when compiling other files
                // e.g. A -> B, A -> C, B -> D, C -> D, -> means "depends on"
                // If we forget to add `import "D.mls"` in C, we need to raise an error
                // Keeping using the same environment would not.
                var newCtx: Ctx = Ctx.init
                val newExtrCtx: Opt[typer.ExtrCtx] = N
                val newVars: Map[Str, typer.SimpleType] = Map.empty
                compile(s"$path$dp", true)(newCtx, raise, newExtrCtx, newVars, stack :+ filename)
              })
              val mtime = getModificationTime(filename)
              val imtime = getModificationTime(s"${options.outputDir}/.temp/$prefixName.mlsi")

              if (options.force || needRecomp || imtime.isEmpty || mtime.compareTo(imtime) >= 0) {
                def importModule(modulePath: String): Unit = {
                  val filename = s"${options.outputDir}/.temp/$modulePath.mlsi"
                  val moduleName = modulePath.substring(modulePath.lastIndexOf("/") + 1)
                  readFile(filename) match {
                    case Some(content) => {
                      val lines = content.splitSane('\n').toIndexedSeq
                      val fph = new mlscript.FastParseHelpers(content, lines)
                      val origin = Origin(modulePath, 1, fph)
                      val lexer = new NewLexer(origin, throw _, dbg = false)
                      val tokens = lexer.bracketedTokens

                      val parser = new NewParser(origin, tokens, throw _, dbg = false, None) {
                        def doPrintDbg(msg: => String): Unit = if (dbg) println(msg)
                      }

                      parser.parseAll(parser.typingUnit) match {
                        case tu: TypingUnit => {
                          val depList = tu.depList.map {
                            case Import(path) => path
                          }
                          depList.foreach(d => importModule(d.substring(0, d.lastIndexOf("."))))
                          val tpd = typer.typeTypingUnit(tu, topLevel = true)
                          val sim = SimplifyPipeline(tpd, all = false)
                          val exp = typer.expandType(sim)
                        }
                      }
                    }
                    case _ =>
                      throw
                        ErrorReport(Ls((s"can not open file $filename", None)), Diagnostic.Compilation)
                  }
                }

                depList.foreach(d => importModule(d.substring(0, d.lastIndexOf("."))))
                val tpd = typer.typeTypingUnit(tu, topLevel = true)
                val sim = SimplifyPipeline(tpd, all = false)(ctx)
                val exp = typer.expandType(sim)(ctx)
                val wrapped =
                  s"module $moduleName() {\n" +
                    exp.showIn(ShowCtx.mk(exp :: Nil), 0).splitSane('\n').toIndexedSeq.map(line => s"  $line").reduceLeft(_ + "\n" + _) +
                  "\n}"
                val expStr =
                  if (exported) "declare " + wrapped
                  else wrapped
                val interfaces = importsList.map(_.toString).foldRight(expStr)((imp, itf) => s"$imp\n$itf")

                val relatedPath = path.substring(options.path.length)
                writeFile(s"${options.outputDir}/.temp/$relatedPath", s"$prefixName.mlsi", interfaces)
                generate(Pgrm(tu.entities), moduleName, importsList, prefixName, s"${options.outputDir}/$relatedPath", exported)
                true
              }
              else false
            }
          }
        }
        case _ =>
          throw
            ErrorReport(Ls((s"can not open file $filename", None)), Diagnostic.Compilation)
      }
    }

  private def generate(
    program: Pgrm,
    moduleName: String,
    imports: Ls[Import],
    filename: String,
    outputDir: String,
    exported: Boolean
  ): Unit = {
    val backend = new JSCompilerBackend()
    val lines = backend(program, moduleName, imports, exported)
    val code = lines.mkString("", "\n", "\n")
    writeFile(outputDir, s"$filename.js", code)
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
      state.mtimeMs.toString
    }

  private def report(msg: String): Unit =
    System.err.println(msg)

  private var totalErrors = 0
  
  // TODO factor with duplicated logic in DiffTests
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
              totalErrors += 1
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
