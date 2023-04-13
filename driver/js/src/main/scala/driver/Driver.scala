package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.collection.mutable.{ListBuffer,Map => MutMap, Set => MutSet}
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

  private val importedModule = MutSet[String]()

  // Return true if success
  def execute: Boolean =
    try {
      implicit var ctx: Ctx = Ctx.init
      implicit val raise: Raise = report
      implicit val extrCtx: Opt[typer.ExtrCtx] = N
      implicit val vars: Map[Str, typer.SimpleType] = Map.empty
      implicit val stack = List[String]()
      compile(options.filename, false)
      Driver.totalErrors == 0
    }
    catch {
      case err: Diagnostic =>
        report(err)
        false
    }
  
  def genPackageJson(): Unit =
    if (!fs.existsSync(s"${options.outputDir}/package.json")) {
      val content = """{ "type": "module" }""" // TODO: more settings?
      writeFile(options.outputDir, "package.json", content)
    }

  private def parse(filename: String, content: String) = {
    import fastparse._
    import fastparse.Parsed.{Success, Failure}

    val lines = content.splitSane('\n').toIndexedSeq
    val fph = new mlscript.FastParseHelpers(content, lines)
    val origin = Origin(filename, 1, fph)
    val lexer = new NewLexer(origin, throw _, dbg = false)
    val tokens = lexer.bracketedTokens

    val parser = new NewParser(origin, tokens, throw _, dbg = false, None) {
      def doPrintDbg(msg: => String): Unit = if (dbg) println(msg)
    }

    val tu = parser.parseAll(parser.typingUnit)
    val (definitions, declarations) = tu.entities.partitionMap {
      case nt: NuTypeDef if (nt.isDecl) => Right(nt)
      case nf @ NuFunDef(_, _, _, Right(_)) => Right(nf)
      case t => Left(t)
    }

    (definitions, declarations, tu.depList, origin)
  }

  private def isInterfaceOutdate(origin: String, inter: String): Boolean = {
    val mtime = getModificationTime(origin)
    val imtime = getModificationTime(inter)
    imtime.isEmpty || mtime.compareTo(imtime) >= 0
  }

  private def packTopModule(moduleName: Option[String], content: String) =
    moduleName match {
      case Some(moduleName) =>
        s"declare module $moduleName() {\n" +
          content.splitSane('\n').toIndexedSeq.filter(!_.isEmpty()).map(line => s"  $line").reduceLeft(_ + "\n" + _) +
        "\n}\n"
      case _ => s"declare $content"
    }

  private def extractSig(filename: String, moduleName: String): TypingUnit =
    readFile(filename) match {
      case Some(content) =>
        parse(filename, content) match {
          case (_, declarations, _, origin) => TypingUnit(
            NuTypeDef(Nms, TypeName(moduleName), Nil, Tup(Nil), N, Nil, N, N, TypingUnit(declarations, Nil))(S(Loc(0, 1, origin))) :: Nil, Nil)
        }
      case None =>
        throw ErrorReport(Ls((s"can not open file $filename", None)), Diagnostic.Compilation)
    }

  private def compile(
    filename: String,
    exported: Boolean
  )(
    implicit ctx: Ctx,
    raise: Raise,
    extrCtx: Opt[typer.ExtrCtx],
    vars: Map[Str, typer.SimpleType],
    stack: List[String]
  ): Boolean = {
    val beginIndex = filename.lastIndexOf("/")
    val endIndex = filename.lastIndexOf(".")
    val prefixName = filename.substring(beginIndex + 1, endIndex)
    val path = filename.substring(0, beginIndex + 1)
    val moduleName = prefixName.substring(prefixName.lastIndexOf("/") + 1)
    val relatedPath = path.substring(options.path.length)

    readFile(filename) match {
      case Some(content) => {
        parse(filename, content) match {
          case (definitions, _, imports, _) => {
            val depList = imports.map {
              case Import(path) => path
            }

            val (cycleList, otherList) = depList.partitionMap { dep => {
              val depFile = s"$path$dep"
              if (depFile === filename)
                throw ErrorReport(Ls((s"can not import $filename itself", None)), Diagnostic.Compilation)
              else if (stack.contains(depFile)) L(dep)
              else R(dep)
            } }

            val (cycleSigs, cycleRecomp) = cycleList.foldLeft((Ls[TypingUnit](), false))((r, dep) => r match {
              case (sigs, recomp) => {
                val filename = s"$path$dep"
                val prefixName = dep.substring(0, dep.lastIndexOf("."))
                (sigs :+ extractSig(filename, prefixName),
                  isInterfaceOutdate(filename, s"${options.outputDir}/.temp/$relatedPath/$prefixName.mlsi"))
              }
            })
            val needRecomp = otherList.foldLeft(cycleRecomp)((nr, dp) => nr || {
              // We need to create another new context when compiling other files
              // e.g. A -> B, A -> C, B -> D, C -> D, -> means "depends on"
              // If we forget to add `import "D.mls"` in C, we need to raise an error
              // Keeping using the same environment would not.
              var newCtx: Ctx = Ctx.init
              val newExtrCtx: Opt[typer.ExtrCtx] = N
              val newVars: Map[Str, typer.SimpleType] = Map.empty
              val newFilename = s"$path$dp"
              importedModule += newFilename
              compile(newFilename, true)(newCtx, raise, newExtrCtx, newVars, stack :+ filename)
            })

            if (options.force || needRecomp || isInterfaceOutdate(filename, s"${options.outputDir}/.temp/$relatedPath/$prefixName.mlsi")) {
              System.out.println(s"compiling $filename...")
              def importModule(modulePath: String): Unit = {
                val filename = s"${options.outputDir}/.temp/$modulePath.mlsi"
                val moduleName = modulePath.substring(modulePath.lastIndexOf("/") + 1)
                readFile(filename) match {
                  case Some(content) => {
                    parse(filename, content) match {
                      case (_, declarations, imports, _) => {
                        val depList = imports.map {
                          case Import(path) => path
                        }
                        depList.foreach(d => importModule(d.substring(0, d.lastIndexOf("."))))
                        val tpd = typer.typeTypingUnit(TypingUnit(declarations, Nil), topLevel = true)
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

              otherList.foreach(d => importModule(d.substring(0, d.lastIndexOf("."))))
              def generateInterface(moduleName: Option[String], tu: TypingUnit) = {
                val tpd = typer.typeTypingUnit(tu, topLevel = true)
                val sim = SimplifyPipeline(tpd, all = false)(ctx)
                val exp = typer.expandType(sim)(ctx)
                packTopModule(moduleName, exp.showIn(ShowCtx.mk(exp :: Nil), 0))
              }

              val expStr = cycleSigs.foldLeft("")((s, tu) => s"$s${generateInterface(None, tu)}") +
                generateInterface(Some(moduleName), TypingUnit(definitions, Nil))
              val interfaces = otherList.map(s => Import(s"${s}i")).foldRight(expStr)((imp, itf) => s"$imp\n$itf")

              writeFile(s"${options.outputDir}/.temp/$relatedPath", s"$prefixName.mlsi", interfaces)
              generate(Pgrm(definitions), moduleName, imports, prefixName, s"${options.outputDir}/$relatedPath", exported || importedModule(filename))
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
  ): Unit = try {
    val backend = new JSCompilerBackend()
    val lines = backend(program, moduleName, imports, exported)
    val code = lines.mkString("", "\n", "\n")
    writeFile(outputDir, s"$filename.js", code)
  } catch {
      case CodeGenError(err) => report(ErrorReport(err, Nil, Diagnostic.Compilation))
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
