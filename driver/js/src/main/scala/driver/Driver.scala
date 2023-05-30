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
import ts2mls.TSModuleResolver

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

  import TSModuleResolver.normalize

  // Return true if success
  def execute: Boolean =
    try {
      Driver.totalErrors = 0
      implicit var ctx: Ctx = Ctx.init
      implicit val raise: Raise = report
      implicit val extrCtx: Opt[typer.ExtrCtx] = N
      implicit val vars: Map[Str, typer.SimpleType] = Map.empty
      implicit val stack = List[String]()
      compile(FileInfo(options.path, options.filename), false)
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
      writeFile(s"${options.outputDir}/package.json", content)
    }

  type ParseResult = (List[Statement], List[NuDecl], List[Import], Origin)
  private def parse(filename: String, content: String): ParseResult = {
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

  private def parseAndRun[Res](filename: String, f: (ParseResult) => Res): Res = readFile(filename) match {
    case Some(content) => f(parse(filename, content))
    case _ =>
      throw
        ErrorReport(Ls((s"can not open file $filename", None)), Diagnostic.Compilation)
  }

  private def extractSig(filename: String, moduleName: String): TypingUnit =
    parseAndRun(filename, {
      case (_, declarations, _, origin) => TypingUnit(
        NuTypeDef(Nms, TypeName(moduleName), Nil, Tup(Nil), N, Nil, N, N, TypingUnit(declarations, Nil))(S(Loc(0, 1, origin)), N) :: Nil, Nil)
    })

  private def `type`(tu: TypingUnit)(
    implicit ctx: Ctx,
    raise: Raise,
    extrCtx: Opt[typer.ExtrCtx],
    vars: Map[Str, typer.SimpleType]
  ) = {
    val tpd = typer.typeTypingUnit(tu, topLevel = true)
    val sim = SimplifyPipeline(tpd, all = false)
    typer.expandType(sim)
  }

  private def compile(
    file: FileInfo,
    exported: Boolean
  )(
    implicit ctx: Ctx,
    raise: Raise,
    extrCtx: Opt[typer.ExtrCtx],
    vars: Map[Str, typer.SimpleType],
    stack: List[String]
  ): Boolean = {
    val mlsiFile = normalize(s"${options.path}/${file.interfaceFilename}")
    if (file.filename.endsWith(".ts")) {} // TODO: invoke ts2mls
    parseAndRun(file.filename, {
      case (definitions, _, imports, _) => {
        val depList = imports.map {
          case Import(path) => path
        }

        val (cycleList, otherList) = depList.partitionMap { dep => {
          val depFile = file.`import`(dep)
          if (depFile.filename === file.filename)
            throw ErrorReport(Ls((s"can not import ${file.filename} itself", None)), Diagnostic.Compilation)
          else if (stack.contains(depFile.filename)) L(depFile)
          else R(dep)
        } }

        val (cycleSigs, cycleRecomp) = cycleList.foldLeft((Ls[TypingUnit](), false))((r, file) => r match {
          case (sigs, recomp) => {
            importedModule += file.filename
            (sigs :+ extractSig(file.filename, file.moduleName),
              isInterfaceOutdate(file.filename, s"${options.path}/${file.interfaceFilename}"))
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
          val newFilename = file.`import`(dp)
          importedModule += newFilename.filename
          compile(newFilename, true)(newCtx, raise, newExtrCtx, newVars, stack :+ file.filename)
        })

        if (options.force || needRecomp || isInterfaceOutdate(file.filename, mlsiFile)) {
          System.out.println(s"compiling ${file.filename}...")
          def importModule(file: FileInfo): Unit = {
            val filename = s"${options.path}/${file.interfaceFilename}"
            parseAndRun(filename, {
              case (_, declarations, imports, _) => {
                val depList = imports.map {
                  case Import(path) => path
                }
                depList.foreach(d => importModule(file.`import`(d)))
                `type`(TypingUnit(declarations, Nil))
              }
            })
          }

          otherList.foreach(d => importModule(file.`import`(d)))
          if (!file.filename.endsWith(".mlsi")) {
            def generateInterface(moduleName: Option[String], tu: TypingUnit) = {
              val exp = `type`(tu)
              packTopModule(moduleName, exp.showIn(ShowCtx.mk(exp :: Nil), 0))
            }

            val expStr = cycleSigs.foldLeft("")((s, tu) => s"$s${generateInterface(None, tu)}") +
              generateInterface(Some(file.moduleName), TypingUnit(definitions, Nil))
            val interfaces = otherList.map(s => Import(FileInfo.importPath(s))).foldRight(expStr)((imp, itf) => s"$imp\n$itf")

            writeFile(mlsiFile, interfaces)
            file.jsFilename match {
              case Some(filename) =>
                generate(Pgrm(definitions), s"${options.outputDir}/$filename", file.moduleName, imports, exported || importedModule(file.filename))
              case _ => ()
            }
          }
          true
        }
        else false
      }
    })
  }

  private def generate(
    program: Pgrm,
    filename: String,
    moduleName: String,
    imports: Ls[Import],
    exported: Boolean
  ): Unit = try {
    val backend = new JSCompilerBackend()
    val lines = backend(program, moduleName, imports, exported)
    val code = lines.mkString("", "\n", "\n")
    writeFile(filename, code)
  } catch {
      case CodeGenError(err) => report(ErrorReport(err, Nil, Diagnostic.Compilation))
    }
}

object Driver {
  def apply(options: DriverOptions) = new Driver(options)

  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  def readFile(filename: String) =
    if (!fs.existsSync(filename)) None
    else Some(fs.readFileSync(filename).toString)

  private def writeFile(filename: String, content: String) = {
    val dir = TSModuleResolver.dirname(filename)
    if (!fs.existsSync(dir)) fs.mkdirSync(dir, js.Dictionary("recursive" -> true))
    fs.writeFileSync(filename, content)
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
