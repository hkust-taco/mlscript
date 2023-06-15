package driver

import scala.scalajs.js
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.collection.mutable.{ListBuffer,Map => MutMap, Set => MutSet}
import mlscript.codegen._
import mlscript.{NewLexer, NewParser, ErrorReport, Origin, Diagnostic}
import ts2mls.{TSProgram, TypeScript}
import ts2mls.TSPathResolver
import ts2mls.JSFileSystem
import ts2mls.JSWriter

class Driver(options: DriverOptions) {
  import Driver._
  import ts2mls.JSFileSystem._
  import JSCompilerBackend.ModuleType

  private val typer =
    new mlscript.Typer(
      dbg = false,
      verbose = false,
      explainErrors = false,
      newDefs = true
    )

  import typer._

  private object SimplifyPipeline extends typer.SimplifyPipeline {
    def debugOutput(msg: => Str): Unit =
      println(msg)
  }

  private val importedModule = MutSet[String]()
  private implicit val config = TypeScript.parseOption(options.path, options.tsconfig)

  import TSPathResolver.{normalize, isLocal, dirname}

  private def checkESModule(filename: String) =
    if (filename.endsWith(".mls")) None
    else if (isLocal(filename))
      Some(TypeScript.isESModule(config, false))
    else {
      val fullname = TypeScript.resolveModuleName(filename, "", config).getOrElse("node_modules/")
      def find(path: String): Boolean = {
        val dir = dirname(path)
        val pack = s"$dir/package.json"
        if (JSFileSystem.exists(pack)) {
          val config = TypeScript.parsePackage(pack)
          TypeScript.isESModule(config, true)
        }
        else if (dir.endsWith("node_modules/")) false // TODO: throw?
        else find(dir)
      }
      Some(find(fullname))
    }

  // Return true if success
  def execute: Boolean =
    try {
      Driver.totalErrors = 0
      implicit var ctx: Ctx = Ctx.init
      implicit val raise: Raise = report
      implicit val extrCtx: Opt[typer.ExtrCtx] = N
      implicit val vars: Map[Str, typer.SimpleType] = Map.empty
      implicit val stack = List[String]()
      initTyper
      compile(FileInfo(options.path, options.filename, options.interfaceDir), false)
      Driver.totalErrors == 0
    }
    catch {
      case err: Diagnostic =>
        report(err)
        false
      case t : Throwable =>
        report(s"unexpected error: ${t.toString()}")
        false
    }
  
  def genPackageJson(): Unit =
    if (!exists(s"${options.outputDir}/package.json")) {
      val content = """{ "type": "module" }""" // TODO: more settings?
      saveToFile(s"${options.outputDir}/package.json", content)
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
      case _ => content
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
        NuTypeDef(Mod, TypeName(moduleName), Nil, S(Tup(Nil)), N, N, Nil, N, N, TypingUnit(declarations, Nil))(S(Loc(0, 1, origin)), N, N) :: Nil, Nil)
    })

  private def `type`(tu: TypingUnit)(
    implicit ctx: Ctx,
    raise: Raise,
    extrCtx: Opt[typer.ExtrCtx],
    vars: Map[Str, typer.SimpleType]
  ) = {
    val tpd = typer.typeTypingUnit(tu, N)
    val sim = SimplifyPipeline(tpd, all = false)
    typer.expandType(sim)
  }

  private lazy val jsBuiltinDecs = Driver.jsBuiltinPaths.map(path => parseAndRun(path, {
    case (_, declarations, _, _) => declarations
  }))

  private def initTyper(
    implicit ctx: Ctx,
    raise: Raise,
    extrCtx: Opt[typer.ExtrCtx],
    vars: Map[Str, typer.SimpleType]
  ) = jsBuiltinDecs.foreach(lst => `type`(TypingUnit(lst, Nil)))

  private def resolveTarget(file: FileInfo, imp: String) =
    if ((imp.startsWith("./") || imp.startsWith("../")) && !imp.endsWith(".mls") && !imp.endsWith(".mlsi")) {
      val tsPath = TypeScript.getOutputFileNames(s"${TSPathResolver.dirname(file.filename)}/$imp", config)
      val outputBase = TSPathResolver.dirname(TSPathResolver.normalize(s"${options.outputDir}${file.jsFilename}"))
      TSPathResolver.relative(outputBase, tsPath)
    }
    else imp

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
    val mlsiFile = normalize(s"${file.workDir}/${file.interfaceFilename}")
    if (!file.filename.endsWith(".mls") && !file.filename.endsWith(".mlsi") ) { // TypeScript
      val tsprog =
         TSProgram(file.localFilename, file.workDir, true, options.tsconfig)
      return tsprog.generate(Some(file.moduleName), mlsiFile)
    }
    parseAndRun(file.filename, {
      case (definitions, _, imports, _) => {
        val depList = imports.map(_.path)

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
        val needRecomp = otherList.foldLeft(cycleRecomp)((nr, dp) => {
          // We need to create another new context when compiling other files
          // e.g. A -> B, A -> C, B -> D, C -> D, -> means "depends on"
          // If we forget to add `import "D.mls"` in C, we need to raise an error
          // Keeping using the same environment would not.
          var newCtx: Ctx = Ctx.init
          val newExtrCtx: Opt[typer.ExtrCtx] = N
          val newVars: Map[Str, typer.SimpleType] = Map.empty
          initTyper
          val newFilename = file.`import`(dp)
          importedModule += newFilename.filename
          compile(newFilename, true)(newCtx, raise, newExtrCtx, newVars, stack :+ file.filename)
        } || nr)

        if (options.force || needRecomp || isInterfaceOutdate(file.filename, mlsiFile)) {
          System.out.println(s"compiling ${file.filename}...")
          def importModule(file: FileInfo): Unit = {
            val filename = s"${options.path}/${file.interfaceFilename}"
            parseAndRun(filename, {
              case (_, declarations, imports, _) => {
                val depList = imports.map(_.path)
                depList.foreach(d => importModule(file.`import`(d)))
                `type`(TypingUnit(declarations, Nil))
              }
            })
          }

          otherList.foreach(d => importModule(file.`import`(d)))
          if (file.filename.endsWith(".mls")) {
            def generateInterface(moduleName: Option[String], tu: TypingUnit) = {
              val exp = `type`(tu)
              packTopModule(moduleName, exp.show)
            }

            val expStr = cycleSigs.foldLeft("")((s, tu) => s"$s${generateInterface(None, tu)}") +
              generateInterface(Some(file.moduleName), TypingUnit(definitions, Nil))
            val interfaces = otherList.map(s => Import(FileInfo.importPath(s))).foldRight(expStr)((imp, itf) => s"$imp\n$itf")

            saveToFile(mlsiFile, interfaces)
            generate(Pgrm(definitions), s"${options.outputDir}/${file.jsFilename}", file.moduleName, imports.map(
              imp => new Import(resolveTarget(file, imp.path)) with ModuleType {
                val isESModule = checkESModule(path)
              }
            ), exported || importedModule(file.filename))
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
    imports: Ls[Import with ModuleType],
    exported: Boolean
  ): Unit = try {
    val backend = new JSCompilerBackend()
    jsBuiltinDecs.foreach(lst => backend.declareJSBuiltin(Pgrm(lst)))
    val lines = backend(program, moduleName, imports, exported)
    val code = lines.mkString("", "\n", "\n")
    saveToFile(filename, code)
  } catch {
      case CodeGenError(err) => report(ErrorReport(err, Nil, Diagnostic.Compilation))
    }
}

object Driver {
  def apply(options: DriverOptions) = new Driver(options)

  private val jsBuiltinPaths = List(
    "./ts2mls/js/src/test/diff/ES5.mlsi",
    "./ts2mls/js/src/test/diff/Dom.mlsi"
  )

  private def report(msg: String): Unit =
    System.err.println(msg)

  private var totalErrors = 0

  private def saveToFile(filename: String, content: String) = {
    val writer = JSWriter(filename)
    writer.write(content)
    writer.close()
  }
  
  // TODO factor with duplicated logic in DiffTests
  private def report(diag: Diagnostic): Unit = {
    val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
    val headStr = diag match {
      case ErrorReport(msg, loco, src) =>
        totalErrors += 1
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
