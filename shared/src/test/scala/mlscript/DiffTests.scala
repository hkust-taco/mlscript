package mlscript

import fastparse._
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line
import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap}
import scala.collection.immutable
import mlscript.utils._, shorthands._
import mlscript.codegen.typescript.TsTypegenCodeBuilder
import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}


abstract class ModeType {
  def expectTypeErrors: Bool
  def expectWarnings: Bool
  def expectParseErrors: Bool
  def fixme: Bool
  def showParse: Bool
  def verbose: Bool
  def noSimplification: Bool
  def explainErrors: Bool
  def dbg: Bool
  def dbgParsing: Bool
  def dbgSimplif: Bool
  def dbgUCS: Bool
  def fullExceptionStack: Bool
  def stats: Bool
  def stdout: Bool
  def noExecution: Bool
  def noGeneration: Bool
  def showGeneratedJS: Bool
  def generateTsDeclarations: Bool
  def debugVariance: Bool
  def expectRuntimeErrors: Bool
  def expectCodeGenErrors: Bool
  def showRepl: Bool
  def allowEscape: Bool
}

class DiffTests
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
  with TimeLimitedTests
{
  
  
  /**  Hook for dependent projects, like the monomorphizer. */
  def postProcess(mode: ModeType, basePath: Ls[Str], testName: Str, unit: TypingUnit): Ls[Str] = Nil
  
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  import DiffTests._

  // scala test will not execute a test if the test class has constructor parameters.
  // override this to get the correct paths of test files.
  protected lazy val files = allFiles.filter { file =>
      val fileName = file.baseName
      // validExt(file.ext) && filter(fileName)
      validExt(file.ext) && filter(file.relativeTo(pwd))
  }
  
  val timeLimit = TimeLimit
  
  override val defaultTestSignaler: Signaler = new Signaler {
    @annotation.nowarn("msg=method stop in class Thread is deprecated") def apply(testThread: Thread): Unit = {
      println(s"!! Test at $testThread has run out out time !! stopping..." +
        "\n\tNote: you can increase this limit by changing DiffTests.TimeLimit")
      // * Thread.stop() is considered bad practice because normally it's better to implement proper logic
      // * to terminate threads gracefully, avoiding leaving applications in a bad state.
      // * But here we DGAF since all the test is doing is runnign a type checker and some Node REPL,
      // * which would be a much bigger pain to make receptive to "gentle" interruption.
      // * It would feel extremely wrong to intersperse the pure type checker algorithms
      // * with ugly `Thread.isInterrupted` checks everywhere...
      testThread.stop()
    }
  }
  
  files.foreach { file =>
        val basePath = file.segments.drop(dir.segmentCount).toList.init
        val testName = basePath.map(_ + "/").mkString + file.baseName
        test(testName) {
    
    val baseStr = basePath.mkString("/")
    
    val testStr = " " * (8 - baseStr.length) + baseStr + ": " + file.baseName
    
    if (!inParallel) print(s"Processing $testStr")
    
    // * For some reason, the color is sometimes wiped out when the line is later updated not in iTerm3:
    // if (!inParallel) print(s"${Console.CYAN}Processing${Console.RESET} $testStr ... ")
    
    val beginTime = System.nanoTime()
    
    val outputMarker = "//│ "
    // val oldOutputMarker = "/// "
    
    val diffBegMarker = "<<<<<<<"
    val diffMidMarker = "======="
    val diff3MidMarker = "|||||||" // * Appears under `git config merge.conflictstyle diff3` (https://stackoverflow.com/a/18131595/1518588)
    val diffEndMarker = ">>>>>>>"
    
    val exitMarker = "=" * 100
    
    var occursCheck = false
    
    val fileContents = os.read(file)
    val allLines = fileContents.splitSane('\n').toList
    val strw = new java.io.StringWriter
    val out = new java.io.PrintWriter(strw) {
      override def println(): Unit = print('\n') // to avoid inserting CRLF on Windows
    }
    var stdout = false
    def output(str: String) =
      // out.println(outputMarker + str)
      if (stdout) System.out.println(str) else
      str.splitSane('\n').foreach(l => out.println(outputMarker + l))
    def outputSourceCode(code: SourceCode) = code.lines.foreach{line => out.println(outputMarker + line.toString())}
    val allStatements = mutable.Buffer.empty[DesugaredStatement]
    val typer = new Typer(dbg = false, verbose = false, explainErrors = false) {
      override def recordTypeVars = occursCheck
      override def funkyTuples = file.ext =:= "fun"
      // override def emitDbg(str: String): Unit = if (stdout) System.out.println(str) else output(str)
      override def emitDbg(str: String): Unit = output(str)
    }
    var ctx: typer.Ctx = typer.Ctx.init
    var declared: Map[Str, typer.ST] = Map.empty
    val failures = mutable.Buffer.empty[Int]
    val unmergedChanges = mutable.Buffer.empty[Int]
    typer.createdTypeVars.clear()
    
    case class Mode(
      expectTypeErrors: Bool = false,
      expectWarnings: Bool = false,
      expectParseErrors: Bool = false,
      fixme: Bool = false,
      showParse: Bool = false,
      verbose: Bool = false,
      noSimplification: Bool = false,
      explainErrors: Bool = false,
      dbg: Bool = false,
      dbgParsing: Bool = false,
      dbgSimplif: Bool = false,
      dbgUCS: Bool = false,
      fullExceptionStack: Bool = false,
      stats: Bool = false,
      stdout: Bool = false,
      preciselyTypeRecursion: Bool = false,
      noExecution: Bool = false,
      noGeneration: Bool = false,
      showGeneratedJS: Bool = false,
      generateTsDeclarations: Bool = false,
      debugVariance: Bool = false,
      expectRuntimeErrors: Bool = false,
      expectCodeGenErrors: Bool = false,
      showRepl: Bool = false,
      allowEscape: Bool = false,
      // noProvs: Bool = false,
    ) extends ModeType {
      def isDebugging: Bool = dbg || dbgSimplif
    }
    val defaultMode = Mode()
    
    var parseOnly = basePath.headOption.contains("parser") || basePath.headOption.contains("compiler")
    var allowTypeErrors = false
    var allowParseErrors = false
    var showRelativeLineNums = false
    var noJavaScript = false
    var noProvs = false
    var allowRuntimeErrors = false
    var generalizeCurriedFunctions = false
    // var generalizeCurriedFunctions = true
    var distributeForalls = true
    // var distributeForalls = false
    var approximateNegativeFunction = false
    var noCycleCheck = false
    var noRecursiveTypes = false
    var constrainedTypes = false
    var irregularTypes = false
    
    // * This option makes some test cases pass which assume generalization should happen in arbitrary arguments
    // * but it's way too aggressive to be ON by default, as it leads to more extrusion, cycle errors, etc.
    var generalizeArguments = false
    
    var newParser = basePath.headOption.contains("parser") || basePath.headOption.contains("compiler")
    
    val backend = new JSTestBackend()
    val host = ReplHost()
    val codeGenTestHelpers = new CodeGenTestHelpers(file, output)
    
    def rec(lines: List[String], mode: Mode): Unit = lines match {
      case "" :: Nil =>
      case line :: ls if line.startsWith(":") =>
        out.println(line)
        val newMode = line.tail.takeWhile(!_.isWhitespace) match {
          case "e" => mode.copy(expectTypeErrors = true)
          case "w" => mode.copy(expectWarnings = true)
          case "pe" => mode.copy(expectParseErrors = true)
          case "p" => mode.copy(showParse = true)
          case "d" => mode.copy(dbg = true)
          case "dp" => mode.copy(dbgParsing = true)
          case "ds" => mode.copy(dbgSimplif = true)
          case "ducs" => mode.copy(dbg = true, dbgUCS = true)
          case "s" => mode.copy(fullExceptionStack = true)
          case "v" | "verbose" => mode.copy(verbose = true)
          case "ex" | "explain" => mode.copy(expectTypeErrors = true, explainErrors = true)
          case "ns" | "no-simpl" => mode.copy(noSimplification = true)
          // case "limit-errors" => mode.copy(limitErrors = true)
          case "stats" => mode.copy(stats = true)
          case "stdout" => mode.copy(stdout = true)
          case "precise-rec-typing" => mode.copy(preciselyTypeRecursion = true)
          case "ParseOnly" => parseOnly = true; mode
          case "AllowTypeErrors" => allowTypeErrors = true; mode
          case "AllowParseErrors" => allowParseErrors = true; mode
          case "AllowRuntimeErrors" => allowRuntimeErrors = true; mode
          case "ShowRelativeLineNums" => showRelativeLineNums = true; mode
          case "NewParser" => newParser = true; mode
          case "NoJS" => noJavaScript = true; mode
          case "NoProvs" => noProvs = true; mode
          case "GeneralizeCurriedFunctions" => generalizeCurriedFunctions = true; mode
          case "DontGeneralizeCurriedFunctions" => generalizeCurriedFunctions = false; mode
          case "DistributeForalls" =>
            distributeForalls = true
            generalizeCurriedFunctions = false
            mode
          case "DontDistributeForalls" =>
            distributeForalls = false
            generalizeCurriedFunctions = true
            mode
          case "ApproximateNegativeFunction" => approximateNegativeFunction = true; mode
          case "NoCycleCheck" => noCycleCheck = true; mode
          case "CycleCheck" => noCycleCheck = false; mode
          case "OccursCheck" => occursCheck = true; mode
          case "RecursiveTypes" => noRecursiveTypes = false; occursCheck = false; mode
          case "NoRecursiveTypes" => noRecursiveTypes = true; occursCheck = true; mode
          case "ConstrainedTypes" => constrainedTypes = true; mode
          case "NoConstrainedTypes" => constrainedTypes = false; mode
          case "GeneralizeArguments" => generalizeArguments = true; mode
          case "DontGeneralizeArguments" => generalizeArguments = false; mode
          case "IrregularTypes" => irregularTypes = true; mode
          case str @ "Fuel" =>
            // println("'"+line.drop(str.length + 2)+"'")
            typer.startingFuel = line.drop(str.length + 2).toInt; mode
          case "ResetFuel" => typer.startingFuel = typer.defaultStartingFuel; mode
          case "ne" => mode.copy(noExecution = true)
          case "ng" => mode.copy(noGeneration = true)
          case "js" => mode.copy(showGeneratedJS = true)
          case "ts" => mode.copy(generateTsDeclarations = true)
          case "dv" => mode.copy(debugVariance = true)
          case "ge" => mode.copy(expectCodeGenErrors = true)
          case "re" => mode.copy(expectRuntimeErrors = true)
          case "ShowRepl" => mode.copy(showRepl = true)
          case "escape" => mode.copy(allowEscape = true)
          case "exit" =>
            out.println(exitMarker)
            ls.dropWhile(_ =:= exitMarker).tails.foreach {
              case Nil =>
              case lastLine :: Nil => out.print(lastLine)
              case l :: _ => out.println(l)
            }
            return ()
          case _ =>
            failures += allLines.size - lines.size
            output("/!\\ Unrecognized option " + line)
            mode
        }
        rec(ls, newMode)
      case line :: ls if line.startsWith("// FIXME") || line.startsWith("// TODO") =>
        out.println(line)
        rec(ls, mode.copy(fixme = true))
      case line :: ls if line.startsWith(outputMarker) //|| line.startsWith(oldOutputMarker)
        => rec(ls, defaultMode)
      case line :: ls if line.isEmpty =>
        out.println(line)
        rec(ls, defaultMode)
      case line :: ls if line.startsWith("//") =>
        out.println(line)
        rec(ls, mode)
      case line :: ls if line.startsWith(diffBegMarker) => // Check if there are unmerged git conflicts
        val diff = ls.takeWhile(l => !l.startsWith(diffEndMarker))
        assert(diff.exists(_.startsWith(diffMidMarker)), diff)
        val rest = ls.drop(diff.length)
        val hdo = rest.headOption
        assert(hdo.exists(_.startsWith(diffEndMarker)), hdo)
        val blankLines = diff.count(_.isEmpty)
        val hasBlankLines = diff.exists(_.isEmpty)
        if (diff.forall(l => l.startsWith(outputMarker) || l.startsWith(diffMidMarker) || l.startsWith(diff3MidMarker) || l.isEmpty)) {
          for (_ <- 1 to blankLines) out.println()
        } else {
          unmergedChanges += allLines.size - lines.size + 1
          out.println(diffBegMarker)
          diff.foreach(out.println)
          out.println(diffEndMarker)
        }
        rec(rest.tail, if (hasBlankLines) defaultMode else mode)
      // process block of text and show output - type, expressions, errors
      case l :: ls =>
        val blockLineNum = (allLines.size - lines.size) + 1
        
        val block = (l :: ls.takeWhile(l => l.nonEmpty && !(
          l.startsWith(outputMarker)
          || l.startsWith(diffBegMarker)
          // || l.startsWith(oldOutputMarker)
        ))).toIndexedSeq
        block.foreach(out.println)
        val processedBlock = if (file.ext =:= "fun") block.map(_ + "\n") else MLParser.addTopLevelSeparators(block)
        val processedBlockStr = processedBlock.mkString
        val fph = new FastParseHelpers(block)
        val globalStartLineNum = allLines.size - lines.size + 1
        
        var totalTypeErrors = 0
        var totalParseErrors = 0
        var totalWarnings = 0
        var totalRuntimeErrors = 0
        var totalCodeGenErrors = 0
        
        // report errors and warnings
        def report(diags: Ls[mlscript.Diagnostic], output: Str => Unit = output): Unit = {
          diags.foreach { diag =>
            val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
            val headStr = diag match {
              case ErrorReport(msg, loco, src) =>
                src match {
                  case Diagnostic.Lexing =>
                    totalParseErrors += 1
                    s"╔══[LEXICAL ERROR] "
                  case Diagnostic.Parsing =>
                    totalParseErrors += 1
                    s"╔══[PARSE ERROR] "
                  case _ => // TODO customize too
                    totalTypeErrors += 1
                    s"╔══[ERROR] "
                }
              case WarningReport(msg, loco, src) =>
                totalWarnings += 1
                s"╔══[WARNING] "
            }
            val lastMsgNum = diag.allMsgs.size - 1
            var globalLineNum = blockLineNum  // solely used for reporting useful test failure messages
            diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
              val isLast = msgNum =:= lastMsgNum
              val msgStr = msg.showIn(sctx)
              if (msgNum =:= 0) output(headStr + msgStr)
              else output(s"${if (isLast && loco.isEmpty) "╙──" else "╟──"} ${msgStr}")
              if (loco.isEmpty && diag.allMsgs.size =:= 1) output("╙──")
              loco.foreach { loc =>
                val (startLineNum, startLineStr, startLineCol) =
                  loc.origin.fph.getLineColAt(loc.spanStart)
                if (globalLineNum =:= 0) globalLineNum += startLineNum - 1
                val (endLineNum, endLineStr, endLineCol) =
                  loc.origin.fph.getLineColAt(loc.spanEnd)
                var l = startLineNum
                var c = startLineCol
                while (l <= endLineNum) {
                  val globalLineNum = loc.origin.startLineNum + l - 1
                  val relativeLineNum = globalLineNum - blockLineNum + 1
                  val shownLineNum =
                    if (showRelativeLineNums && relativeLineNum > 0) s"l.+$relativeLineNum"
                    else "l." + globalLineNum
                  val prepre = "║  "
                  val pre = s"$shownLineNum: "
                  val curLine = loc.origin.fph.lines(l - 1)
                  output(prepre + pre + "\t" + curLine)
                  val tickBuilder = new StringBuilder()
                  tickBuilder ++= (
                    (if (isLast && l =:= endLineNum) "╙──" else prepre)
                    + " " * pre.length + "\t" + " " * (c - 1))
                  val lastCol = if (l =:= endLineNum) endLineCol else curLine.length + 1
                  while (c < lastCol) { tickBuilder += ('^'); c += 1 }
                  if (c =:= startLineCol) tickBuilder += ('^')
                  output(tickBuilder.toString)
                  c = 1
                  l += 1
                }
              }
            }
            if (diag.allMsgs.isEmpty) output("╙──")
            
            if (!mode.fixme) {
              if (!allowTypeErrors
                  && !mode.expectTypeErrors && diag.isInstanceOf[ErrorReport] && diag.source =:= Diagnostic.Typing)
                failures += globalLineNum
              if (!allowParseErrors
                  && !mode.expectParseErrors && diag.isInstanceOf[ErrorReport] && (diag.source =:= Diagnostic.Lexing || diag.source =:= Diagnostic.Parsing))
                failures += globalLineNum
              if (!allowTypeErrors && !allowParseErrors
                  && !mode.expectWarnings && diag.isInstanceOf[WarningReport])
                failures += globalLineNum
            }
            
            ()
          }
        }
        
        val raise: typer.Raise = d => report(d :: Nil)
        
        // try to parse block of text into mlscript ast
        val ans = try {
          if (newParser || basePath.headOption.contains("compiler")) {
            
            val origin = Origin(testName, globalStartLineNum, fph)
            val lexer = new NewLexer(origin, raise, dbg = mode.dbgParsing)
            
            val tokens = lexer.bracketedTokens
            
            if (mode.showParse || mode.dbgParsing || parseOnly)
              output(NewLexer.printTokens(tokens))
            
            val p = new NewParser(origin, tokens, raise, dbg = mode.dbgParsing, N) {
              def doPrintDbg(msg: => Str): Unit = if (dbg) output(msg)
            }
            val res = p.parseAll(p.typingUnit)
            
            if (parseOnly)
              output("Parsed: " + res.show)
            
            postProcess(mode, basePath, testName, res).foreach(output)
            
            if (parseOnly)
              Success(Pgrm(Nil), 0)
            else
              Success(Pgrm(res.entities), 0)
            
          }
          else parse(processedBlockStr, p =>
            if (file.ext =:= "fun") new Parser(Origin(testName, globalStartLineNum, fph)).pgrm(p)
            else new MLParser(Origin(testName, globalStartLineNum, fph)).pgrm(p),
            verboseFailures = true
          )
        } match {
          case f: Failure =>
            val Failure(lbl, index, extra) = f
            val (lineNum, lineStr, col) = fph.getLineColAt(index)
            val globalLineNum = (allLines.size - lines.size) + lineNum
            if (!mode.expectParseErrors && !mode.fixme)
              failures += globalLineNum
            output("/!\\ Parse error: " + extra.trace().msg +
              s" at l.$globalLineNum:$col: $lineStr")
            
          // successfully parsed block into a valid syntactically valid program
          case Success(p, index) =>
            if (mode.expectParseErrors && !newParser)
              failures += blockLineNum
            if (mode.showParse || mode.dbgParsing) output("Parsed: " + p)
            // if (mode.isDebugging) typer.resetState()
            if (mode.stats) typer.resetStats()
            typer.dbg = mode.dbg
            typer.dbgUCS = mode.dbgUCS
            // typer.recordProvenances = !noProvs
            typer.recordProvenances = !noProvs && !mode.dbg && !mode.dbgSimplif || mode.explainErrors
            typer.generalizeCurriedFunctions = generalizeCurriedFunctions
            typer.approximateNegativeFunction = approximateNegativeFunction
            typer.distributeForalls = distributeForalls
            typer.noCycleCheck = noCycleCheck
            typer.noRecursiveTypes = noRecursiveTypes
            typer.constrainedTypes = constrainedTypes
            typer.generalizeArguments = generalizeArguments
            typer.irregularTypes = irregularTypes
            typer.verbose = mode.verbose
            typer.explainErrors = mode.explainErrors
            stdout = mode.stdout
            typer.preciselyTypeRecursion = mode.preciselyTypeRecursion
            
            val (diags, (typeDefs, stmts)) = p.desugared
            report(diags)
            
            if (mode.showParse) {
              typeDefs.foreach(td => output("Desugared: " + td))
              stmts.foreach { s =>
                output("Desugared: " + s)
                output("AST: " + mlscript.codegen.Helpers.inspect(s))
              }
            }
            
            val oldCtx = ctx
            ctx = 
              // if (newParser) typer.typeTypingUnit(tu)
              // else 
              typer.processTypeDefs(typeDefs)(ctx, raise)
            
            def getType(ty: typer.SimpleType, pol: Opt[Bool], removePolarVars: Bool = true): Type = {
              if (mode.isDebugging) output(s"⬤ Typed as: $ty")
              if (mode.isDebugging) output(s" where: ${ty.showBounds}")
              typer.dbg = mode.dbgSimplif
              if (mode.noSimplification) typer.expandType(ty)(ctx)
              else {
                object SimplifyPipeline extends typer.SimplifyPipeline {
                  def debugOutput(msg: => Str): Unit =
                    if (mode.dbgSimplif) output(msg)
                }
                val sim = SimplifyPipeline(ty, pol, removePolarVars)(ctx)
                val exp = typer.expandType(sim)(ctx)
                if (mode.dbgSimplif) output(s"⬤ Expanded: ${exp}")
                def stripPoly(pt: PolyType): Type =
                  pt.targs.filterNot(_.isRight) match {
                    case Nil => pt.body
                    case tps => PolyType(tps, pt.body)
                  }
                exp match {
                  // * Strip top-level implicitly-quantified type variables
                  case pt: PolyType => stripPoly(pt)
                  case Constrained(pt: PolyType, bs, cs) => Constrained(stripPoly(pt), bs, cs)
                  case ty => ty
                }
              }
            }
            // initialize ts typegen code builder and
            // declare all type definitions for current block
            val tsTypegenCodeBuilder = new TsTypegenCodeBuilder()
            if (mode.generateTsDeclarations) {
              typeDefs.iterator.filter(td =>
                ctx.tyDefs.contains(td.nme.name) && !oldCtx.tyDefs.contains(td.nme.name)
              ).foreach(td => tsTypegenCodeBuilder.declareTypeDef(td))
            }

            val curBlockTypeDefs = typeDefs
              // add check from process type def block below
              .flatMap(td => if (!oldCtx.tyDefs.contains(td.nme.name)) ctx.tyDefs.get(td.nme.name) else None)
            
            // activate typer tracing if variance debugging is on and then set it back
            // this makes it possible to debug variance in isolation
            var temp = typer.dbg
            typer.dbg = mode.debugVariance
            typer.computeVariances(curBlockTypeDefs, ctx)
            typer.dbg = temp
            val varianceWarnings: MutMap[TypeName, Ls[TypeName]] = MutMap()

            // show the result of type inference for each processed type def
            typeDefs.foreach(td =>
              // check if type def is not previously defined
              if (ctx.tyDefs.contains(td.nme.name)
                  && !oldCtx.tyDefs.contains(td.nme.name)) {
                  // ^ it may not end up being defined if there's an error

                val tn = td.nme.name
                val ttd = ctx.tyDefs(tn)
                val tvv = ttd.tvarVariances.getOrElse(die)

                // generate warnings for bivariant type variables
                val bivariantTypeVars = ttd.tparamsargs.iterator.filter{ case (tname, tvar) =>
                  tvv.get(tvar).contains(typer.VarianceInfo.bi)
                }.map(_._1).toList
                if (!bivariantTypeVars.isEmpty) {
                  varianceWarnings.put(td.nme, bivariantTypeVars)
                }
                
                val params = if (!ttd.tparamsargs.isEmpty)
                    SourceCode.horizontalArray(ttd.tparamsargs.map{ case (tname, tvar) =>
                      val tvarVariance = tvv.getOrElse(tvar, throw new Exception(
                        s"Type variable $tvar not found in variance store ${ttd.tvarVariances} for $ttd"))
                      SourceCode(s"${tvarVariance.show}${tname.name}")
                    })
                  else
                    SourceCode("")
                output(s"Defined " + td.kind.str + " " + tn + params)

                // calculate types for all method definitions and declarations
                // only once and reuse for pretty printing and type generation
                val methodsAndTypes = (ttd.mthDecls ++ ttd.mthDefs).flatMap {
                  case m@MethodDef(_, _, Var(mn), _, rhs) =>
                    rhs.fold(
                      _ => ctx.getMthDefn(tn, mn).map(mthTy => (m, getType(mthTy.toPT, S(true)))),
                      _ => ctx.getMth(S(tn), mn).map(mthTy => (m, getType(mthTy.toPT, N)))
                    )
                }

                // pretty print method definitions
                methodsAndTypes.foreach {
                  case (MethodDef(_, _, Var(mn), _, rhs), res) =>
                    output(s"${rhs.fold(
                      _ => "Defined",  // the method has been defined
                      _ => "Declared"  // the method type has just been declared
                    )} ${tn}.${mn}: ${res.show}")
                }

                // start typegen, declare methods if any and complete typegen block
                if (mode.generateTsDeclarations) {
                  val mthDeclSet = ttd.mthDecls.iterator.map(_.nme.name).toSet
                  val methods = methodsAndTypes
                    // filter method declarations and definitions
                    // without declarations
                    .withFilter { case (mthd, _) =>
                      mthd.rhs.isRight || !mthDeclSet.contains(mthd.nme.name)
                    }
                    .map { case (mthd, mthdTy) => (mthd.nme.name, mthdTy) }

                  tsTypegenCodeBuilder.addTypeDef(td, methods)
                }
              }
            )
            
            if (!varianceWarnings.isEmpty) {
              import Message._
              val diags = varianceWarnings.iterator.map { case (tname, biVars) =>
                val warnings = biVars.map( tname => msg"${tname.name} is irrelevant and may be removed" -> tname.toLoc)
                WarningReport(msg"Type definition ${tname.name} has bivariant type parameters:" -> tname.toLoc :: warnings)
              }.toList
              report(diags)
            }
            
            // process statements and output mlscript types
            // all `Def`s and `Term`s are processed here
            // generate typescript types if generateTsDeclarations flag is
            // set in the mode
            // The tuple type means: (<stmt name>, <type>, <diagnosis>, <order>)
            val typerResults: Ls[(Str, Ls[Str], Ls[Str], Bool)] = stmts.map { stmt =>
              // Because diagnostic lines are after the typing results,
              // we need to cache the diagnostic blocks and add them to the
              // `typerResults` buffer after the statement has been processed.
              val diagnosticLines = mutable.Buffer.empty[Str]
              // We put diagnosis to the buffer in the following `Typer` routines.
              val raiseToBuffer: typer.Raise = d => {
                report(d :: Nil, diagnosticLines += _)
              }
              // Typing results are before diagnostic messages in the subsumption case.
              // We use this flag to prevent too much changes in PR #150.
              var typeBeforeDiags = false
              val typingResults: Opt[(Str, Ls[Str])] = stmt match {
                // statement only declares a new term with its type
                // but does not give a body/definition to it
                case Def(isrec, nme, R(PolyType(tps, rhs)), isByname) =>
                  typer.dbg = mode.dbg
                  
                  implicit val prov: typer.TP = typer.NoProv // TODO
                  implicit val r: typer.Raise = raise
                  
                  val ty_sch = ctx.poly { ctx =>
                    typer.typeType(rhs)(ctx, raise, vars = tps.collect {
                        case L(tp: TypeName) => tp.name -> typer.freshVar(typer.noProv/*FIXME*/, N)(1)
                      }.toMap)
                  }
                  
                  ctx += nme.name -> typer.VarSymbol(ty_sch, nme)
                  declared += nme.name -> ty_sch
                  val exp = getType(ty_sch, N)
                  if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))
                  S(nme.name -> (s"$nme: ${exp.show}" :: Nil))
                  
                // statement is defined and has a body/definition
                case d @ Def(isrec, nme, L(rhs), isByname) =>
                  typer.dbg = mode.dbg
                  val ty_sch = typer.typeLetRhs2(isrec, nme.name, rhs)(ctx, raiseToBuffer)
                  val exp = getType(ty_sch, S(true))
                  // statement does not have a declared type for the body
                  // the inferred type must be used and stored for lookup
                  S(nme.name -> (declared.get(nme.name) match {
                    // statement has a body but it's type was not declared
                    // infer it's type and store it for lookup and type gen
                    case N =>
                      ctx += nme.name -> typer.VarSymbol(ty_sch, nme)
                      if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))
                      s"$nme: ${exp.show}" :: Nil
                      
                    // statement has a body and a declared type
                    // both are used to compute a subsumption (What is this??)
                    // the inferred type is used to for ts type gen
                    case S(sign) =>
                      ctx += nme.name -> typer.VarSymbol(sign, nme)
                      val sign_exp = getType(sign, S(false))
                      typer.dbg = mode.dbg
                      typer.subsume(ty_sch, sign)(ctx, raiseToBuffer, typer.TypeProvenance(d.toLoc, "def definition"))
                      if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))
                      typeBeforeDiags = true
                      exp.show :: s"  <:  $nme:" :: sign_exp.show :: Nil
                  }))
                case desug: DesugaredStatement =>
                  typer.dbg = mode.dbg
                  typer.typeStatement(desug, allowPure = true)(ctx, raiseToBuffer, Map.empty, genLambdas = true) match {
                    case R(binds) =>
                      binds.map { case nme -> pty =>
                        val ptType = getType(pty, S(true))
                        ctx += nme -> typer.VarSymbol(pty, Var(nme))
                        if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(ptType, Some(nme))
                        nme -> (s"$nme: ${ptType.show}" :: Nil)
                      }
                    
                    // statements for terms that compute to a value
                    // and are not bound to a variable name
                    case L(pty) =>
                      val exp = getType(pty, S(true))
                      S(if (exp =/= TypeName("unit")) {
                        val res = "res"
                        ctx += res -> typer.VarSymbol(pty, Var(res))
                        if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, None)
                        res -> (s"res: ${exp.show}" :: Nil)
                      } else (
                        "" -> Nil
                      ))
                }
              }
              typingResults match {
                case N => ("", Nil, diagnosticLines.toList, false)
                case S(name -> typingLines) =>
                  (name, typingLines, diagnosticLines.toList, typeBeforeDiags)
              }
            }
            
            
            if (occursCheck) {
              typer.dbg = mode.dbg
              val tvs = typer.createdTypeVars.toList
              
              implicit val _ctx: typer.Ctx = ctx // Mostly for `typer.AliasOf`
              
              // if (mode.dbg)
              //   output(s"REC? ${
              //     tvs.map(tv => tv -> tv.isRecursive_$(omitTopLevel = true)(ctx))
              //       .mkString(" ")}")
              
              // * Does not keep track of recursion polarity:
              // val recs = tvs.filter(_.isRecursive_$(omitTopLevel = true)(ctx))
              
              val recs = tvs.flatMap { tv =>
                val fromLB = tv.lbRecOccs_$(omitIrrelevantVars = true) match {
                  case S(pol @ (S(true) | N)) => (tv, pol) :: Nil
                  case _ => Nil
                }
                val fromUB = tv.ubRecOccs_$(omitIrrelevantVars = true) match {
                  case S(pol @ (S(false) | N)) => (tv, pol) :: Nil
                  case _ => Nil
                }
                fromLB ::: fromUB
              }
              
              if (mode.dbg) output(s"RECs: ${recs.mkString(" ")}")
              
              val withLocs = recs.filter(_._1.prov.loco.isDefined)
              
              withLocs.find {
                case (typer.AliasOf(typer.AssignedVariable(_)), _) => false
                case _ => true
              }.orElse(withLocs.headOption).orElse(recs.headOption).foreach { case (tv, pol) =>
                import Message._
                if (mode.dbg) output("REC: " + tv + tv.showBounds)
                report(ErrorReport(
                  msg"Inferred recursive type: ${
                    getType(tv, pol = pol, removePolarVars = false).show
                  }" -> tv.prov.loco :: Nil) :: Nil)
              }
              
              typer.dbg = false
            }
            
            typer.createdTypeVars.clear()
            
            
            import JSTestBackend._
            
            val executionResults: Result \/ Ls[(ReplHost.Reply, Str)] = if (!allowTypeErrors &&
                file.ext =:= "mls" && !mode.noGeneration && !noJavaScript) {
              import codeGenTestHelpers._
              backend(p, mode.allowEscape) match {
                case testCode @ TestCode(prelude, queries) => {
                  // Display the generated code.
                  if (mode.showGeneratedJS) showGeneratedCode(testCode)
                  // Execute code.
                  if (!mode.noExecution) {
                    val preludeReply = if (prelude.isEmpty) N else S(host.execute(prelude.mkString(" ")))
                    if (mode.showRepl) showReplPrelude(prelude, preludeReply, blockLineNum)
                    val replies = queries.map {
                      case CodeQuery(preludeLines, codeLines, resultName) =>
                        host.query(preludeLines.mkString, codeLines.mkString, resultName)
                      case AbortedQuery(reason) => (ReplHost.Unexecuted(reason), "")
                      case EmptyQuery => (ReplHost.Empty, "")
                    }
                    if (mode.showRepl) showReplContent(queries, replies)
                    R(replies)
                  } else {
                    L(ResultNotExecuted)
                  }
                }
                case t => L(t)
              }
            } else {
              L(ResultNotExecuted)
            }

            def outputLog(log: String): Unit = {
              val loglines = log.split('\n').iterator.filter(_.nonEmpty)
              if (loglines.nonEmpty) {
                output("// Output")
                loglines.foreach(output)
              }
            }
            
            // If code generation fails, show the error message.
            executionResults match {
              case R(replies) =>
                val replyQueue = mutable.Queue.from(replies)
                typerResults.foreach { case (name, typingLines, diagnosticLines, typeBeforeDiags) =>
                  if (typeBeforeDiags) {
                    typingLines.foreach(output)
                    diagnosticLines.foreach(output)
                  } else {
                    diagnosticLines.foreach(output)
                    typingLines.foreach(output)
                  }
                  val prefixLength = name.length
                  replyQueue.headOption.foreach { case (head, log) =>
                    head match {
                      case ReplHost.Error(isSyntaxError, content) =>
                        // We don't expect type errors nor FIXME.
                        if (!mode.expectTypeErrors && !mode.fixme) {
                          // We don't expect code generation errors and it is.
                          if (!mode.expectCodeGenErrors && isSyntaxError)
                            failures += blockLineNum
                          // We don't expect runtime errors and it's a runtime error.
                          if (!mode.expectRuntimeErrors && !allowRuntimeErrors && !isSyntaxError)
                            failures += blockLineNum
                        }
                        if (isSyntaxError) {
                          // If there is syntax error in the generated code,
                          // it should be a code generation error.
                          output("Syntax error:")
                          totalCodeGenErrors += 1
                        } else { // Otherwise, it is a runtime error.
                          output("Runtime error:")
                          totalRuntimeErrors += 1
                        }
                        content.linesIterator.foreach { s => output("  " + s) }
                      case ReplHost.Unexecuted(reason) =>
                        output(" " * prefixLength + "= <no result>")
                        output(" " * (prefixLength + 2) + reason)
                      case ReplHost.Result(result, _) =>
                        result.linesIterator.zipWithIndex.foreach { case (line, i) =>
                          if (i =:= 0) output(" " * prefixLength + "= " + line)
                          else output(" " * (prefixLength + 2) + line)
                        }
                      case ReplHost.Empty =>
                        output(" " * prefixLength + "= <missing implementation>")
                    }
                    outputLog(log)
                    replyQueue.dequeue()
                  }
                }
              case L(other) =>
                // Print type checking results first.
                typerResults.foreach { case (_, typingLines, diagnosticLines, typeBeforeDiags) =>
                  if (typeBeforeDiags) {
                    typingLines.foreach(output)
                    diagnosticLines.foreach(output)
                  } else {
                    diagnosticLines.foreach(output)
                    typingLines.foreach(output)
                  }
                }
                other match {
                  case _: TestCode => () // Impossible case.
                  case IllFormedCode(message) =>
                    totalCodeGenErrors += 1
                    if (!mode.expectCodeGenErrors && !mode.fixme)
                      failures += blockLineNum
                    output("Code generation encountered an error:")
                    output(s"  ${message}")
                  case Unimplemented(message) =>
                    output("Unable to execute the code:")
                    output(s"  ${message}")
                  case UnexpectedCrash(name, message) =>
                    if (!mode.fixme)
                      failures += blockLineNum
                    output("Code generation crashed:")
                    output(s"  $name: $message")
                  case ResultNotExecuted => ()
                }
            }
            // generate typescript typegen block
            if (mode.generateTsDeclarations) outputSourceCode(tsTypegenCodeBuilder.toSourceCode())
            
            if (mode.stats) {
              val (co, an, su, ty) = typer.stats
              output(s"constrain calls  : " + co)
              output(s"annoying  calls  : " + an)
              output(s"subtyping calls  : " + su)
              // output(s"constructed types: " + ty)
            }
            
            if (mode.expectParseErrors && totalParseErrors =:= 0)
              failures += blockLineNum
            if (mode.expectTypeErrors && totalTypeErrors =:= 0)
              failures += blockLineNum
            if (mode.expectWarnings && totalWarnings =:= 0)
              failures += blockLineNum
            if (mode.expectCodeGenErrors && totalCodeGenErrors =:= 0)
              failures += blockLineNum
            if (mode.expectRuntimeErrors && totalRuntimeErrors =:= 0)
              failures += blockLineNum
        } catch {
          case oh_noes: ThreadDeath => throw oh_noes
          case err: Throwable =>
            if (!mode.fixme)
              failures += allLines.size - lines.size
            // err.printStackTrace(out)
            output("/!!!\\ Uncaught error: " + err +
              err.getStackTrace().take(
                if (mode.fullExceptionStack) Int.MaxValue
                else if (mode.fixme || err.isInstanceOf[StackOverflowError]) 0
                else 10
              ).map("\n" + "\tat: " + _).mkString)
        } finally {
          typer.dbg = false
          typer.verbose = false
        }
        rec(lines.drop(block.size), mode)
      case Nil =>
    }

    try rec(allLines, defaultMode) finally {
      out.close()
      host.terminate()
    }
    val testFailed = failures.nonEmpty || unmergedChanges.nonEmpty
    val result = strw.toString
    val endTime = System.nanoTime()
    val timeStr = (((endTime - beginTime) / 1000 / 100).toDouble / 10.0).toString
    val testColor = if (testFailed) Console.RED else Console.GREEN
    
    val resStr = s"${" " * (35 - testStr.size)}${testColor}${
      " " * (6 - timeStr.size)}$timeStr  ms${Console.RESET}"
    
    if (inParallel) println(s"${Console.CYAN}Processed${Console.RESET}  $testStr$resStr")
    else println(resStr)
    
    if (result =/= fileContents) {
      println(s"! Updated $file")
      os.write.over(file, result)
    }
    
    if (testFailed)
      if (unmergedChanges.nonEmpty)
        fail(s"Unmerged non-output changes around: " + unmergedChanges.map("\n\t"+file.segments.toList.last+":"+_).mkString(", "))
      else fail(s"Unexpected diagnostics (or lack thereof) at: " + failures.distinct.map("\n\t"+file.segments.toList.last+":"+_).mkString(", "))
    
  }}
}

object DiffTests {
  
  private val TimeLimit =
    if (sys.env.get("CI").isDefined) Span(60, Seconds)
    else Span(30, Seconds)
  
  private val pwd = os.pwd
  private val dir = pwd/"shared"/"src"/"test"/"diff"
  
  private val allFiles = os.walk(dir).filter(_.toIO.isFile)
  
  private val validExt = Set("fun", "mls")
  
  // Aggregate unstaged modified files to only run the tests on them, if there are any
  private val modified: Set[os.RelPath] =
    try os.proc("git", "status", "--porcelain", dir).call().out.lines().iterator.flatMap { gitStr =>
      println(" [git] " + gitStr)
      val prefix = gitStr.take(2)
      val filePath = os.RelPath(gitStr.drop(3))
      if (prefix =:= "A " || prefix =:= "M " || prefix =:= "R " || prefix =:= "D ")
        N // * Disregard modified files that are staged
      else S(filePath)
    }.toSet catch {
      case err: Throwable => System.err.println("/!\\ git command failed with: " + err)
      Set.empty
    }
  
  // Allow overriding which specific tests to run, sometimes easier for development:
  private val focused = Set[Str](
    // "LetRec"
    // "Ascribe",
    // "Repro",
    // "RecursiveTypes",
    // "Simple",
    // "Inherit",
    // "Basics",
    // "Paper",
    // "Negations",
    // "RecFuns",
    // "With",
    // "Annoying",
    // "Tony",
    // "Lists",
    // "Traits",
    // "BadTraits",
    // "TraitMatching",
    // "Subsume",
    // "Methods",
  ).map(os.RelPath(_))
  // private def filter(name: Str): Bool =
  def filter(file: os.RelPath): Bool = {
    if (focused.nonEmpty) focused(file) else modified(file) || modified.isEmpty &&
      true
      // name.startsWith("new/")
      // file.segments.toList.init.lastOption.contains("parser")
  }
}
