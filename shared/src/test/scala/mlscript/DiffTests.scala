package mlscript

import fastparse._
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line
import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap}
import scala.collection.immutable
import mlscript.utils._, shorthands._
import mlscript.JSTestBackend.IllFormedCode
import mlscript.JSTestBackend.Unimplemented
import mlscript.JSTestBackend.UnexpectedCrash
import mlscript.JSTestBackend.TestCode
import mlscript.codegen.typescript.TsTypegenCodeBuilder
import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}


class DiffTests
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
  with TimeLimitedTests
{
  
  
  /**  Hook for dependent projects, like the monomorphizer. */
  def postProcess(basePath: Ls[Str], testName: Str, unit: TypingUnit): Ls[Str] = Nil
  
  
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
      println(s"!! Test at $testThread has run out out time !! stopping...")
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
    val diffEndMarker = ">>>>>>>"
    
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
      override def funkyTuples = file.ext =:= "fun"
      // override def emitDbg(str: String): Unit = if (stdout) System.out.println(str) else output(str)
      override def emitDbg(str: String): Unit = output(str)
    }
    var ctx: typer.Ctx = typer.Ctx.init
    var declared: Map[Str, typer.PolymorphicType] = Map.empty
    val failures = mutable.Buffer.empty[Int]
    val unmergedChanges = mutable.Buffer.empty[Int]
    
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
      fullExceptionStack: Bool = false,
      stats: Bool = false,
      stdout: Bool = false,
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
    ) {
      def isDebugging: Bool = dbg || dbgSimplif
    }
    val defaultMode = Mode()
    
    var parseOnly = basePath.headOption.contains("parser") || basePath.headOption.contains("mono")
    var allowTypeErrors = false
    var allowParseErrors = false // TODO use
    var showRelativeLineNums = false
    var noJavaScript = false
    var noProvs = false
    var allowRuntimeErrors = false
    var newParser = basePath.headOption.contains("parser") || basePath.headOption.contains("mono")

    val backend = new JSTestBackend()
    val host = ReplHost()
    
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
          case "s" => mode.copy(fullExceptionStack = true)
          case "v" | "verbose" => mode.copy(verbose = true)
          case "ex" | "explain" => mode.copy(expectTypeErrors = true, explainErrors = true)
          case "ns" | "no-simpl" => mode.copy(noSimplification = true)
          case "stats" => mode.copy(stats = true)
          case "stdout" => mode.copy(stdout = true)
          case "ParseOnly" => parseOnly = true; mode
          case "AllowTypeErrors" => allowTypeErrors = true; mode
          case "AllowParseErrors" => allowParseErrors = true; mode
          case "AllowRuntimeErrors" => allowRuntimeErrors = true; mode
          case "ShowRelativeLineNums" => showRelativeLineNums = true; mode
          case "NewParser" => newParser = true; mode
          case "NoJS" => noJavaScript = true; mode
          case "NoProvs" => noProvs = true; mode
          case "ne" => mode.copy(noExecution = true)
          case "ng" => mode.copy(noGeneration = true)
          case "js" => mode.copy(showGeneratedJS = true)
          case "ts" => mode.copy(generateTsDeclarations = true)
          case "dv" => mode.copy(debugVariance = true)
          case "ge" => mode.copy(expectCodeGenErrors = true)
          case "re" => mode.copy(expectRuntimeErrors = true)
          case "ShowRepl" => mode.copy(showRepl = true)
          case "escape" => mode.copy(allowEscape = true)
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
        if (diff.forall(l => l.startsWith(outputMarker) || l.startsWith(diffMidMarker) || l.isEmpty)) {
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
        def report(diags: Ls[mlscript.Diagnostic]): Unit = {
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
                  out.print(outputMarker
                    + (if (isLast && l =:= endLineNum) "╙──" else prepre)
                    + " " * pre.length + "\t" + " " * (c - 1))
                  val lastCol = if (l =:= endLineNum) endLineCol else curLine.length + 1
                  while (c < lastCol) { out.print('^'); c += 1 }
                  if (c =:= startLineCol) out.print('^')
                  out.println
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
          if (newParser || basePath.headOption.contains("mono")) {
            
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
            
            postProcess(basePath, testName, res).foreach(output)
            
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
            // typer.recordProvenances = !noProvs
            typer.recordProvenances = !noProvs && !mode.dbg && !mode.dbgSimplif || mode.explainErrors
            typer.verbose = mode.verbose
            typer.explainErrors = mode.explainErrors
            stdout = mode.stdout
            
            val (diags, (typeDefs, stmts)) = p.desugared
            report(diags)
            
            if (mode.showParse) {
              typeDefs.foreach(td => output("Desugared: " + td))
              stmts.foreach(s => output("Desugared: " + s))
            }
            
            val oldCtx = ctx
            ctx = 
              // if (newParser) typer.typeTypingUnit(tu)
              // else 
              typer.processTypeDefs(typeDefs)(ctx, raise)
            
            def getType(ty: typer.TypeScheme): Type = {
              val wty = ty.uninstantiatedBody
              if (mode.isDebugging) output(s"⬤ Typed as: $wty")
              if (mode.isDebugging) output(s" where: ${wty.showBounds}")
              typer.dbg = mode.dbgSimplif
              if (mode.noSimplification) typer.expandType(wty)(ctx)
              else {
                object SimplifyPipeline extends typer.SimplifyPipeline {
                  def debugOutput(msg: => Str): Unit =
                    if (mode.dbgSimplif) output(msg)
                }
                val sim = SimplifyPipeline(wty)(ctx)
                val exp = typer.expandType(sim)(ctx)
                if (mode.dbgSimplif) output(s"⬤ Expanded: ${exp}")
                exp
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
                    }.toList).toString()
                  else
                    SourceCode("")
                output(s"Defined " + td.kind.str + " " + tn + params)

                // calculate types for all method definitions and declarations
                // only once and reuse for pretty printing and type generation
                val methodsAndTypes = (ttd.mthDecls ++ ttd.mthDefs).flatMap {
                  case m@MethodDef(_, _, Var(mn), _, rhs) =>
                    rhs.fold(
                      _ => ctx.getMthDefn(tn, mn).map(mthTy => (m, getType(mthTy.toPT))),
                      _ => ctx.getMth(S(tn), mn).map(mthTy => (m, getType(mthTy.toPT)))
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
              val diags = varianceWarnings.map{ case (tname, biVars) =>
                val warnings = biVars.map( tname => msg"${tname.name} is irrelevant and may be removed" -> tname.toLoc).toList
                WarningReport(msg"Type definition ${tname.name} has bivariant type parameters:" -> tname.toLoc :: warnings)
              }.toList
              report(diags)
            }

            final case class ExecutedResult(var replies: Ls[ReplHost.Reply]) extends JSTestBackend.Result {
              def showFirst(prefixLength: Int): Unit = replies match {
                case ReplHost.Error(isSyntaxError, content) :: rest =>
                  if (!(mode.expectTypeErrors
                      || mode.expectRuntimeErrors
                      || allowRuntimeErrors
                      || mode.fixme
                  )) failures += blockLineNum
                  totalRuntimeErrors += 1
                  output((if (isSyntaxError) "Syntax" else "Runtime") + " error:")
                  content.linesIterator.foreach { s => output("  " + s) }
                  replies = rest
                case ReplHost.Unexecuted(reason) :: rest =>
                  output(" " * prefixLength + "= <no result>")
                  output(" " * (prefixLength + 2) + reason)
                  replies = rest
                case ReplHost.Result(result, _) :: rest =>
                  result.linesIterator.zipWithIndex.foreach { case (line, i) =>
                    if (i =:= 0) output(" " * prefixLength + "= " + line)
                    else output(" " * (prefixLength + 2) + line)
                  }
                  replies = rest
                case ReplHost.Empty :: rest =>
                  output(" " * prefixLength + "= <missing implementation>")
                  replies = rest
                case Nil => ()
              }
            }
            
            var results: JSTestBackend.Result = if (!allowTypeErrors &&
                file.ext =:= "mls" && !mode.noGeneration && !noJavaScript) {
              backend(p, mode.allowEscape) match {
                case TestCode(prelude, queries) => {
                  // Display the generated code.
                  if (mode.showGeneratedJS) {
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
                  // Execute code.
                  if (!mode.noExecution) {
                    if (mode.showRepl) {
                      output(s"┌ Block at ${file.last}:${blockLineNum}")
                    }
                    // Execute the prelude code.
                    prelude match {
                      case Nil => {
                        if (mode.showRepl) {
                          output(s"├── No prelude")
                          if (queries.isEmpty)
                            output(s"└── No queries")
                        }
                      }
                      case lines => {
                        val preludeReply = host.execute(lines mkString " ")
                        if (mode.showRepl) {
                          output(s"├─┬ Prelude")
                          output(s"│ ├── Code")
                          lines.iterator.foreach { line => output(s"│ │   $line") }
                          // Display successful results in multiple lines.
                          // Display other results in single line.
                          preludeReply match {
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
                      }
                    }
                    if (mode.showRepl && queries.isEmpty) {
                      output(s"└── No queries")
                    }
                    // Send queries to the host.
                    ExecutedResult(queries.zipWithIndex.map {
                      case (JSTestBackend.CodeQuery(preludeLines, codeLines, res), i) =>
                        val prelude = preludeLines.mkString
                        val code = codeLines.mkString
                        val p0 = if (i + 1 == queries.length) "  " else "│ "
                        if (mode.showRepl) {
                          val p1 = if (i + 1 == queries.length) "└─" else "├─"
                          output(s"$p1┬ Query ${i + 1}/${queries.length}")
                          output(s"$p0├── Prelude: ${if (preludeLines.isEmpty) "<empty>" else prelude}")
                          output(s"$p0├── Code: ${code}")
                        }
                        val reply = host.query(prelude, code, res)
                        if (mode.showRepl) {
                          // Show the intermediate reply if possible.
                          reply match {
                            case ReplHost.Result(_, Some(intermediate)) =>
                              output(s"$p0├── Intermediate: $intermediate")
                            case _ => ()
                          }
                          val p1 = if (i + 1 == queries.length) "  └──" else s"$p0└──"
                          output(s"$p1 Reply: $reply")
                        }
                        reply
                      case (JSTestBackend.AbortedQuery(reason), i) =>
                        if (mode.showRepl) {
                          val prefix = if (i + 1 == queries.length) "└──" else "├──"
                          output(s"$prefix Query ${i + 1}/${queries.length}: <aborted: $reason>")
                        }
                        ReplHost.Unexecuted(reason)
                      case (JSTestBackend.EmptyQuery, i) =>
                        if (mode.showRepl) {
                          val prefix = if (i + 1 == queries.length) "└──" else "├──"
                          output(s"$prefix Query ${i + 1}/${queries.length}: <empty>")
                        }
                        ReplHost.Empty
                    })
                  } else {
                    JSTestBackend.ResultNotExecuted
                  }
                }
                case t => t
              }
            } else {
              JSTestBackend.ResultNotExecuted
            }

            def showFirstResult(prefixLength: Int) = results match {
              case t: ExecutedResult => t.showFirst(prefixLength)
              case _ => ()
            }
            
            // process statements and output mlscript types
            // all `Def`s and `Term`s are processed here
            // generate typescript types if generateTsDeclarations flag is
            // set in the mode
            stmts.foreach {
              // statement only declares a new term with its type
              // but does not give a body/definition to it
              case Def(isrec, nme, R(PolyType(tps, rhs)), isByname) =>
                typer.dbg = mode.dbg
                val ty_sch = typer.PolymorphicType(0,
                  typer.typeType(rhs)(ctx.nextLevel, raise,
                    vars = tps.map(tp => tp.name -> typer.freshVar(typer.noProv/*FIXME*/)(1)).toMap))
                ctx += nme.name -> ty_sch
                declared += nme.name -> ty_sch
                val exp = getType(ty_sch)
                output(s"$nme: ${exp.show}")
                showFirstResult(nme.name.length())
                if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))

              // statement is defined and has a body/definition
              case d @ Def(isrec, nme, L(rhs), isByname) =>
                typer.dbg = mode.dbg
                val ty_sch = typer.typeLetRhs(isrec, nme.name, rhs)(ctx, raise)
                val exp = getType(ty_sch)
                // statement does not have a declared type for the body
                // the inferred type must be used and stored for lookup
                declared.get(nme.name) match {
                  // statement has a body but it's type was not declared
                  // infer it's type and store it for lookup and type gen
                  case N =>
                    ctx += nme.name -> ty_sch
                    output(s"$nme: ${exp.show}")
                    if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))
                    
                  // statement has a body and a declared type
                  // both are used to compute a subsumption (What is this??)
                  // the inferred type is used to for ts type gen
                  case S(sign) =>
                    ctx += nme.name -> sign
                    val sign_exp = getType(sign)
                    output(exp.show)
                    output(s"  <:  $nme:")
                    output(sign_exp.show)
                    typer.dbg = mode.dbg
                    typer.subsume(ty_sch, sign)(ctx, raise, typer.TypeProvenance(d.toLoc, "def definition"))
                    if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))
                }
                showFirstResult(nme.name.length())
              case desug: DesugaredStatement =>
                var prefixLength = 0
                typer.dbg = mode.dbg
                typer.typeStatement(desug, allowPure = true)(ctx, raise) match {
                  // when does this happen??
                  case R(binds) =>
                    binds.foreach {
                      case (nme, pty) =>
                        val ptType = getType(pty)
                        ctx += nme -> pty
                        output(s"$nme: ${ptType.show}")
                        prefixLength = nme.length()
                        if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(ptType, Some(nme))
                    }

                  // statements for terms that compute to a value
                  // and are not bound to a variable name
                  case L(pty) =>
                    val exp = getType(pty)
                    if (exp =/= TypeName("unit")) {
                      ctx += "res" -> pty
                      output(s"res: ${exp.show}")
                      if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, None)
                      prefixLength = 3
                    }
                }
                showFirstResult(prefixLength)
            }

            // If code generation fails, show the error message.
            results match {
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
              case _ => ()
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
                else if (mode.fixme) 0
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
        fail(s"Unmerged non-output changes around: " + unmergedChanges.map("l."+_).mkString(", "))
      else fail(s"Unexpected diagnostics (or lack thereof) at: " + failures.map("l."+_).mkString(", "))
    
  }}
}

object DiffTests {
  
  private val TimeLimit =
    if (sys.env.get("CI").isDefined) Span(25, Seconds)
    else Span(5, Seconds)
  
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
      if (prefix =:= "A " || prefix =:= "M ") N else S(filePath) // disregard modified files that are staged
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
  private def filter(file: os.RelPath): Bool = {
    if (focused.nonEmpty) focused(file) else modified(file) || modified.isEmpty &&
      true
      // name.startsWith("new/")
      // file.segments.toList.init.lastOption.contains("parser")
  }
}
