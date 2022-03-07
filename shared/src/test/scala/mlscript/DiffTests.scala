package mlscript

import fastparse._
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line
import ammonite.ops._
import scala.collection.mutable
import scala.collection.immutable
import mlscript.utils._, shorthands._
import mlscript.JSTestBackend.IllFormedCode
import mlscript.JSTestBackend.Unimplemented
import mlscript.JSTestBackend.UnexpectedCrash
import mlscript.JSTestBackend.TestCode
import mlscript.codegen.typescript.TsTypegenCodeBuilder

class DiffTests extends org.scalatest.funsuite.AnyFunSuite with org.scalatest.ParallelTestExecution {
  
  import DiffTests._
  files.foreach { file => val fileName = file.baseName; test(fileName) {
    
    val buf = mutable.ArrayBuffer.empty[Char]
    buf ++= s"Processed  $fileName"
    // For some reason the color is sometimes wiped out when the line is later updated not in iTerm3:
    // print(s"${Console.CYAN}Processing $fileName${Console.RESET}... ")
    
    val beginTime = System.nanoTime()
    
    val outputMarker = "//│ "
    // val oldOutputMarker = "/// "
    
    val diffBegMarker = "<<<<<<<"
    val diffMidMarker = "======="
    val diffEndMarker = ">>>>>>>"
    
    val fileContents = read(file)
    val allLines = fileContents.splitSane('\n').toList
    val strw = new java.io.StringWriter
    val out = new java.io.PrintWriter(strw)
    def output(str: String) = out.println(outputMarker + str)
    def outputSourceCode(code: SourceCode) = code.lines.foreach{line => out.println(outputMarker + line.toString())}
    val allStatements = mutable.Buffer.empty[DesugaredStatement]
    var stdout = false
    val typer = new Typer(dbg = false, verbose = false, explainErrors = false) {
      override def funkyTuples = file.ext =:= "fun"
      override def emitDbg(str: String): Unit = if (stdout) System.out.println(str) else output(str)
    }
    var ctx: typer.Ctx = typer.Ctx.init
    var declared: Map[Str, typer.PolymorphicType] = Map.empty
    val failures = mutable.Buffer.empty[Int]
    val unmergedChanges = mutable.Buffer.empty[Int]
    
    case class Mode(
      expectTypeErrors: Bool, expectWarnings: Bool, expectParseErrors: Bool,
      fixme: Bool, showParse: Bool, verbose: Bool, noSimplification: Bool,
      explainErrors: Bool, dbg: Bool, fullExceptionStack: Bool, stats: Bool,
      stdout: Bool, noExecution: Bool, noGeneration: Bool, showGeneratedJS: Bool,
      generateTsDeclarations: Bool, expectRuntimeErrors: Bool, showRepl: Bool, allowEscape: Bool)
    val defaultMode = Mode(false, false, false, false, false, false, false, false,
      false, false, false, false, false, false, false, false, false, false, false)
    
    var allowTypeErrors = false
    var showRelativeLineNums = false
    var noJavaScript = false
    var allowRuntimeErrors = false

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
          case "s" => mode.copy(fullExceptionStack = true)
          case "v" | "verbose" => mode.copy(verbose = true)
          case "ex" | "explain" => mode.copy(expectTypeErrors = true, explainErrors = true)
          case "ns" | "no-simpl" => mode.copy(noSimplification = true)
          case "stats" => mode.copy(stats = true)
          case "stdout" => mode.copy(stdout = true)
          case "AllowTypeErrors" => allowTypeErrors = true; mode
          case "AllowRuntimeErrors" => allowRuntimeErrors = true; mode
          case "ShowRelativeLineNums" => showRelativeLineNums = true; mode
          case "NoJS" => noJavaScript = true; mode
          case "ne" => mode.copy(noExecution = true)
          case "ng" => mode.copy(noGeneration = true)
          case "js" => mode.copy(showGeneratedJS = true)
          case "ts" => mode.copy(generateTsDeclarations = true)
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
      case line :: ls if line.isEmpty || line.startsWith("//") =>
        out.println(line)
        rec(ls, defaultMode)
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

        // try to parse block of text into mlscript ast
        val ans = try parse(processedBlockStr,
          p => if (file.ext =:= "fun") new Parser(Origin(fileName, globalStartLineNum, fph)).pgrm(p)
            else new MLParser(Origin(fileName, globalStartLineNum, fph)).pgrm(p),
          verboseFailures = true)
        match {
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
            val blockLineNum = (allLines.size - lines.size) + 1
            if (mode.expectParseErrors)
              failures += blockLineNum
            if (mode.showParse) output("Parsed: " + p)
            if (mode.dbg) typer.resetState()
            if (mode.stats) typer.resetStats()
            typer.dbg = mode.dbg
            typer.verbose = mode.verbose
            typer.explainErrors = mode.explainErrors
            stdout = mode.stdout
            
            var totalTypeErrors = 0
            var totalWarnings = 0
            var totalRuntimeErrors = 0
            
            // report errors and warnings
            def report(diags: Ls[Diagnostic]): Unit = {
              diags.foreach { diag =>
                val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
                val headStr = diag match {
                  case TypeError(msg, loco) =>
                    totalTypeErrors += 1
                    s"╔══[ERROR] "
                  case Warning(msg, loco) =>
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
                      out.println
                      c = 1
                      l += 1
                    }
                  }
                }
                if (diag.allMsgs.isEmpty) output("╙──")
                if (!allowTypeErrors && !mode.fixme && (
                    !mode.expectTypeErrors && diag.isInstanceOf[TypeError]
                  || !mode.expectWarnings && diag.isInstanceOf[Warning]
                )) failures += globalLineNum
                ()
              }
            }
            
            val raise: typer.Raise = d => report(d :: Nil)
            
            val (diags, (typeDefs, stmts)) = p.desugared
            report(diags)
            
            if (mode.showParse) {
              typeDefs.foreach(td => output("Desugared: " + td))
              stmts.foreach(s => output("Desugared: " + s))
            }
            
            val oldCtx = ctx
            ctx = typer.processTypeDefs(typeDefs)(ctx, raise)
            
            def getType(ty: typer.TypeScheme): Type = {
              val wty = ty.instantiate(0)
              if (mode.dbg) output(s"Typed as: $wty")
              if (mode.dbg) output(s" where: ${wty.showBounds}")
              if (mode.noSimplification) typer.expandType(wty, true)
              else {
                val cty = typer.canonicalizeType(wty)(ctx)
                if (mode.dbg) output(s"Canon: ${cty}")
                if (mode.dbg) output(s" where: ${cty.showBounds}")
                val sim = typer.simplifyType(cty)(ctx)
                if (mode.dbg) output(s"Type after simplification: ${sim}")
                if (mode.dbg) output(s" where: ${sim.showBounds}")
                // val exp = typer.expandType(sim)
                
                // TODO: would be better toa void having to do a second pass,
                // but would require more work:
                val reca = typer.canonicalizeType(sim)(ctx)
                if (mode.dbg) output(s"Recanon: ${reca}")
                if (mode.dbg) output(s" where: ${reca.showBounds}")
                val resim = typer.simplifyType(reca)(ctx)
                if (mode.dbg) output(s"Resimplified: ${resim}")
                if (mode.dbg) output(s" where: ${resim.showBounds}")
                val recons = typer.reconstructClassTypes(resim, true, ctx)
                if (mode.dbg) output(s"Recons: ${recons}")
                val exp = typer.expandType(recons, true)
                
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
            
            // process type definitions first
            typeDefs.foreach(td =>
              // check if type def is not previously defined
              if (ctx.tyDefs.contains(td.nme.name)
                  && !oldCtx.tyDefs.contains(td.nme.name)) {
                  // ^ it may not end up being defined if there's an error
                val tn = td.nme.name
                output(s"Defined " + td.kind.str + " " + tn)
                val ttd = ctx.tyDefs(tn)

                // pretty print method definitions
                (ttd.mthDecls ++ ttd.mthDefs).foreach {
                  case MethodDef(_, _, Var(mn), _, rhs) =>
                    rhs.fold(
                      _ => ctx.getMthDefn(tn, mn),
                      _ => ctx.getMth(S(tn), mn)
                    ).foreach(res => {
                      output(s"${rhs.fold(
                        _ => "Defined",  // the method has been defined
                        _ => "Declared"  // the method type has just been declared
                      )} ${tn}.${mn}: ${getType(res.toPT).show}")
                    })
                }

                // start typegen, declare methods if any and complete typegen block
                if (mode.generateTsDeclarations) {
                  val mthDeclSet = ttd.mthDecls.iterator.map(_.nme.name).toSet
                  val onlyMethodDef = ttd.mthDefs.filter(mthd => !mthDeclSet.contains(mthd.nme.name))
                  val methods = (ttd.mthDecls ++ onlyMethodDef).flatMap({
                    case MethodDef(_, _, Var(mn), _, rhs) =>
                      rhs.fold(
                        _ => ctx.getMthDefn(tn, mn),
                        _ => ctx.getMth(S(tn), mn),
                      ).map(res => (mn, getType(res.toPT)))
                  })

                  tsTypegenCodeBuilder.addTypeDef(td, methods)
                }
              }
            )
            
            final case class ExecutedResult(var replies: Ls[ReplHost.Reply]) extends JSTestBackend.Result {
              def showFirst(prefixLength: Int): Unit = replies match {
                case ReplHost.Error(err) :: rest =>
                  if (!(mode.expectTypeErrors
                      || mode.expectRuntimeErrors
                      || allowRuntimeErrors
                      || mode.fixme
                  )) failures += blockLineNum
                  totalRuntimeErrors += 1
                  output("Runtime error:")
                  err.split('\n') foreach { s => output("  " + s) }
                  replies = rest
                case ReplHost.Unexecuted(reason) :: rest =>
                  output(" " * prefixLength + "= <no result>")
                  output(" " * (prefixLength + 2) + reason)
                  replies = rest
                case ReplHost.Result(result) :: rest =>
                  result.split('\n').zipWithIndex foreach { case (s, i) =>
                    if (i =:= 0) output(" " * prefixLength + "= " + s)
                    else output(" " * (prefixLength + 2) + s)
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
                      case (JSTestBackend.CodeQuery(prelude, code), i) =>
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
                    prelude match {
                      case Nil => ()
                      case lines => host.execute(lines mkString " ")
                    }
                    if (mode.showRepl) {
                      println(s"Block [line: ${blockLineNum}] [file: ${file.baseName}]")
                      if (queries.isEmpty)
                        println(s"The block is empty")
                    }
                    // Send queries to the host.
                    ExecutedResult(queries.zipWithIndex.map {
                      case (JSTestBackend.CodeQuery(preludeLines, codeLines), i) =>
                        val prelude = preludeLines.mkString
                        val code = codeLines.mkString
                        if (mode.showRepl) {
                          println(s"├── Query ${i + 1}/${queries.length}")
                          println(s"│ ├── Prelude: ${if (preludeLines.isEmpty) "<empty>" else prelude}")
                          println(s"│ └── Code: ${code}")
                        }
                        val reply = host.query(prelude, code)
                        if (mode.showRepl) {
                          val prefix = if (i + 1 == queries.length) "└──" else "├──"
                          println(s"$prefix Reply ${i + 1}/${queries.length}: $reply")
                        }
                        reply
                      case (JSTestBackend.AbortedQuery(reason), i) =>
                        if (mode.showRepl) {
                          val prefix = if (i + 1 == queries.length) "└──" else "├──"
                          println(s"$prefix Query ${i + 1}/${queries.length}: <aborted: $reason>")
                        }
                        ReplHost.Unexecuted(reason)
                      case (JSTestBackend.EmptyQuery, i) =>
                        if (mode.showRepl) {
                          val prefix = if (i + 1 == queries.length) "└──" else "├──"
                          println(s"$prefix Query ${i + 1}/${queries.length}: <empty>")
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
              // statement only declares a new term with it's type
              // but does not give a body/definition to it
              case Def(isrec, nme, R(PolyType(tps, rhs))) =>
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
              case d @ Def(isrec, nme, L(rhs)) =>
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
                    typer.subsume(ty_sch, sign)(ctx, raise, typer.TypeProvenance(d.toLoc, "def definition"))
                    if (mode.generateTsDeclarations) tsTypegenCodeBuilder.addTypeGenTermDefinition(exp, Some(nme.name))
                }
                showFirstResult(nme.name.length())
              case desug: DesugaredStatement =>
                var prefixLength = 0
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
                totalRuntimeErrors += 1
                output("Code generation encountered an error:")
                output(s"  ${message}")
              case Unimplemented(message) =>
                output("Unable to execute the code:")
                output(s"  ${message}")
              case UnexpectedCrash(name, message) =>
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
            
            if (mode.expectTypeErrors && totalTypeErrors =:= 0)
              failures += blockLineNum
            if (mode.expectWarnings && totalWarnings =:= 0)
              failures += blockLineNum
            if (mode.expectRuntimeErrors && totalRuntimeErrors =:= 0)
              failures += blockLineNum
        } catch {
          case err: Throwable =>
            if (!mode.fixme)
              failures += allLines.size - lines.size
            // err.printStackTrace(out)
            output("/!!!\\ Uncaught error: " + err +
              err.getStackTrace().take(if (mode.fullExceptionStack) Int.MaxValue else 10)
                .map("\n" + outputMarker + "\tat: " + _).mkString)
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
    buf ++= s"${" " * (30 - fileName.size)}${testColor}${
      " " * (6 - timeStr.size)}$timeStr  ms${Console.RESET}\n"
    if (result =/= fileContents) {
      buf ++= s"! Updated $file\n"
      write.over(file, result)
    }
    print(buf.mkString)
    if (testFailed)
      if (unmergedChanges.nonEmpty)
        fail(s"Unmerged non-output changes around: " + unmergedChanges.map("l."+_).mkString(", "))
      else fail(s"Unexpected diagnostics (or lack thereof) at: " + failures.map("l."+_).mkString(", "))
    
  }}
}

object DiffTests {
  
  private val dir = pwd/"shared"/"src"/"test"/"diff"
  
  private val allFiles = ls.rec(dir).filter(_.isFile)
  
  private val validExt = Set("fun", "mls")
  
  // Aggregate unstaged modified files to only run the tests on them, if there are any
  private val modified: Set[Str] =
    try os.proc("git", "status", "--porcelain", dir).call().out.lines().iterator.flatMap { gitStr =>
      println(" [git] " + gitStr)
      val prefix = gitStr.take(2)
      val filePath = gitStr.drop(3)
      val fileName = RelPath(filePath).baseName
      if (prefix =:= "A " || prefix =:= "M ") N else S(fileName) // disregard modified files that are staged
    }.toSet catch {
      case err: Throwable => System.err.println("/!\\ git command failed with: " + err)
      Set.empty
    }
  
  // Allow overriding which specific tests to run, sometimes easier for development:
  private val focused = Set[Str](
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
  )
  private def filter(name: Str): Bool =
    if (focused.nonEmpty) focused(name) else modified.isEmpty || modified(name)
  
  private val files = allFiles.filter { file =>
      val fileName = file.baseName
      validExt(file.ext) && filter(fileName)
  }
  
  
  /** Helper to run NodeJS on test input. */
  final case class ReplHost() {
    import java.io.{BufferedWriter, BufferedReader, InputStreamReader, OutputStreamWriter}
    private val builder = new java.lang.ProcessBuilder()
    builder.command("node", "--interactive")
    private val proc = builder.start()

    private val stdin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream))
    private val stdout = new BufferedReader(new InputStreamReader(proc.getInputStream))
    private val stderr = new BufferedReader(new InputStreamReader(proc.getErrorStream))

    skipUntilPrompt()

    private def skipUntilPrompt(): Unit = {
      val buffer = new StringBuilder()
      while (!buffer.endsWith("\n> ")) {
        buffer.append(stdout.read().toChar)
      }
      buffer.delete(buffer.length - 3, buffer.length)
      ()
    }

    private def consumeUntilPrompt(): ReplHost.Reply = {
      val buffer = new StringBuilder()
      while (!buffer.endsWith("\n> ")) {
        buffer.append(stdout.read().toChar)
      }
      buffer.delete(buffer.length - 3, buffer.length)
      val reply = buffer.toString()
      val begin = reply.indexOf(0x200B)
      val end = reply.lastIndexOf(0x200B)
      if (begin >= 0 && end >= 0)
        // `console.log` inserts a space between every two arguments,
        // so + 1 and - 1 is necessary to get correct length.
        ReplHost.Error(reply.substring(begin + 1, end))
      else
        ReplHost.Result(reply)
    }

    private def send(code: Str, useEval: Bool = false): Unit = {
      stdin.write(
        if (useEval) "eval(" + JSLit.makeStringLiteral(code) + ")\n"
        else if (code endsWith "\n") code
        else code + "\n"
      )
      stdin.flush()
    }

    def query(prelude: Str, code: Str): ReplHost.Reply = {
      val wrapped = s"$prelude try { $code } catch (e) { console.log('\\u200B' + e + '\\u200B'); }"
      send(wrapped)
      consumeUntilPrompt() match {
        case _: ReplHost.Result =>
          send("res")
          consumeUntilPrompt()
        case t => t
      }
    }

    def execute(code: Str): Unit = {
      send(code)
      skipUntilPrompt()
    }

    def terminate(): Unit = proc.destroy()
  }

  object ReplHost {
    /**
      * The base class of all kinds of REPL replies.
      */
    sealed abstract class Reply

    final case class Result(content: Str) extends Reply {
      override def toString(): Str = s"[success] $content"
    }

    /**
      * If the query is `Empty`, we will receive this.
      */
    final object Empty extends Reply {
      override def toString(): Str = "[empty]"
    }

    /**
      * If the query is `Unexecuted`, we will receive this.
      */
    final case class Unexecuted(message: Str) extends Reply {
      override def toString(): Str = s"[unexecuted] $message"
    }

    /**
      * If the `ReplHost` captured errors, it will response with `Error`.
      */
    final case class Error(message: Str) extends Reply {
      override def toString(): Str = s"[error] $message"
    }
  }
}
