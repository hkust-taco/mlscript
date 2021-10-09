package mlscript

import fastparse._
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line
import ammonite.ops._
import scala.collection.mutable
import mlscript.utils._, shorthands._

class DiffTests extends org.scalatest.funsuite.AnyFunSuite {
  
  private val dir = pwd/"shared"/"src"/"test"/"diff"
  
  private val files = ls.rec(dir).filter(_.isFile)
  
  files.foreach { file => val fileName = file.baseName; test(fileName) {
    
    val outputMarker = "//│ "
    // val oldOutputMarker = "/// "
    
    val fileContents = read(file)
    val allLines = fileContents.splitSane('\n').toList
    val strw = new java.io.StringWriter
    val out = new java.io.PrintWriter(strw)
    def output(str: String) = out.println(outputMarker + str)
    val typer = new Typer(dbg = false, verbose = false, explainErrors = false) {
      override def emitDbg(str: String): Unit = output(str)
    }
    var ctx: typer.Ctx = typer.Ctx.init
    val failures = mutable.Buffer.empty[Int]
    
    case class Mode(
      expectTypeErrors: Bool, expectWarnings: Bool, expectParseErrors: Bool,
      fixme: Bool, showParse: Bool, verbose: Bool, noSimplification: Bool,
      explainErrors: Bool, dbg: Bool, fullExceptionStack: Bool)
    val defaultMode = Mode(false, false, false, false, false, false, false, false, false, false)
    
    var allowTypeErrors = false
    var showRelativeLineNums = false
    
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
          case "AllowTypeErrors" => allowTypeErrors = true; mode
          case "ShowRelativeLineNums" => showRelativeLineNums = true; mode
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
      case l :: ls =>
        val block = (l :: ls.takeWhile(l => l.nonEmpty && !(
          l.startsWith(outputMarker)
          // || l.startsWith(oldOutputMarker)
        ))).toIndexedSeq
        block.foreach(out.println)
        val processedBlock = if (file.ext =:= "fun") block.map(_ + "\n") else MLParser.addTopLevelSeparators(block)
        val processedBlockStr = processedBlock.mkString
        val fph = new FastParseHelpers(block)
        val globalStartLineNum = allLines.size - lines.size + 1
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
          case Success(p, index) =>
            val blockLineNum = (allLines.size - lines.size) + 1
            if (mode.expectParseErrors)
              failures += blockLineNum
            if (mode.showParse) output("Parsed: " + p)
            if (mode.dbg) typer.resetState()
            typer.dbg = mode.dbg
            typer.verbose = mode.verbose
            typer.explainErrors = mode.explainErrors
            
            var totalTypeErrors = 0
            var totalWarnings = 0
            
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
                      out.print(outputMarker + (if (isLast) "╙──" else prepre) + " " * pre.length + "\t" + " " * (c - 1))
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
            
            val oldCtx = ctx
            ctx = typer.processTypeDefs(p.typeDefs)(ctx, raise)
            
            p.typeDefs.foreach(td =>
              if (ctx.tyDefs.contains(td.nme.name)
                  && !oldCtx.tyDefs.contains(td.nme.name))
                  // ^ it may not end up being defined if there's an error
                output(s"Defined " + td.kind.str + " " + td.nme.name))
            
            def getType(ty: typer.TypeScheme): Type = {
              val wty = ty.instantiate(0).widenVar
              if (mode.dbg) output(s"Typed as: $wty")
              if (mode.dbg) output(s" where: ${wty.showBounds}")
              if (mode.noSimplification) typer.expandType(wty)
              else {
                val com = typer.compactType(wty)
                if (mode.dbg) output(s"Compact type before simplification: ${com}")
                val sim = typer.simplifyType(com)
                if (mode.dbg) output(s"Compact type after simplification: ${sim}")
                val exp = typer.expandCompactType(sim)
                exp
              }
            }
            
            p.otherTops.foreach {
              case s: Statement =>
                val (diags, desug) = s.desugared
                report(diags)
                typer.typeStatement(desug, allowPure = true)(ctx, raise) match {
                  case R(binds) =>
                    binds.foreach {
                      case (nme, pty) =>
                        ctx += nme -> pty
                        output(s"$nme: ${getType(pty).show}")
                    }
                  case L(pty) =>
                    val exp = getType(pty)
                    if (exp =/= Primitive("unit")) {
                      ctx += "res" -> pty
                      output(s"res: ${exp.show}")
                    }
                }
              case Def(isrec, nme, rhs) =>
                val ty_sch = typer.typeLetRhs(isrec, nme, rhs)(ctx, raise)
                ctx += nme -> ty_sch
                val exp = getType(ty_sch)
                output(s"$nme: ${exp.show}")
            }
            
            if (mode.expectTypeErrors && totalTypeErrors =:= 0)
              failures += blockLineNum
            if (mode.expectWarnings && totalWarnings =:= 0)
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
    }
    val result = strw.toString
    if (result =/= fileContents) {
      println(s"Updating $file...")
      write.over(file, result)
    }
    if (failures.nonEmpty)
      fail(s"Unexpected diagnostics (or lack thereof) at: " + failures.map("l."+_).mkString(", "))
    
  }}
  
  try os.proc("git", "status", "--porcelain", dir).call().out.lines().foreach(l => println(" [git] " + l))
  catch { case err: Throwable => System.err.println("git command failed with: " + err) }
  
}
