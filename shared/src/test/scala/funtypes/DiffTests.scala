package funtypes

import org.scalatest._
import fastparse._
import MLParser.pgrm
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line
import ammonite.ops._
import scala.collection.mutable
import funtypes.utils._, shorthands._

class DiffTests extends FunSuite {
  
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
    var ctx: typer.Ctx = typer.builtins
    val failures = mutable.Buffer.empty[Int]
    
    case class Mode(
      expectTypeErrors: Bool, expectWarnings: Bool, expectParseErrors: Bool,
      fixme: Bool, showParse: Bool, verbose: Bool, explainErrors: Bool, dbg: Bool, fullExceptionStack: Bool)
    val defaultMode = Mode(false, false, false, false, false, false, false, false, false)
    
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
        val fph = new FastParseHelpers(block)
        val globalStartLineNum = allLines.size - lines.size + 1
        val parser = new Parser(Origin(fileName, globalStartLineNum, fph))
        val ans = try parse(fph.blockStr, parser.pgrm(_), verboseFailures = true) match {
          case f @ Failure(lbl, index, extra) =>
            val (lineNum, lineStr, col) = fph.getLineColAt(index)
            val globalLineNum = (allLines.size - lines.size) + lineNum
            if (!mode.expectParseErrors && !mode.fixme)
              failures += globalLineNum
            outputMarker + "/!\\ Parse error: " + extra.trace().msg +
              s" at l.$globalLineNum:$col: $lineStr"
          case Success(p, index) =>
            val blockLineNum = (allLines.size - lines.size) + 1
            if (mode.expectParseErrors)
              failures += blockLineNum
            if (mode.showParse) output("Parsed: " + p)
            if (mode.dbg) typer.resetState()
            typer.dbg = mode.dbg
            typer.verbose = mode.verbose
            typer.explainErrors = mode.explainErrors
            val tys = typer.typeBlk(p, ctx, allowPure = true)
            var totalTypeErrors = 0
            var totalWarnings = 0
            val res = (p.stmts.zipWithIndex lazyZip tys).map {
              case ((s, _), diags -> ty) =>
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
                  var globalLineNum = 0  // solely used for reporting useful test failure messages
                  diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
                    val isLast = msgNum =:= lastMsgNum
                    val msgStr = msg.showIn(sctx)
                    if (msgNum =:= 0) output(headStr + msgStr)
                    else output(s"${if (isLast && loco.isEmpty) "╙──" else "╟──"} ${msgStr}")
                    loco.foreach { loc =>
                      val (startLineNum, startLineStr, startLineCol) =
                        loc.origin.fph.getLineColAt(loc.spanStart)
                      if (globalLineNum =:= 0) globalLineNum = startLineNum - 1
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
                  if (!allowTypeErrors && !mode.fixme && (
                      !mode.expectTypeErrors && diag.isInstanceOf[TypeError]
                   || !mode.expectWarnings && diag.isInstanceOf[Warning]
                  )) failures += globalLineNum
                  ()
                }
                if (diags.exists(_.isInstanceOf[TypeError]) && !mode.expectTypeErrors && !allowTypeErrors) {
                  // output(s"Statement was parsed as:\n$outputMarker\t$s")
                  if (!mode.dbg) {
                    output(s"Retyping with debug info...")
                    typer.resetState()
                    typer.dbg = true
                    try typer.typeStatement(s, allowPure = true)(ctx, 0, throw _)
                    catch { case err: TypeError =>
                      output(s"ERROR: " + err.mainMsg)
                      if (!mode.fixme)
                        err.getStackTrace().take(10).foreach(s => output("\tat: " + s))
                    } finally typer.dbg = false
                  }
                }
                if (mode.dbg) output(s"Typed as: $ty")
                if (mode.dbg) output(s" where: ${ty.instantiate(0).showBounds}")
                val com = typer.compactType(ty.instantiate(0))
                if (mode.dbg) output(s"Compact type before simplification: ${com}")
                val sim = typer.simplifyType(com)
                if (mode.dbg) output(s"Compact type after simplification: ${sim}")
                val exp = typer.expandCompactType(sim)
                s match {
                  case LetS(_, Var(n), _) =>
                    ctx += n -> ty
                    s"$n: ${exp.show}"
                  case _ =>
                    ctx += "res" -> ty
                    s"res: ${exp.show}"
                }
            }.map(outputMarker + _).mkString("\n")
            if (mode.expectTypeErrors && totalTypeErrors =:= 0)
              failures += blockLineNum
            if (mode.expectWarnings && totalWarnings =:= 0)
              failures += blockLineNum
            res
        } catch {
          case err: Throwable =>
            if (!mode.fixme)
              failures += allLines.size - lines.size
            // err.printStackTrace(out)
            outputMarker + "/!!!\\ Uncaught error: " + err +
              err.getStackTrace().take(if (mode.fullExceptionStack) Int.MaxValue else 10)
                .map("\n" + outputMarker + "\tat: " + _).mkString
        } finally {
          typer.dbg = false
          typer.verbose = false
        }
        out.println(ans)
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
