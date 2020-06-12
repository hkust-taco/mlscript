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
  
  private val files = ls.rec(pwd/"shared"/"src"/"test"/"diff").filter(_.isFile)
  
  files.foreach { file => test(file.baseName) {
    
    val outputMarker = "/// "
    val fileContents = read(file)
    val allLines = fileContents.splitSane('\n').toList
    val strw = new java.io.StringWriter
    val out = new java.io.PrintWriter(strw)
    def output(str: String) = out.println(outputMarker + str)
    val parser = new Parser
    val typer = new Typer(dbg = false) with TypeSimplifier {
      override def emitDbg(str: String): Unit = output(str)
    }
    var ctx: typer.Ctx = typer.builtins
    val failures = mutable.Buffer.empty[Int]
    
    case class Mode(
      expectTypeErrors: Bool, expectWarnings: Bool, expectParseErrors: Bool,
      fixme: Bool, showParse: Bool, dbg: Bool)
    val defaultMode = Mode(false, false, false, false, false, false)
    
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
          case _ =>
            failures += allLines.size - lines.size
            output("/!\\ Unrecognized option " + line)
            mode
        }
        rec(ls, newMode)
      case line :: ls if line.startsWith("// FIXME") || line.startsWith("// TODO") =>
        out.println(line)
        rec(ls, mode.copy(fixme = true))
      case line :: ls if line.startsWith(outputMarker) => rec(ls, defaultMode)
      case line :: ls if line.isEmpty || line.startsWith("//") =>
        out.println(line)
        rec(ls, defaultMode)
      case l :: ls =>
        val block = (l :: ls.takeWhile(l => l.nonEmpty && !l.startsWith(outputMarker))).toIndexedSeq
        block.foreach(out.println)
        val fph = new FastParseHelpers(block)
        val blockStr = fph.blockStr
        val ans = try parse(blockStr, parser.pgrm(_), verboseFailures = true) match {
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
            val tys = try typer.typeBlk(p, ctx, allowPure = true) finally typer.dbg = false
            var totalTypeErrors = 0
            var totalWarnings = 0
            val res = (p.stmts.zipWithIndex lazyZip tys).map {
              case ((s, _), diags -> ty) =>
                // totalTypeErrors += diags.length
                diags.foreach { diag =>
                  diag match {
                    case TypeError(msg, loco) =>
                      totalTypeErrors += 1
                      output(s"/!\\ Type error: $msg")
                    case Warning(msg, loco) =>
                      totalWarnings += 1
                      output(s"/!\\ Warning: $msg")
                  }
                  val globalStartLineNum = allLines.size - lines.size + 1
                  val globalLineNum = globalStartLineNum + diag.loco.fold(0) { loc =>
                    val (startLineNum, startLineStr, startLineCol) =
                      fph.getLineColAt(loc.spanStart)
                    val (endLineNum, endLineStr, endLineCol) =
                      fph.getLineColAt(loc.spanEnd)
                    var l = startLineNum
                    var c = startLineCol
                    while (l <= endLineNum) {
                      val globalLineNum = globalStartLineNum + l - 1
                      val pre = s"l.$globalLineNum: "
                      val curLine = block(l - 1)
                      output(pre + "\t" + curLine)
                      out.print(outputMarker + " " * pre.length + "\t" + " " * (c - 1))
                      val lastCol = if (l =:= endLineNum) endLineCol else curLine.length + 1
                      while (c < lastCol) { out.print('^'); c += 1 }
                      out.println
                      c = 1
                      l += 1
                    }
                    startLineNum - 1
                  }
                  if (!mode.fixme && (
                      !mode.expectTypeErrors && diag.isInstanceOf[TypeError]
                   || !mode.expectWarnings && diag.isInstanceOf[Warning]
                  )) failures += globalLineNum
                  ()
                }
                if (diags.exists(_.isInstanceOf[TypeError]) && !mode.expectTypeErrors) {
                  // output(s"Statement was parsed as:\n$outputMarker\t$s")
                  if (!mode.dbg) {
                    output(s"Retyping with debug info...")
                    typer.resetState()
                    typer.dbg = true
                    try typer.typeStatement(s, allowPure = true)(ctx, 0, throw _)
                    catch { case err: TypeError =>
                      output(s"ERROR: " + err.msg)
                      if (!mode.fixme)
                        err.getStackTrace().take(10).foreach(s => output("\tat: " + s))
                    } finally typer.dbg = false
                  }
                }
                // if (diags.exists(_.isInstanceOf[Warning]) && !mode.expectTypeErrors) {
                // }
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
              err.getStackTrace().take(10).map("\n" + outputMarker + "\tat: " + _).mkString
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
  
}
