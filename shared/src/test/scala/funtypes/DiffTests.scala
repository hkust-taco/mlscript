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
    
    case class Mode(silenceErrors: Bool, fixme: Bool, showParse: Bool, dbg: Bool)
    val defaultMode = Mode(false, false, false, false)
    
    def rec(lines: List[String], mode: Mode): Unit = lines match {
      case "" :: Nil =>
      case line :: ls if line.startsWith(":") =>
        out.println(line)
        val newMode = line.tail match {
          case "e" => mode.copy(silenceErrors = true)
          case "p" => mode.copy(showParse = true)
          case "d" => mode.copy(dbg = true)
          case _ =>
            failures += allLines.size - lines.size
            output("/!\\ Unrecognized option " + line)
            mode
        }
        rec(ls, newMode)
      case line :: ls if line.startsWith("// FIXME") =>
        out.println(line)
        rec(ls, mode.copy(fixme = true))
      case line :: ls if line.startsWith(outputMarker) => rec(ls, defaultMode)
      case line :: ls if line.isEmpty || line.startsWith("//") =>
        out.println(line)
        rec(ls, defaultMode)
      case l :: ls =>
        val block = l :: ls.takeWhile(l => l.nonEmpty && !l.startsWith(outputMarker))
        block.foreach(out.println)
        val blockStr = block.mkString("\n")
        val ans = try parse(blockStr, parser.pgrm(_), verboseFailures = true) match {
          case f @ Failure(lbl, index, extra) =>
            val (lineNum, lineStr) = FastParseHelpers.getLineAt(blockStr, index)
            val globalLineNum = (allLines.size - lines.size) + lineNum
            if (!mode.silenceErrors && !mode.fixme)
              failures += globalLineNum
            outputMarker + "/!\\ Parse error: " + extra.trace().msg +
              s" at line $globalLineNum: $lineStr"
          case Success(p, index) =>
            if (mode.showParse) output("Parsed: " + p)
            if (mode.dbg) typer.resetState()
            typer.dbg = mode.dbg
            val tys = try typer.typeBlk(p, ctx) finally typer.dbg = false
            (p.stmts.zipWithIndex lazyZip tys).map {
              case ((s, _), errs -> ty) =>
                // if (mode.showParse) output("Parsed: " + s)
                errs.foreach { case TypeError(msg) =>
                  val (lineNum, lineStr) = FastParseHelpers.getLineAt(blockStr, index)
                  val globalLineNum = (allLines.size - lines.size) + lineNum
                  output(s"/!\\ Type error at line ${globalLineNum}: $msg")
                  if (!mode.silenceErrors && !mode.fixme)
                    failures += globalLineNum
                  ()
                }
                if (errs.nonEmpty && !mode.silenceErrors) {
                  // output(s"Statement was parsed as:\n$outputMarker\t$s")
                  if (!mode.dbg) {
                    output(s"Retyping with debug info...")
                    typer.resetState()
                    typer.dbg = true
                    try typer.typeStatement(s)(ctx, 0, throw _)
                    catch { case err: TypeError =>
                      output(s"ERROR: " + err.msg)
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
      fail(s"Unexpected error(s) at: " + failures.map("l."+_).mkString(", "))
    
  }}
  
}
