package funtypes

import org.scalatest._
import fastparse._
import MLParser.pgrm
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line
import ammonite.ops._

class DiffTests extends FunSuite {
  
  private val files = ls(pwd/"shared"/"src"/"test"/"diff")
  
  files.foreach { file =>
    
    val lines = read.lines(file)
    val out = new java.io.PrintWriter(file.toString)
    val typer = new Typer(dbg = false) with TypeSimplifier
    var ctx: typer.Ctx = typer.builtins
    
    try lines.foreach { line =>
      if (line.startsWith(">")) {
        val str = line.tail.trim()
        out.println(line)
        val ans = try {
          parse(str, pgrm(_), verboseFailures = true) match {
            case Failure(lbl, index, extra) =>
              val (lineNum, lineStr) = FastParseHelpers.getLineAt(str, index)
              "/!\\ Parse error: " + extra.trace().msg +
                s" at line $lineNum: $lineStr"
            case Success(p, index) =>
              val tys = typer.inferTypes(p, ctx)
              (p.defs.zipWithIndex lazyZip tys).map {
                case ((d, i), Right(ty)) =>
                  ctx += d._2 -> ty
                  // println(s"Typed `${d._2}` as: $ty")
                  // println(s" where: ${ty.instantiate(0).showBounds}")
                  val com = typer.compactType(ty.instantiate(0))
                  // println(s"Compact type before simplification: ${com}")
                  val sim = typer.simplifyType(com)
                  // println(s"Compact type after simplification: ${sim}")
                  val exp = typer.expandCompactType(sim)
                  s"${d._2}: ${exp.show}"
                case ((d, i), Left(TypeError(msg))) =>
                  s"Type error in ${d._2}: $msg"
              }.mkString("\n")
          }
        } catch {
          case err: TypeError =>
            s"/!\\ Type error: $err"
        }
        out.println(ans)
      } else if (line.isEmpty || line.startsWith("//")) {
        out.println(line)
      } else {
      }
    } finally {
      out.close()
    }
    
  }
  
}
