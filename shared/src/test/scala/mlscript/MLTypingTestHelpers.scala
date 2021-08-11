package mlscript

import fastparse._
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class MLTypingTestHelpers extends org.scalatest.funsuite.AnyFunSuite {
  
  def doTest(str: String, expected: String = "")(implicit line: Line): Unit = {
    val dbg = expected.isEmpty
    
    val fph = new mlscript.FastParseHelpers(str)
    val parser = new MLParser(Origin("<input>", 0, fph))
    
    if (dbg) println(s">>> $str")
    val Success(term, index) = parse(str, parser.expr(_), verboseFailures = true)
    
    val typer = new Typer(dbg, verbose = false, explainErrors = false) with TypeSimplifier
    val tyv = typer.typeTerm(term)(typer.Ctx.init, throw _)
    
    if (dbg) {
      println("inferred: " + tyv)
      println(" where " + tyv.showBounds)
    }
    val cty = typer.compactType(tyv)
    if (dbg) println("compacted: " + cty)
    val sty = typer.simplifyType(cty)
    if (dbg) println("simplified: " + sty)
    val ety = typer.expandCompactType(sty)
    if (dbg) {
      println("expanded raw: " + ety)
      println("expanded: " + ety.show)
    }
    
    val res = ety.show
    if (dbg) {
      println("typed: " + res)
      println("---")
    } else {
      assert(res == expected, "at line " + line.value); ()
    }
  }
  def error(str: String, msg: String): Unit = {
    assert(intercept[TypeError](doTest(str, "<none>")).mainMsg == msg); ()
  }
  
}
