package simplesub

import org.scalatest._
import fastparse._
import Parser.expr
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class TypingTester extends FunSuite {
  
  def doTest(str: String, expected: String = "")(implicit line: Line): Unit = {
    if (expected.isEmpty) println(s">>> $str")
    val Success(term, index) = parse(str, expr(_), verboseFailures = true)
    
    val typing = new Typer
    val tyv = typing.inferType(term)
    
    if (expected.isEmpty) {
      println("inferred: " + tyv)
      println(" where " + tyv.showBounds)
    }
    val ty = typing.expandType(tyv, true)
    if (expected.isEmpty) println("T " + ty.show)
    val res = ty.normalize.show
    if (expected.isEmpty) println("N " + res)
    
    val ety = typing.expandPosType(tyv, true)
    val sety = ety.simplify
    val res2 = sety.show
    // val res2 = typing.expandSimplifiedPosType(tyv, true).show
    if (expected.nonEmpty)
      assert(res2 == expected, "at line " + line.value)
    else {
      println("typed: " + ety.show)
      println("simpl: " + res2)
      // println("occ "+ety.occurrences)
      // println("occ "+ety.simplify.show)
      println("---")
    }
    
    ()
  }
  def error(str: String, msg: String): Unit = {
    assert(intercept[TypeError](doTest(str, "<none>")).msg == msg)
    ()
  }
  
}
