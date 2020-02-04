package simplesub

import org.scalatest._
import fastparse._
import Parser.expr
import fastparse.Parsed.Failure
import fastparse.Parsed.Success

class ParserTests extends FunSuite {
  
  def doTest(str: String): Unit = {
    parse(str, expr(_), verboseFailures = true) match {
      case Success(value, index) =>
        // println("OK: " + value)
      case f @ Failure(expected, failIndex, extra) =>
        println(extra.trace())
        println(extra.trace().longAggregateMsg)
        assert(false)
    }
    ()
  }
  
  test("basics") {
    doTest("1")
    doTest("a")
    doTest("1 2 3")
    doTest("a b c")
  }
  
  test("let") {
    doTest("let a = b in c")
    doTest("let a = 1 in 1")
    doTest("let a = (1) in 1")
  }
  
}
