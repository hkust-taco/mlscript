package ts2mls

import org.scalatest.funsuite.AnyFunSuite

class WrongPath extends AnyFunSuite {
  test("Wrong Path") {
    try {
      val program = TSProgram(WrongPath.testFiles)
      assert(false)
    }
    catch {
      case e: java.lang.Exception => assert(true)
    }
  }
}

object WrongPath {
  private val testFiles = TSTypeTest.tsPathes(Seq("AFileThatNeverExists.ts"))
}