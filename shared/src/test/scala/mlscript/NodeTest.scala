package mlscript

class NodeTests extends org.scalatest.funsuite.AnyFunSuite {
  
  test("node versoion") {
    
    val v = os.proc("node", "-v").call().out.lines().head
    
    println(s"Detected node version: " + v)
    
    assert(
          v.startsWith("v16.14")
      ||  v.startsWith("v17")
    )
    
  }
  
}
