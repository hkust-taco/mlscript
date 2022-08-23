package mlscript

class NodeTests extends org.scalatest.funsuite.AnyFunSuite {
  
  test("node version") {
    
    val v = os.proc("node", "-v").call().out.lines().head
    
    println(s"Detected node version: " + v)
    
    assert(
          v.startsWith("v16.14")
      ||  v.startsWith("v16.15")
      ||  v.startsWith("v16.16")
      ||  v.startsWith("v16.17")
      ||  v.startsWith("v17")
      ||  v.startsWith("v18")
    )
    
  }
  
}
