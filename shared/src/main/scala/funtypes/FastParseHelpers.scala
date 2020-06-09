package funtypes

object FastParseHelpers {
  
  def getLineAt(str: String, index: Int): (Int, String) = {
    // this line-parsing logic was copied from fastparse internals:
    val lineNumberLookup = fastparse.internal.Util.lineNumberLookup(str)
    val lineNum = lineNumberLookup.indexWhere(_ > index) match {
      case -1 => lineNumberLookup.length - 1
      case n => math.max(0, n - 1)
    }
    val lines = str.split('\n')
    val lineStr = lines(lineNum min lines.length - 1)
    (lineNum, lineStr)
  }
  
}
