package mlscript

import mlscript.utils._, shorthands._

class FastParseHelpers(val blockStr: Str, val lines: collection.IndexedSeq[Str]) {
  def this(lines: IndexedSeq[Str]) = this(lines.mkString("\n"), lines)
  def this(blockStr: Str) = this(blockStr, blockStr.splitSane('\n'))
  
  // this line-parsing logic was copied from fastparse internals:
  val lineNumberLookup: Array[Int] = fastparse.internal.Util.lineNumberLookup(blockStr)
  def getLineColAt(index: Int): (Int, String, Int) = {
    val lineNum = lineNumberLookup.indexWhere(_ > index) match {
      case -1 => lineNumberLookup.length
      case n => math.max(1, n)
    }
    val idx = lineNum.min(lines.length) - 1
    val colNum = index - lineNumberLookup(idx) + 1
    val lineStr = lines(idx)
    (lineNum, lineStr, colNum)
  }
  
}
