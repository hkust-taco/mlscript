package hkmc2

import scala.collection.mutable.ArrayBuffer

import mlscript.utils._, shorthands._

class FastParseHelpers(val blockStr: Str, val lines: collection.IndexedSeq[Str]) {
  def this(lines: IndexedSeq[Str]) = this(lines.mkString("\n"), lines)
  def this(blockStr: Str) = this(blockStr, blockStr.splitSane('\n'))
  
  // this line-parsing logic was copied from fastparse internals:
  // val lineNumberLookup: Array[Int] = fastparse.internal.Util.lineNumberLookup(blockStr)
  val lineNumberLookup: Array[Int] = mkLineNumberLookup(blockStr)
  def mkLineNumberLookup(data: String): Array[Int] = {
    val lineStarts = new ArrayBuffer[Int]()
    var i = 0
    var col = 1
    var cr = false
    var prev: Character = null
    while i < data.length do {
      val char = data(i)
      if char == '\r' then {
        if prev != '\n' && col == 1 then lineStarts.append(i)
        col = 1
        cr = true
      }else if char == '\n' then {
        if prev != '\r' && col == 1 then lineStarts.append(i)
        col = 1
        cr = false
      }else{
        if col == 1 then lineStarts.append(i)
        col += 1
        cr = false
      }
      prev = char
      i += 1
    }
    if col == 1 then lineStarts.append(i)

    lineStarts.toArray
  }
  
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
