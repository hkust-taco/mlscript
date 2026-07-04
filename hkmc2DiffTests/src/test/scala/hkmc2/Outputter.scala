package hkmc2

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*


class Outputter(val out: java.io.PrintWriter):
  
  val outputMarker = "//│ "
  // val oldOutputMarker = "/// "

  val diffBegMarker = "<<<<<<<"
  val diffMidMarker = "======="
  val diff3MidMarker = "|||||||" // * Appears under `git config merge.conflictstyle diff3` (https://stackoverflow.com/a/18131595/1518588)
  val diffEndMarker = ">>>>>>>"

  val ColWidth = 100
  val exitMarker = "=" * ColWidth
  val blockSeparator = "—" * 80
  
  val fullBlockSeparator = outputMarker + blockSeparator
  
  /** Tracks the net difference between lines written to the output and lines
    * consumed from the original file so far. Adding a new output line (via
    * [[apply]]) increments it; consuming an original output line (starting
    * with [[outputMarker]]) decrements it. This is used to adjust block
    * line numbers so they refer to positions in the output file rather than
    * the original, avoiding the need for a second run to stabilize them. */
  var linesDelta: Int = 0
  
  def apply(str: String) =
    // out.println(outputMarker + str)
    val ls = str.splitSane('\n')
    linesDelta += ls.size
    ls.foreach(l => out.println(outputMarker + l))


