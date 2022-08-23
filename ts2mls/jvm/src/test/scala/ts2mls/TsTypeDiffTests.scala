package ts2mls

import mlscript.DiffTests
import mlscript.utils._, shorthands._

class TsTypeDiffTests extends DiffTests {
  import TsTypeDiffTests._

  override protected def getFiles() =
    os.walk(dir).filter(_.toIO.isFile)
}

object TsTypeDiffTests {
  private val dir = os.pwd/"ts2mls"/"js"/"src"/"test"/"diff"
}