package ts2mls

import mlscript.DiffTests
import mlscript.utils._, shorthands._

class TsTypeDiffTests extends DiffTests {
  override protected def getFiles() =
    os.walk(os.pwd/"ts2mls"/"js"/"src"/"test"/"diff").filter(_.toIO.isFile)
}