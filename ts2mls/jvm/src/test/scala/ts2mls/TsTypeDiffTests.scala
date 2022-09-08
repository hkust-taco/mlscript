package ts2mls

import mlscript.DiffTests

class TsTypeDiffTests extends DiffTests {
  override protected lazy val files =
    os.walk(os.pwd/"ts2mls"/"js"/"src"/"test"/"diff").filter(_.toIO.isFile)
}
