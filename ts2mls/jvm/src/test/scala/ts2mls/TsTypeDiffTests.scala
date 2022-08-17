package ts2mls

import mlscript.DiffTests

class TsTypeDiffTests extends DiffTests(TsTypeDiffTests.dir) {
}

object TsTypeDiffTests {
  private val dir = os.pwd/"ts2mls"/"js"/"src"/"test"/"diff"
}