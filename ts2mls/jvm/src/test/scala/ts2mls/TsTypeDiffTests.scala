package ts2mls

import mlscript.DiffTests
import mlscript.utils._, shorthands._

class TsTypeDiffTests extends DiffTests {
  import TsTypeDiffTests._

  private lazy val allFiles = os.walk(dir).filter(_.toIO.isFile)

  override protected def getFiles() = allFiles.filter { file =>
      val fileName = file.baseName
      validExt(file.ext)
  }
}

object TsTypeDiffTests {
  private val dir = os.pwd/"ts2mls"/"js"/"src"/"test"/"diff"
  private val validExt = Set("mls")
}