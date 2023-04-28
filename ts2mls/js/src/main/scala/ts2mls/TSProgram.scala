package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import ts2mls.types._

// for general ts, we still consider that there is a top-level module
// and in mls we will import ts file like this:
// import * as TopLevelModuleName from "filename"
// for es5.d.ts, we only need to translate everything
// and it will be imported without top-level module before we compile other files
class TSProgram(filename: String, uesTopLevelModule: Boolean) {
  private val program = TypeScript.createProgram(Seq(filename))

  // check if file exists
  if (!program.fileExists(filename)) throw new Exception(s"file ${filename} doesn't exist.")

  val globalNamespace = TSNamespace()
  
  // TODO: support multi-files correctly.
  implicit val checker = TSTypeChecker(program.getTypeChecker())
  TSSourceFile(program.getSourceFile(filename), globalNamespace)

  def generate(writer: JSWriter): Unit =
    if (!uesTopLevelModule) globalNamespace.generate(writer, "")
    else {
      import TSProgram._
      writer.writeln(s"export declare module ${getModuleName(filename)} {")
      globalNamespace.generate(writer, "  ")
      writer.writeln("}")
    }
}

object TSProgram {
  def apply(filename: String, uesTopLevelModule: Boolean) = new TSProgram(filename, uesTopLevelModule)

  private def getModuleName(filename: String): String =
    if (filename.lastIndexOf('.') > -1)
      getModuleName(filename.substring(filename.lastIndexOf('/') + 1, filename.lastIndexOf('.')))
    else
      filename.substring(filename.lastIndexOf('/') + 1)
}
