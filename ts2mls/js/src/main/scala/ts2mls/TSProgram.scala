package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import ts2mls.types._

class TSProgram(filenames: Seq[String], keepUnexportedVars: Boolean) {
  private val program = TypeScript.createProgram(filenames)

  // check if files exist
  filenames.foreach((fn) => if (!program.fileExists(fn)) throw new Exception(s"file ${fn} doesn't exist."))

  val globalNamespace = TSNamespace(keepUnexportedVars)
  
  implicit val checker = TSTypeChecker(program.getTypeChecker())
  filenames.foreach(filename => TSSourceFile(program.getSourceFile(filename), globalNamespace))

  def generate(writer: JSWriter): Unit = globalNamespace.generate(writer, "")
}

object TSProgram {
  def apply(filenames: Seq[String], keepUnexportedVars: Boolean) = new TSProgram(filenames, keepUnexportedVars)
}
