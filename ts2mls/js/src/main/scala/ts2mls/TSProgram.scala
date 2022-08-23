package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import scala.collection.mutable.HashMap
import ts2mls.types._

class TSProgram(filenames: Seq[String]) {
  private val program = TypeScript.createProgram(filenames)

  // check if files exist
  filenames.foreach((fn) => if (!program.fileExists(fn)) throw new Exception(s"file ${fn} doesn't exist."))

  implicit private val checker: TSTypeChecker = TSTypeChecker(program.getTypeChecker())
  val globalNamespace = TSNamespace()
  
  filenames.foreach(filename => {
    filename -> TSSourceFile(program.getSourceFile(filename), globalNamespace)
  })

  def generate(writer: JSWriter, prefix: String = ""): Unit = globalNamespace.generate(writer, prefix)
}

object TSProgram {
    def apply(filenames: Seq[String]) = new TSProgram(filenames)

    def getMLSType(tp: TSType): String = Converter.convert(tp)
}