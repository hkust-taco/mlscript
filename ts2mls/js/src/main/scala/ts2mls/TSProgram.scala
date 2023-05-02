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

  implicit val checker = TSTypeChecker(program.getTypeChecker())

  // TODO: support multi-files correctly.
  private val globalNamespace = TSNamespace()
  private val entryFile = TSSourceFile(program.getSourceFile(filename), globalNamespace)
  private val importList = entryFile.getImportList
  private val importAlias = entryFile.getUnexportedAlias

  def generate(workDir: String, targetPath: String): Unit = {
    val moduleName = TSImport.getModuleName(filename)
    val relatedPath =
      if (filename.startsWith(workDir)) filename.substring(workDir.length() + 1, filename.lastIndexOf('/') + 1)
      else throw new AssertionError(s"wrong work dir $workDir")
    var writer = JSWriter(s"$targetPath/$relatedPath/$moduleName.mlsi")
    generate(writer)
    writer.close()
  }

  private def generate(writer: JSWriter): Unit =
    if (!uesTopLevelModule) globalNamespace.generate(writer, "") // will be imported directly and has no dependency
    else {
      importList.foreach{f => writer.writeln(s"""import "${TSImport.getModuleName(f)}.mlsi"""")}
      importAlias.foreach{alias => writer.writeln(Converter.convert(alias, false)(""))}
      writer.writeln(s"export declare module ${TSImport.getModuleName(filename)} {")
      globalNamespace.generate(writer, "  ")
      writer.writeln("}")
    }
}

object TSProgram {
  def apply(filename: String, uesTopLevelModule: Boolean) = new TSProgram(filename, uesTopLevelModule)
}
