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

  def generate(workDir: String, targetPath: String): Unit = generate(filename, workDir, targetPath)

  def generate(filename: String, workDir: String, targetPath: String): Unit = {
    val globalNamespace = TSNamespace()
    val entryFile = TSSourceFile(program.getSourceFile(filename), globalNamespace)
    val importList = entryFile.getImportList

    val moduleName = TSImport.getModuleName(filename)
    val relatedPath =
      if (filename.startsWith(workDir)) filename.substring(workDir.length() + 1, filename.lastIndexOf('/') + 1)
      else throw new AssertionError(s"wrong work dir $workDir")
    var writer = JSWriter(s"$targetPath/$relatedPath/$moduleName.mlsi")
    generate(writer, importList, globalNamespace, moduleName)
    writer.close()

    importList.foreach(imp => {
      val newFilename = // TODO: node_modules
        if (!imp.endsWith(".ts")) s"$imp.ts"
        else imp
      generate(newFilename, TSModuleResolver.resolve(workDir), targetPath)
    })
  }

  private def generate(writer: JSWriter, importList: List[String], globalNamespace: TSNamespace, moduleName: String): Unit =
    if (!uesTopLevelModule) globalNamespace.generate(writer, "") // will be imported directly and has no dependency
    else {
      importList.foreach{f => writer.writeln(s"""import "${TSImport.getModuleName(f)}.mlsi"""")}
      writer.writeln(s"export declare module $moduleName {")
      globalNamespace.generate(writer, "  ")
      writer.writeln("}")
    }
}

object TSProgram {
  def apply(filename: String, uesTopLevelModule: Boolean) = new TSProgram(filename, uesTopLevelModule)
}
