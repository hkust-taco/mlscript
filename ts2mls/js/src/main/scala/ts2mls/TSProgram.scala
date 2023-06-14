package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import ts2mls.types._
import scala.collection.mutable.{HashSet, HashMap}
import ts2mls.TSPathResolver

// for general ts, we still consider that there is a top-level module
// and in mls we will import ts file like this:
// import * as TopLevelModuleName from "filename"
// for es5.d.ts, we only need to translate everything
// and it will be imported without top-level module before we compile other files
class TSProgram(filename: String, workDir: String, uesTopLevelModule: Boolean, tsconfig: Option[String]) {
  private implicit val configContent = TypeScript.parseOption(workDir, tsconfig)
  private val fullname =
    if (JSFileSystem.exists(s"$workDir/$filename")) s"$workDir/$filename"
    else TypeScript.resolveModuleName(filename, "", configContent) match {
      case Some(path) => path
      case _ => throw new Exception(s"file $workDir/$filename doesn't exist.")
    }

  private val program = TypeScript.createProgram(Seq(fullname))
  private val cache = new HashMap[String, TSNamespace]()

  private implicit val checker = TSTypeChecker(program.getTypeChecker())

  import TSPathResolver.{basename, extname, isLocal, resolve, dirname, relative, normalize}

  def generate(outputFilename: String): Boolean =
    generate(resolve(fullname), outputFilename)(Nil)

  private def generate(filename: String, outputFilename: String)(implicit stack: List[String]): Boolean = { 
    val globalNamespace = TSNamespace()
    val sourceFile = TSSourceFile(program.getSourceFile(filename), globalNamespace)
    val importList = sourceFile.getImportList
    val reExportList = sourceFile.getReExportList
    cache.addOne(filename, globalNamespace)
    val relatedPath = relative(workDir, dirname(filename))

    def `import`(imp: String) = TypeScript.resolveModuleName(imp, filename, configContent).getOrElse("")

    val moduleName = basename(filename)

    val (cycleList, otherList) =
      importList.partition(imp => stack.contains(`import`(imp.filename)))

    otherList.foreach(imp => {
      val fullname = `import`(imp.filename)
      generate(fullname,
        if (isLocal(imp.filename)) normalize(s"${dirname(outputFilename)}/${basename(imp.filename)}.mlsi")
        else TSImport.createInterfaceForNode(fullname)
      )(filename :: stack)
    })

    var writer = JSWriter(outputFilename)
    val imported = new HashSet[String]()
    
    otherList.foreach(imp => {
      val name = imp.filename.replace(extname(imp.filename), "")
      if (!imported(name)) {
        imported += name
        writer.writeln(s"""import "$name.mlsi"""")
      }
    })
    cycleList.foreach(imp => {
      writer.writeln(s"declare module ${basename(imp.filename)} {")
      cache(`import`(imp.filename)).generate(writer, "  ")
      writer.writeln("}")
    })

    reExportList.foreach {
      case TSReExport(alias, imp, memberName) =>
        val absName = `import`(imp)
        if (!cache.contains(absName))
          throw new AssertionError(s"unexpected re-export from ${imp}")
        else {
          val ns = cache(absName)
          val moduleName = basename(absName)
          memberName.fold(
            globalNamespace.put(alias, TSRenamedType(alias, TSReferenceType(moduleName)), true)
          )(name => ns.getTop(name).fold[Unit](())(tp => globalNamespace.put(alias, TSRenamedType(alias, tp), true)))
        }
    }

    generate(writer, globalNamespace, moduleName)
    writer.close()
  }

  private def generate(writer: JSWriter, globalNamespace: TSNamespace, moduleName: String): Unit =
    if (!uesTopLevelModule) globalNamespace.generate(writer, "") // will be imported directly and has no dependency
    else {
      writer.writeln(s"export declare module $moduleName {")
      globalNamespace.generate(writer, "  ")
      writer.writeln("}")
    }
}

object TSProgram {
  def apply(filename: String, workDir: String, uesTopLevelModule: Boolean, tsconfig: Option[String]) =
    new TSProgram(filename, workDir, uesTopLevelModule, tsconfig)
}
