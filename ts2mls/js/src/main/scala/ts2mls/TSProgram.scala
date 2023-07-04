package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import ts2mls.types._
import scala.collection.mutable.{HashSet, HashMap}

// for general ts, we still consider that there is a top-level module
// and in mls we will import ts file like this:
// import * as TopLevelModuleName from "filename"
// for es5.d.ts, we only need to translate everything
// and it will be imported without top-level module before we compile other files
class TSProgram(file: FileInfo, uesTopLevelModule: Boolean, tsconfig: Option[String], typer: (FileInfo, JSWriter) => Unit) {
  private implicit val configContent = TypeScript.parseOption(file.workDir, tsconfig)
  private val program = TypeScript.createProgram(Seq(
    if (file.isNodeModule) file.resolve
    else file.filename
  ))
  private val cache = new HashMap[String, TSNamespace]()
  private implicit val checker = TSTypeChecker(program.getTypeChecker())

  import TSPathResolver.{basename, extname, isLocal, resolve, dirname, relative, normalize}

  def generate: Unit = generate(file, None)(Nil)

  private def generate(file: FileInfo, ambientNS: Option[TSNamespace])(implicit stack: List[String]): Unit = {
    val filename = if (TypeScript.isLinux) file.resolve else file.resolve.toLowerCase()
    val moduleName = file.moduleName
    val globalNamespace = ambientNS.getOrElse(TSNamespace(!uesTopLevelModule))
    val sfObj = program.getSourceFileByPath(filename)
    val sourceFile =
      if (js.isUndefined(sfObj)) throw new Exception(s"can not load source file $filename.")
      else TSSourceFile(sfObj, globalNamespace, moduleName)
    val importList = sourceFile.getImportList
    val reExportList = sourceFile.getReExportList
    cache.addOne(filename, globalNamespace)
    val relatedPath = relative(file.workDir, dirname(filename))

    val (cycleList, otherList) =
      importList.partitionMap(imp => {
        val newFile = file.`import`(imp.filename)
        if (stack.contains(newFile.resolve)) Left(newFile)
        else Right(newFile)
      })

    otherList.foreach(imp => {
      generate(imp, None)(filename :: stack)
    })

    var writer = JSWriter(s"${file.workDir}/${file.interfaceFilename}")
    val imported = new HashSet[String]()
    
    otherList.foreach(imp => {
      val name = file.translateImportToInterface(imp)
      if (!imported(name)) {
        imported += name
        writer.writeln(s"""import "$name"""")
      }
    })
    cycleList.foreach(imp => {
      if (ambientNS.isEmpty || stack.indexOf(filename) > 0) {
        writer.writeln(s"declare module ${Converter.escapeIdent(imp.moduleName)} {")
        cache(imp.resolve).generate(writer, "  ")
        writer.writeln("}")
      }
    })

    reExportList.foreach {
      case TSReExport(alias, imp, memberName) =>
        val absName = file.`import`(imp).resolve
        if (!cache.contains(absName))
          throw new AssertionError(s"unexpected re-export from ${imp}")
        else {
          val ns = cache(absName)
          val moduleName = basename(absName)
          memberName.fold(
            globalNamespace.put(alias, TSRenamedType(alias, TSReferenceType(moduleName)), true, false)
          )(name => globalNamespace.put(alias, TSRenamedType(alias, TSReferenceType(s"$moduleName.$name")), true, false))
        }
    }

    sourceFile.referencedFiles.forEach((s: js.Dynamic) => {
      generate(file.`import`(s.toString()), sourceFile.getUMDModule)(filename :: stack)
    })

    if (ambientNS.isEmpty) {
      generate(writer, globalNamespace, moduleName, globalNamespace.isCommonJS)
      typer(file, writer)
      writer.close()
    }
  }

  private def generate(writer: JSWriter, globalNamespace: TSNamespace, moduleName: String, commonJS: Boolean): Unit =
    if (!uesTopLevelModule || commonJS) globalNamespace.generate(writer, "")
    else {
      writer.writeln(s"export declare module ${Converter.escapeIdent(moduleName)} {")
      globalNamespace.generate(writer, "  ")
      writer.writeln("}")
    }
}

object TSProgram {
  def apply(file: FileInfo, uesTopLevelModule: Boolean, tsconfig: Option[String], typer: (FileInfo, JSWriter) => Unit) =
    new TSProgram(file, uesTopLevelModule, tsconfig, typer)
}
