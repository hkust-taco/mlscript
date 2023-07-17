package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import ts2mls.types._
import scala.collection.mutable.{HashSet, HashMap}

// For general ts, we still consider that there is a top-level module
// and in mls we will import ts file like this:
// `import * as TopLevelModuleName from "filename"`.
// For es5.d.ts, we only need to translate everything
// and it will be imported without top-level module before we compile other files
class TSProgram(
  file: FileInfo,
  uesTopLevelModule: Boolean,
  tsconfig: Option[String],
  typer: (FileInfo, JSWriter) => Unit,
  gitHelper: Option[JSGitHelper]
) {
  private implicit val configContent = TypeScript.parseOption(file.workDir, tsconfig)
  private val program = TypeScript.createProgram(Seq(
    if (file.isNodeModule) file.resolve
    else file.filename
  ))
  private val cache = new HashMap[String, TSSourceFile]()
  private implicit val checker = TSTypeChecker(program.getTypeChecker())

  import TSPathResolver.{basename, extname, isLocal, resolve, dirname, relative, normalize}

  def generate: Boolean = generate(file, None)(Nil)

  private def generate(file: FileInfo, ambientNS: Option[TSNamespace])(implicit stack: List[String]): Boolean = {
    def resolve(file: FileInfo) = if (TypeScript.isLinux) file.resolve else file.resolve.toLowerCase()
    // We prefer to not tract node_modules in git, so we need to check if the interface file exists
    def shouldRecompile(filename: String, interface: String) = gitHelper.fold(true)(
      helper => helper.forceIfNoChange || helper.filter(relative(filename, file.workDir)) || !JSFileSystem.exists(interface)
    )

    val filename = resolve(file)
    val moduleName = file.moduleName
    val globalNamespace = ambientNS.getOrElse(TSNamespace(!uesTopLevelModule))
    val sfObj = program.getSourceFileByPath(filename)
    val sourceFile =
      if (js.isUndefined(sfObj)) throw new Exception(s"can not load source file $filename.")
      else TSSourceFile(sfObj, globalNamespace, moduleName)
    val importList = sourceFile.getImportList
    val reExportList = sourceFile.getReExportList
    cache.addOne(filename, sourceFile)
    val relatedPath = relative(file.workDir, dirname(filename))
    val interfaceFilename = s"${file.workDir}/${file.interfaceFilename}"

    val (cycleList, otherList) =
      importList.map(imp => file.`import`(imp.filename)).filter(
        imp => !resolve(imp).endsWith(".js") // If it is not a ts lib, we ignore it and require users to provide full type annotations
      ).partitionMap(imp => {
        if (stack.contains(resolve(imp))) Left(imp)
        else Right(imp)
      })

    val cycleRecompile = cycleList.foldLeft(false)((r, f) =>
      r || shouldRecompile(resolve(f), s"${f.workDir}/${f.interfaceFilename}"))
    val reExportRecompile = reExportList.foldLeft(false)((r, e) =>
      r || {
        val f = file.`import`(e.filename)
        shouldRecompile(resolve(f), s"${f.workDir}/${f.interfaceFilename}")
      })
    val referencedRecompile: Boolean = sourceFile.referencedFiles.reduce((r: Boolean, s: js.Dynamic) => {
      val f = file.`import`(s.toString())
      r || shouldRecompile(resolve(f), interfaceFilename)
    }, false)

    val dependentRecompile = otherList.foldLeft(cycleRecompile || reExportRecompile || referencedRecompile)((r, imp) => {
      generate(imp, None)(filename :: stack) || r
    })

    if (!dependentRecompile && !shouldRecompile(filename, interfaceFilename)) return false
    sourceFile.parse
    
    val writer = JSWriter(interfaceFilename)
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
        val sf = cache(resolve(imp))
        sf.parse
        sf.global.generate(writer, "  ")
        writer.writeln("}")
      }
    })

    reExportList.foreach {
      case TSReExport(alias, imp, memberName) =>
        val absName = resolve(file.`import`(imp))
        if (!cache.contains(absName))
          throw new AssertionError(s"unexpected re-export from ${imp}")
        else {
          val ns = cache(absName).global
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

    true
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
  def apply(
    file: FileInfo,
    uesTopLevelModule: Boolean,
    tsconfig: Option[String],
    typer: (FileInfo, JSWriter) => Unit,
    gitHelper: Option[JSGitHelper]
  ) =
    new TSProgram(file, uesTopLevelModule, tsconfig, typer, gitHelper)
}
