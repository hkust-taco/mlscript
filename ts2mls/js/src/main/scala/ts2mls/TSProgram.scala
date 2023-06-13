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

  private def resolveTarget(filename: String) = {
    val moduleName = TSImport.getModuleName(filename, false)
    Option.when(!TSModuleResolver.isLocal(filename))(s"node_modules/$moduleName/$moduleName.mlsi")
  }

  def generate(targetPath: String): Boolean =
    generate(TSModuleResolver.resolve(fullname), targetPath, resolveTarget(filename))(Nil)

  private def generate(filename: String, targetPath: String, outputOverride: Option[String])(implicit stack: List[String]): Boolean = {
    if (filename.endsWith(".js")) return false // if users need to reuse js libs, they need to wrap them with ts signatures.
    
    val globalNamespace = TSNamespace()
    val sourceFile = TSSourceFile(program.getSourceFile(filename), globalNamespace)
    val importList = sourceFile.getImportList
    val reExportList = sourceFile.getReExportList
    cache.addOne(filename, globalNamespace)
    val relatedPath = TSModuleResolver.relative(workDir, TSModuleResolver.dirname(filename))

    def resolve(imp: String) = TypeScript.resolveModuleName(imp, filename, configContent).getOrElse("")

    val (moduleName, outputFilename) = outputOverride match {
      case Some(output) => (TSImport.getModuleName(output, false), output)
      case _ =>
        val moduleName = TSImport.getModuleName(filename, false)
        (moduleName, s"$relatedPath/$moduleName.mlsi")
    }

    val (cycleList, otherList) =
      importList.partition(imp => stack.contains(resolve(imp.filename)))

    otherList.foreach(imp => {
      generate(resolve(imp.filename), targetPath, outputOverride match {
        case Some(filename) =>
          val moduleName = TSImport.getModuleName(imp.filename, false)
          val dir = TSModuleResolver.dirname(filename)
          val rel = TSModuleResolver.dirname(imp.filename)
          Some(TSModuleResolver.normalize(s"$dir/$rel/$moduleName.mlsi"))
        case _ => resolveTarget(imp.filename)
      })(filename :: stack)
    })

    var writer = JSWriter(s"$targetPath/$outputFilename")
    val imported = new HashSet[String]()
    
    otherList.foreach(imp => {
      val name = TSImport.getModuleName(imp.filename, true)
      if (!imported(name) && !resolve(imp.filename).endsWith(".js")) {
        imported += name
        writer.writeln(s"""import "$name.mlsi"""")
      }
    })
    cycleList.foreach(imp => {
      writer.writeln(s"declare module ${TSImport.getModuleName(imp.filename, false)} {")
      cache(resolve(imp.filename)).generate(writer, "  ")
      writer.writeln("}")
    })

    reExportList.foreach {
      case TSReExport(alias, imp, memberName) =>
        val absName = resolve(imp)
        if (!cache.contains(absName))
          throw new AssertionError(s"unexpected re-export from ${imp}")
        else {
          val ns = cache(absName)
          val moduleName = TSImport.getModuleName(absName, false)
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
