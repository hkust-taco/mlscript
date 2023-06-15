package ts2mls

import scala.scalajs.js
import ts2mls.{TypeScript, TSImport}
import ts2mls.TSPathResolver

final case class FileInfo(
  workDir: String, // work directory (related to compiler path)
  localFilename: String, // filename (related to work dir, or in node_modules)
  interfaceDir: String, // .mlsi file directory (related to output dir)
  parent: Option[String] = None, // file that imports this (related to work dir)
  nodeModulesNested: Boolean = false // if it is a local file in node_modules
) {
  import TSPathResolver.{normalize, isLocal, dirname, basename, extname}

  val relatedPath: Option[String] = // related path (related to work dir, or none if it is in node_modules)
    if (isLocal(localFilename)) Some(normalize(dirname(localFilename)))
    else None

  val isNodeModule: Boolean = nodeModulesNested || relatedPath.isEmpty

  // module name in ts/mls
  val moduleName = basename(localFilename)

  // full filename (related to compiler path, or module name in node_modules)
  lazy val filename: String =
    if (!isNodeModule) normalize(s"./$workDir/$localFilename")
    else if (nodeModulesNested) localFilename
    else localFilename.replace(extname(localFilename), "")

  lazy val importedMlsi: String =
    FileInfo.importPath(
      if (!isNodeModule) localFilename
      else if (nodeModulesNested) {
        val p = dirname(TSImport.createInterfaceForNode(parent.getOrElse(workDir)))
        s"./${normalize(TSPathResolver.relative(p, localFilename))}"
      }
      else filename
    )

  def resolve(implicit config: js.Dynamic) =
    if (isNodeModule && !nodeModulesNested) TypeScript.resolveModuleName(filename, parent.getOrElse(""), config)
    else if (nodeModulesNested) TypeScript.resolveModuleName(s"./$moduleName", parent.getOrElse(""), config)
    else TSPathResolver.resolve(filename)

  def interfaceFilename(implicit config: js.Dynamic): String = // interface filename (related to work directory)
    relatedPath.fold(
      s"$interfaceDir/${dirname(TSImport.createInterfaceForNode(resolve))}/${moduleName}.mlsi"
    )(path => s"${normalize(s"$interfaceDir/$path/$moduleName.mlsi")}")
  
  val jsFilename: String =
    relatedPath.fold(filename)(path => normalize(s"$path/$moduleName.js"))

  def `import`(path: String)(implicit config: js.Dynamic): FileInfo =
    if (isLocal(path))
      relatedPath match {
        case Some(value) =>
          if (path.endsWith(".mls") || path.endsWith(".mlsi"))
            FileInfo(workDir, s"./${normalize(s"$value/$path")}", interfaceDir, Some(resolve))
          else {
            val res = TypeScript.resolveModuleName(s"./${dirname(path)}/${basename(path)}", resolve, config)
            val absWordDir = TSPathResolver.resolve(workDir)
            FileInfo(workDir, s"./${TSPathResolver.relative(absWordDir, res)}", interfaceDir, Some(resolve))
          }
        case _ =>
          val currentPath = dirname(TSImport.createInterfaceForNode(resolve))
          FileInfo(workDir, s"./$currentPath/$path", interfaceDir, Some(resolve), true)
      }
    else FileInfo(workDir, path, interfaceDir, Some(resolve))
}

object FileInfo {
  def importPath(filename: String): String =
    if (filename.endsWith(".mls") || filename.endsWith(".ts"))
      filename.replace(TSPathResolver.extname(filename), ".mlsi")
    else filename + ".mlsi"
}
