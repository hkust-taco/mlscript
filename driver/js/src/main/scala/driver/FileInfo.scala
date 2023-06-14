package driver

import scala.scalajs.js
import ts2mls.{TypeScript, TSImport}
import ts2mls.TSPathResolver

final case class FileInfo(
  workDir: String, // work directory (related to compiler path)
  localFilename: String, // filename (related to work dir, or in node_modules)
  interfaceDir: String, // .mlsi file directory (related to output dir)
) {
  import TSPathResolver.{normalize, isLocal, dirname, basename, extname}

  val relatedPath: Option[String] = // related path (related to work dir, or none if it is in node_modules)
    if (isLocal(localFilename)) Some(normalize(dirname(localFilename)))
    else None

  val isNodeModule: Boolean = relatedPath.isEmpty

  // module name in ts/mls
  val moduleName = basename(localFilename)

  // full filename (related to compiler path, or in node_modules)
  lazy val filename: String =
    if (!isNodeModule) normalize(s"./$workDir/$localFilename")
    else localFilename.replace(extname(localFilename), "")

  private def resolveNodeModule(implicit config: js.Dynamic) =
    if (!isNodeModule) throw new AssertionError(s"$filename is not a node module")
    else TypeScript.resolveModuleName(filename, "", config).getOrElse(
      throw new AssertionError(s"can not find node module $filename")
    )

  def interfaceFilename(implicit config: js.Dynamic): String = // interface filename (related to output directory)
    relatedPath.fold(
      s"$interfaceDir/${dirname(TSImport.createInterfaceForNode(resolveNodeModule))}/${moduleName}.mlsi"
    )(path => s"${normalize(s"$interfaceDir/$path/$moduleName.mlsi")}")
  
  val jsFilename: String =
    relatedPath.fold(moduleName)(path => normalize(s"$path/$moduleName.js"))

  def `import`(path: String)(implicit config: js.Dynamic): FileInfo =
    if (isLocal(path))
      relatedPath match {
        case Some(value) => FileInfo(workDir, s"./${normalize(s"$value/$path")}", interfaceDir)
        case _ =>
          val currentPath = dirname(TSImport.createInterfaceForNode(resolveNodeModule))
          FileInfo(workDir, s"./$currentPath/$path", interfaceDir)
      }
    else FileInfo(workDir, path, interfaceDir)
}

object FileInfo {
  def importPath(filename: String): String =
    if (filename.endsWith(".mls") || filename.endsWith(".ts"))
      filename.replace(TSPathResolver.extname(filename), ".mlsi")
    else filename + ".mlsi"
}
