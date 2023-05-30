package driver

import ts2mls.{TSModuleResolver, TypeScript}

final case class FileInfo(
  workDir: String, // work directory (related to compiler path)
  localFilename: String // filename (related to work dir, or in node_modules)
) {
  import TSModuleResolver.{normalize, isLocal, dirname, basename}

  val relatedPath: Option[String] = // related path (related to work dir, or none if it is in node_modules)
    if (TSModuleResolver.isLocal(localFilename)) Some(normalize(dirname(localFilename)))
    else None

  // module name in ts/mls
  val moduleName = basename(localFilename)

  // full filename (related to compiler path, or in node_modules)
  lazy val filename: String =
    if (relatedPath.isDefined) normalize(s"./$workDir/$localFilename")
    else TypeScript.resolveNodeModulePath(localFilename)

  val interfaceFilename: String = // interface filename (related to output directory)
    relatedPath.fold(s"node_modules/$localFilename")(path => s"${normalize(s"$path/$moduleName.mlsi")}")
  
  val jsFilename: Option[String] =
    relatedPath.fold[Option[String]](None)(path => Some(normalize(s"$path/$moduleName.js")))

  val importPath: String =
    relatedPath.fold(s"$moduleName.mlsi")(path => s"./${normalize(s"$path/$moduleName.mlsi")}")
  
  def `import`(path: String): FileInfo =
    if (isLocal(path))
      relatedPath match {
        case Some(value) => FileInfo(workDir, s"./${normalize(s"$value/$path")}")
        case _ => ??? // TODO:
      }
    else FileInfo(workDir, path)
}

object FileInfo {
  def importPath(filename: String): String =
    filename.replace(TSModuleResolver.extname(filename), ".mlsi")
}
