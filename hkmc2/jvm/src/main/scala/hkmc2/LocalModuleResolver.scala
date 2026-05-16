
package hkmc2

import mlscript.utils.*, shorthands.*
import ModuleResolver.*
import io.PlatformPath.{given}
import LocalModuleResolver.Vendor

/**
  * For local tests, including `CompileTestRunner`, `DiffTestRunner`, etc.
  *
  * @param vendors the list of vendor paths.
  * @param nodeModulesPath the optional path to the `node_modules` folder.
  *                        If provided, we will do a simple check to see if
  *                        the requested Node.js built-in module exists.
  */
class LocalModuleResolver(vendors: Ls[Vendor], nodeModulesPath: Opt[io.Path])(using fs: io.FileSystem) extends ModuleResolver:
  import LocalModuleResolver.*
  
  private def existsNodeModule(orgNameOpt: Opt[Str], moduleName: Str): Bool =
    nodeModulesPath match
    case S(basePath) =>
      val packagePath = orgNameOpt match
        case S(orgName) => basePath / s"@$orgName" / moduleName
        case N => basePath / moduleName
      fs.exists(packagePath)
    case N => false
  
  protected def tryVerbatim(path: Str): Opt[ResolvedModule.Verbatim] = path match
    case r(rawOrgName, modName, rawSubPath) => 
      val importedName = Opt(rawSubPath) match
        case S(subPath) => io.RelPath(subPath).baseName
        case N if modName.startsWith("node:") => modName.drop(5)
        case N => modName
      val exists = Opt(rawOrgName) match
        case orgNameOpt @ S(_) => existsNodeModule(orgNameOpt, modName)
        case N if modName.startsWith("node:") =>
          allowedNodeJsModules.contains(modName.drop(5))
        case N => allowedNodeJsModules.contains(modName) || existsNodeModule(N, modName)
      if exists then S(ResolvedModule.Verbatim(path, importedName)) else N
    case _ => N
  
  protected def tryFile(rawPath: Str): Opt[ResolvedModule] =
    vendors.iterator.map:
      case vendor @ Vendor(prefix, path, patterns) if rawPath.startsWith(prefix) =>
        val relativePath = io.RelPath(rawPath.drop(prefix.length))
        val absolutePath = path / relativePath
        if vendor.files.contains(absolutePath) then
          S(ResolvedModule.File(absolutePath, absolutePath, relativePath.baseName))
        else
          N
      case _ => N
    .collectFirst:
      case S(resolved) => resolved
  
  def tryResolveModulePath(path: Str): Opt[ResolvedModule] =
    ModuleResolver.tryResolveUrl(path) orElse tryVerbatim(path) orElse tryFile(path)

object LocalModuleResolver:
  def apply(stdPath: io.Path, nodeModulesPath: Opt[io.Path] = N)(using fs: io.FileSystem): LocalModuleResolver =
    val vendors = Vendor("std/", stdPath, Ls("*.mls", "**/*.mls")) :: Nil
    new LocalModuleResolver(vendors, nodeModulesPath)
  
  import java.nio.file.FileSystems
  
  case class Vendor(prefix: Str, path: io.Path, patterns: Ls[Str]):
    val files: Ls[io.Path] = patterns.iterator.flatMap: pattern =>
      val m = FileSystems.getDefault.getPathMatcher(s"glob:$pattern")
      os.walk(path).iterator.filter: p =>
        m.matches(path.toNIO.relativize(p.toNIO))
      .map(io.PlatformPath.fromOsPath(_))
    .toList
    
    println(s"Vendor $prefix: found ${"file" countBy files.length}")
    files.foreach: file =>
      println(s"- $file")
  
  /**
    * The pattern of valid Node.js module specifiers.
    * 
    * 1. **Group 1:** `@([a-z0-9-~][a-z0-9-._~]*)\/`
    *      + Meaning: Scope (no `@`)
    *      + Example: `@my-org/foo/bar` → `"my-org"`
    * 2. **Group 2:** `(?:node:)?[a-z0-9-~][a-z0-9-._~]*`
    *      + Meaning: Package name with optional `node:` prefix
    *      + Example: `@my-org/foo/bar` → `"foo"`
    *      + Example: `mypkg/test` → `"mypkg"`
    * 3. **Group 3:** `\/(.*)`
    *      + Meaning: The remaining text after the first slash
    *      + Example: `@my-org/foo/bar/baz` → `"bar/baz"`
    *      + Example: `mypkg/sub/path` → `"sub/path"`
    *      + Example: `mypkg` → `null`
    */
  private val r = """^(?:@([a-z0-9-~][a-z0-9-._~]*)\/)?((?:node:)?[a-z0-9-~][a-z0-9-._~]*)(?:\/(.*))?$""".r
  
  /**
    * An incomplete list of allowed Node.js built-in modules. Add more as needed.
    */
  private val allowedNodeJsModules = Set(
    "fs", "path", "http", "https", "url", "util", "events", "stream", "buffer",
    "os", "child_process", "vm", "assert", "tty", "process")
