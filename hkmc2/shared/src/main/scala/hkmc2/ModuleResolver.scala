package hkmc2

import mlscript.utils.*, shorthands.*

trait ModuleResolver:
  /**
    * Try to resolve path if it refers to a module or a source file in a module.
    *
    * @param path the import path
    * @return the resolved path and module identifier, if any.
    */
  def tryResolveModulePath(path: Str): Opt[(Str \/ io.Path, Opt[Str])]

/**
  * For local tests, including `CompileTestRunner`, `DiffTestRunner`, etc.
  *
  * @param stdPath the path to the standard library folder
  * @param nodeModulesPath the optional path to the `node_modules` folder.
  *                        If provided, we will do a simple check to see if
  *                        the requested Node.js built-in module exists.
  */
class LocalTestModuleResolver(stdPath: io.Path, nodeModulesPath: Opt[io.Path])(using fs: io.FileSystem) extends ModuleResolver:
  import LocalTestModuleResolver.*
  
  private def existsNodeModule(orgNameOpt: Opt[Str], moduleName: Str): Bool =
    nodeModulesPath match
    case S(basePath) =>
      val packagePath = orgNameOpt match
        case S(orgName) => basePath / s"@$orgName" / moduleName
        case N => basePath / moduleName
      fs.exists(packagePath)
    case N => false
  
  /**
    * Resolve an imported module name to a directory (or file) path. This method
    * should be overridden by subclasses to provide module resolution logic.
    *
    * @param orgName the optional organization name of the module
    * @param moduleName the name of the module being imported
    * @param noSubPath if the import does not have a sub-path (i.e., only the module name)
    * @return the pure module name or the resolved path
    */
  private def resolveModule(orgName: Opt[Str], moduleName: Str, noSubPath: Bool): Opt[(Str \/ io.Path, Opt[Str])] =
    // Currently, there is only one std module, so the implementation here is
    // hard-coded. If one day we implement the mechanism of a module manifest
    // (for example, through `.mlson` file or `.witton` file), this part will
    // need to be updated accordingly.
    if orgName.isEmpty then
      if noSubPath then
        val realName = if moduleName.startsWith("node:") then moduleName.drop(5) else moduleName
        if allowedNodeJsModules contains realName then S(L(moduleName) -> S(realName))
        else if existsNodeModule(orgName, moduleName) then S(L(moduleName) -> N)
        else N
      else if moduleName == "std" then S(R(stdPath) -> N)
      else N
    else N
  
  def tryResolveModulePath(path: Str): Opt[(Str \/ io.Path, Opt[Str])] = path match
    case r(orgName, modName, subPath) =>
      val orgNameOpt = Opt(orgName)
      if subPath is null then
        resolveModule(orgNameOpt, modName, true)
      else
        val res = resolveModule(orgNameOpt, modName, false).map:
          case (R(p), id) => (R(p / io.RelPath(subPath)), id)
          case other => other
        res
    case _ => N

object LocalTestModuleResolver:
  def apply(stdPath: io.Path, nodeModulesPath: Opt[io.Path] = N)(using fs: io.FileSystem): LocalTestModuleResolver =
    new LocalTestModuleResolver(stdPath, nodeModulesPath)
  
  /**
    * The pattern of valid Node.js module specifiers.
    * 
    * 1. **Group 1:** Scope (no `@`)
    *      + Example: `@my-org/foo/bar` → `"my-org"`
    * 2. **Group 2:** Package name
    *      + Example: `@my-org/foo/bar` → `"foo"`
    *      + Example: `mypkg/test` → `"mypkg"`
    * 3. **Group 3:** The remaining text after the first slash
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

// TODO: WebModuleResolver that can resolve URL imports.
