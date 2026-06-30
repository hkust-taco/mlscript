package hkmc2

import hkmc2.utils.*, shorthands.*
import ModuleResolver.*

trait ModuleResolver:
  /**
    * Try to resolve path if it refers to a module or a source file in a module.
    *
    * @param path the import path
    * @return the resolved path and module identifier, if any.
    */
  def tryResolveModulePath(path: Str): Opt[ResolvedModule]
  
  /** Try to resolve a module path from a specific source directory. */
  def tryResolveModulePath(path: Str, from: io.Path): Opt[ResolvedModule] =
    tryResolveModulePath(path)
  
  /**
    * Return the generated JavaScript target path for a source file when it is
    * compiled somewhere other than beside the source.
    */
  def targetPathForSource(sourcePath: io.Path): Opt[io.Path] = N

object ModuleResolver:
  def isUrlModuleSpecifier(path: Str): Bool =
    path.startsWith("https://") || path.startsWith("http://")
  
  def urlModuleName(path: Str): Str =
    val withoutFragment = path.takeWhile(ch => ch =/= '#' && ch =/= '?').stripSuffix("/")
    val lastSegment = withoutFragment.split('/').lastOption.getOrElse("module")
    val sanitized = lastSegment.map:
      case ch if ch.isLetterOrDigit || ch === '_' || ch === '$' => ch
      case _ => '_'
    val nonEmpty = if sanitized.isEmpty then "module" else sanitized
    if nonEmpty.headOption.exists(_.isDigit) then "_" + nonEmpty else nonEmpty
  
  def tryResolveUrl(path: Str): Opt[ResolvedModule.Verbatim] =
    // For URLs, we just return the path as-is.
    if isUrlModuleSpecifier(path) then S(ResolvedModule.Verbatim(path, urlModuleName(path)))
    else N
  
  /** The result of module resolution. */
  enum ResolvedModule:
    /** The module's name, to be used as the identifier. */
    val moduleName: Str
    
    /**
      * The module specifier will be used as-is, e.g., built-in modules, or any
      * modules that are resolved by the runtime.
      *
      * @param specifier the module specifier used in the import statement.
      * @param moduleName the module's name, to be used as the identifier.
      */
    case Verbatim(specifier: Str, moduleName: Str)
    
    /**
      * The module is resolved to a local file.
      *
      * @param sourcePath the path to the source code, ending with `.mls`.
      * @param targetPath the path to the compiled code, used in the import
      *                   statements in the generated JavaScript files.
      * @param moduleName the module's name, to be used as the identifier.
      */
    case File(sourcePath: io.Path, targetPath: io.Path, moduleName: Str)
