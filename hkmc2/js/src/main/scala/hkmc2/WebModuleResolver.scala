package hkmc2

import mlscript.utils.*, shorthands.*
import ModuleResolver.*

/** Placeholder resolver for browser compilation.
  *
  * Returning `N` makes imports fall back to normal file-path resolution against
  * the worker's virtual filesystem. Package and URL rules should be added here.
  */
class WebModuleResolver(using fs: io.FileSystem) extends ModuleResolver:
  
  def tryResolveModulePath(path: Str): Opt[ResolvedModule] = N
