package hkmc2

import hkmc2.utils.*, shorthands.*
import ModuleResolver.*

/** Browser resolver for imports that should not be treated as virtual files.
  *
  * Returning `N` still makes imports fall back to normal file-path resolution
  * against the worker's virtual filesystem. Package rules should be added here.
  */
class WebModuleResolver(using fs: io.FileSystem) extends ModuleResolver:
  
  def tryResolveModulePath(path: Str): Opt[ResolvedModule] =
    ModuleResolver.tryResolveUrl(path)
