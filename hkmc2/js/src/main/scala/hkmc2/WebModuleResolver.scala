package hkmc2

import mlscript.utils.*, shorthands.*
import ModuleResolver.*

class WebModuleResolver(using fs: io.FileSystem) extends ModuleResolver:
  
  def tryResolveModulePath(path: Str): Opt[ResolvedModule] = N