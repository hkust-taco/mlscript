package hkmc2
package utils

import CompilerCache.Artifact
import collection.mutable.Map as MutMap
import mlscript.utils.*, shorthands.*

class PlatformCompilerCache extends CompilerCache:
  
  val elabCache: MutMap[io.Path, Artifact] = MutMap.empty
  
