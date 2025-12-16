package hkmc2
package utils

import CompilerCache.Artifact
import collection.concurrent.{Map => ConcMap, TrieMap}
import mlscript.utils.*, shorthands.*

class PlatformCompilerCache extends CompilerCache:
  
  val elabCache: ConcMap[io.Path, Artifact] = TrieMap.empty
  
