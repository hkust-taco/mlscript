package hkmc2
package utils

import CompilerCache.Artifact
import collection.concurrent.{Map => ConcMap, TrieMap}
import hkmc2.utils.*, shorthands.*

class PlatformCompilerCache extends CompilerCache:
  
  val elabCache: ConcMap[io.Path, Artifact] = TrieMap.empty
  
