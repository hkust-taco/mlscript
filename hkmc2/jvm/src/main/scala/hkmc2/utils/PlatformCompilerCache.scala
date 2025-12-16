package hkmc2
package utils

import CompilerCache.Artifact
import collection.concurrent.{Map => ConcMap, TrieMap}
import mlscript.utils.*, shorthands.*

class PlatformCompilerCache extends CompilerCache:
  // TODO also use hash comparison to avoid needless re-parses?
  
  val elabCache: ConcMap[io.Path, Artifact] = TrieMap.empty
  
  def upsert(path: io.Path)(update: Option[Artifact] => Artifact): Artifact =
    elabCache
      .updateWith(path):
        case N => S(update(N))
        case cur @ S(oldArt) =>
          val newArt = update(cur)
          if newArt is oldArt then cur else S(newArt)
      .get // * above, we always returns Some

object PlatformCompilerCache:
  def apply(): CompilerCache = new PlatformCompilerCache()
