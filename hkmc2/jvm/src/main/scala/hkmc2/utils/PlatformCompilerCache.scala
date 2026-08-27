package hkmc2
package utils

import collection.concurrent.TrieMap

import CompilerCache.*


class PlatformCompilerCache extends CompilerCache:
  protected val elabCache = new ArtifactCache[Artifact](TrieMap.empty, TrieMap.empty)
  protected val preludeCache = new ArtifactCache[PreludeArtifact](TrieMap.empty, TrieMap.empty)
