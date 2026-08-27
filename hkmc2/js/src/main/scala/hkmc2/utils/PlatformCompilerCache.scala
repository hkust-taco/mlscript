package hkmc2
package utils

import collection.mutable.Map as MutMap

import CompilerCache.*


class PlatformCompilerCache extends CompilerCache:
  protected val elabCache = new ArtifactCache[Artifact](MutMap.empty, MutMap.empty)
  protected val preludeCache = new ArtifactCache[PreludeArtifact](MutMap.empty, MutMap.empty)
