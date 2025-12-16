package hkmc2

import scala.collection.mutable
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext
import hkmc2.io
import utils.TraceLogger

import semantics.*
import Elaborator.*
import hkmc2.syntax.LetBind
import hkmc2.bbml.cctx


import CompilerCache.*


class CompilerCtx(
    val importing: Opt[(io.Path, CompilerCtx)],
    val beingCompiled: Set[io.Path],
    val fs: io.FileSystem,
    cache: CompilerCache,
):
  
  def allFilesBeingImported: Ls[io.Path] =
    importing match
    case S((path, parent)) => path :: parent.allFilesBeingImported
    case N => Nil
  
  def derive(newFile: io.Path): CompilerCtx =
    CompilerCtx(S(newFile, this), beingCompiled + newFile, fs, cache)
  
  def getElaboratedBlock
        (file: io.Path, prelude: Ctx)
        (using TL, State, Raise, Config)
        : Artifact =
    
    // println(s"Cache has: ${cache.elabCache.contains(file)} ${cache.elabCache.keys}")
    
    val lastMod = file.lastChangedTimestamp
    
    def mk =
      val parse =
        given CompilerCtx = this
        ParserSetup(file, dbgParsing = false)
      val resBlk = parse.resultBlk
      given Elaborator.Ctx = prelude.copy(mode = Mode.Light).nestLocal("prelude")
      val elab =
        given CompilerCtx = derive(parse.origin.fileName)
        Elaborator(tl, file.up, prelude)
      val elabbed = elab.importFrom(resBlk)
      Artifact(resBlk, elabbed._1, lastMod)
    
    cache.upsert(file):
      case N => mk
      case cur @ S(art) =>
        if art.lastChangedTimestamp < lastMod then mk
        else art
  
  
object CompilerCtx:
  
  inline def get(using cctx: CompilerCtx) = cctx
  
  def fresh(fs: io.FileSystem): CompilerCtx = CompilerCtx(N, Set.empty, fs, CompilerCache())
  
end CompilerCtx



object CompilerCache:
  
  def apply(): CompilerCache = PlatformCompilerCache()
  
  class Artifact(val tree: syntax.Tree.Block, val term: semantics.Term.Blk, val lastChangedTimestamp: Long)
  
end CompilerCache


trait CompilerCache:
  
  /** Create or update an artifact at the given path in the cache. */
  def upsert(path: io.Path)(update: Option[Artifact] => Artifact): Artifact
  
end CompilerCache



