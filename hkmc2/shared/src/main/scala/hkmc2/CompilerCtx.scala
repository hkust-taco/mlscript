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
    
    cache.elabCache
      .updateWith(file):
        case N => S(mk)
        case cur @ S(art) =>
          if art.lastChangedTimestamp < lastMod then S(mk)
          else cur
      .get // * above, we always returns Some
  
  
object CompilerCtx:
  
  inline def get(using cctx: CompilerCtx) = cctx
  
  def fresh(fs: io.FileSystem): CompilerCtx = CompilerCtx(N, Set.empty, fs, new CompilerCache)
  
end CompilerCtx



object CompilerCache:
  
  class Artifact(val tree: syntax.Tree.Block, val term: semantics.Term.Blk, val lastChangedTimestamp: Long)
  
end CompilerCache


class CompilerCache:
  
  // TODO also use hash comparison to avoid needless re-parses?
  
  import collection.concurrent.{Map => ConcMap, TrieMap}
  val elabCache: ConcMap[io.Path, Artifact] = TrieMap.empty
  
  
end CompilerCache



