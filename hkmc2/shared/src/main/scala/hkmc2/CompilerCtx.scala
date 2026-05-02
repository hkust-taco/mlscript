package hkmc2

import scala.collection.mutable
import scala.annotation.tailrec
import collection.mutable.Map as MutMap

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext
import hkmc2.io
import utils.TL

import semantics.*
import Elaborator.*
import hkmc2.syntax.LetBind


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
        (file: io.Path, prelude: Ctx, full: Bool)
        (using TL, Raise, Config)
        : Artifact =
    
    // println(s"Cache has: ${cache.elabCache.contains(file)} ${cache.elabCache.keys}")
    
    // * FIXME:
    // * This is not quite correct, but might be good enough for now
    // * (to be fixed when we overhaul the symbol and elaboration systems).
    // * The problem is that different modules will see different builtin symbols
    // * for things like `unitSymbol` and `termSymbol`, which could in theory cause problems
    // * if the compiler later wants to compare them as part of the type checking/compilation/optimization logic.
    // * Technically, we should also have the same problem with the symbols loaded from the prelude,
    // * which are passed on to imported modules from the first importer
    // * (and the "first importer" is nondeterministic, due to concurrent tests),
    // * and since the imported modules are cached,
    // * this means subsequent importers will not have see same prelude symbols.
    // * The correct approach should be to only cache a *single* State and prelude Ctx at the start,
    // * and reuse it for every compilation unit (each compilation unit duplicating the root State).
    given Elaborator.State = new Elaborator.State
    
    val lastMod = fs.getLastChangedTimestamp(file)
    
    def mk =
      val parse =
        given CompilerCtx = this
        ParserSetup(file, dbgParsing = false)
      val resBlk = parse.resultBlk
      val mode = if full then Mode.Full else Mode.Light
      given Elaborator.Ctx = prelude.copy(mode = mode).nestLocal("prelude")
      val elab =
        given CompilerCtx = derive(parse.origin.fileName)
        Elaborator(tl, file.up, prelude)
      val (blk, _) = elab.importFrom(resBlk)
      // Resolve once here so cached terms are not mutated again by later passes
      // (diamond imports would otherwise re-run Resolver and trip expand()).
      Resolver(summon[TL])(using summon[Raise], summon[State], summon[Ctx], summon[Config])
        .traverseBlock(blk)(using Resolver.ICtx.empty)
      Artifact(resBlk, blk, lastMod, full)
    
    cache.upsert(file):
      case N => mk
      case cur @ S(art) =>
        if art.lastChangedTimestamp < lastMod || !art.mode && full then mk
        else art

  def getCachedElaboratedBlock(file: io.Path, full: Bool): Opt[Artifact] =
    val lastMod = fs.getLastChangedTimestamp(file)
    cache.elabCache.get(file).filter: art =>
      art.lastChangedTimestamp >= lastMod && (art.mode || !full)
  
  
object CompilerCtx:
  
  inline def get(using cctx: CompilerCtx) = cctx
  
  def fresh(fs: io.FileSystem): CompilerCtx = CompilerCtx(N, Set.empty, fs, new PlatformCompilerCache)
  
end CompilerCtx



object CompilerCache:
  
  class Artifact(
      val tree: syntax.Tree.Block,
      val term: semantics.Term.Blk,
      val lastChangedTimestamp: Long,
      val mode: Bool,
  )
  
end CompilerCache


trait CompilerCache:
  // TODO also use hash comparison to avoid needless re-parses?
  
  def elabCache: MutMap[io.Path, Artifact]
  
  /** Create or update an artifact at the given path in the cache. */
  def upsert(path: io.Path)(update: Option[Artifact] => Artifact): Artifact =
    elabCache
      .updateWith(path):
        case N => S(update(N))
        case cur @ S(oldArt) =>
          val newArt = update(cur)
          if newArt is oldArt then cur else S(newArt)
      .get // * above, we always returns Some
  
end CompilerCache

