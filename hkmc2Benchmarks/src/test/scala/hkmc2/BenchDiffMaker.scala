package hkmc2

import mlscript.utils._, shorthands._
import hkmc2.syntax.Tree
import hkmc2.syntax.Keyword


class BenchDiffMaker
    (val rootPath: Str, val file: io.Path, val preludeFile: io.Path, val predefFile: io.Path, val relativeName: Str)
    (using val cctx: CompilerCtx)
  extends InvalMLDiffMaker:
  
  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(blk, inImport)


