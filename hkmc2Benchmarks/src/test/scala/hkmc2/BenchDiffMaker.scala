package hkmc2

import mlscript.utils._, shorthands._
import hkmc2.syntax.Tree
import hkmc2.syntax.Keyword

class BenchDiffMaker(val rootPath: Str, val file: os.Path, val preludeFile: os.Path, val predefFile: os.Path, val relativeName: Str)
  extends LlirDiffMaker:

  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(blk, inImport)
