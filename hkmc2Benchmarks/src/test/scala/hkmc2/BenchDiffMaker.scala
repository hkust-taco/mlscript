package hkmc2

import mlscript.utils._, shorthands._
import hkmc2.syntax.Tree
import hkmc2.syntax.Keyword

class BenchDiffMaker(val rootPath: Str, val file: io.Path, val preludeFile: io.Path, val predefFile: io.Path, val relativeName: Str)
  extends LlirDiffMaker:
  
  override def fs = io.FileSystem.default

  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(blk, inImport)
