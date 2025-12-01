package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}

import mlscript.utils._, shorthands._


abstract class MainDiffMaker(val rootPath: Str, val file: io.Path, val preludeFile: io.Path, val predefFile: io.Path, val relativeName: Str)
  extends WasmDiffMaker


