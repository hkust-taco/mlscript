package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}

import hkmc2.utils.*, shorthands.*


abstract class MainDiffMaker
    (val rootPath: Str, val file: io.Path, val preludeFile: io.Path, val predefFile: io.Path, val relativeName: Str)
  extends WasmDiffMaker:
    
    // println(s"Running diff test for $relativeName") // * useful to debug nonterminating tests
    
end MainDiffMaker

