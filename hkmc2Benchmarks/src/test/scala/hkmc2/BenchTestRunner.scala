package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path
import io.PlatformPath.given

object BenchTestState extends DiffTestRunner.State:

  override val allFiles = os.walk(workingDir/"hkmc2Benchmarks"/"src"/"test"/"bench")
    .filter(_.toIO.isFile)
    .filter(_.ext == "mls")

  override val TimeLimit = Span(1, Hour)

class BenchTestRunner
  extends DiffTestRunnerBase(BenchTestState)
  with ParallelTestExecution
:
  override protected def createDiffMaker
      (file: Path, preludePath: Path, predefPath: Path, relativeName: String)
      : DiffMaker =
    new BenchDiffMaker(state.workingDir.toString, file, preludePath, predefPath, relativeName)(using state.cctx)

