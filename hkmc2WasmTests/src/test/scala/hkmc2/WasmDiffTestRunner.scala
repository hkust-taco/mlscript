package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import hkmc2.utils._
import os.Path
import io.PlatformPath.given

object WasmDiffTestState extends DiffTestRunner.State:

  override def testDir = TestFolders.wasmDiffDir(workingDir)

class WasmDiffTestRunner
  extends DiffTestRunnerBase(WasmDiffTestState)
  with ParallelTestExecution
