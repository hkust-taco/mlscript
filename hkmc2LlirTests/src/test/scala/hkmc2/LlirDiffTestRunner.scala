package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path
import io.PlatformPath.given

object LlirDiffTestState extends DiffTestRunner.State:
  
  override def testDir = TestFolders.llirDiffDir(workingDir)

class LlirDiffTestRunner
  extends DiffTestRunnerBase(LlirDiffTestState)
  with ParallelTestExecution
