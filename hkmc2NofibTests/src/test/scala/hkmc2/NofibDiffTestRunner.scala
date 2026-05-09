package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path
import io.PlatformPath.given

object NofibDiffTestState extends DiffTestRunner.State:

  override def testDir = TestFolders.nofibDiffDir(workingDir)

class NofibDiffTestRunner
  extends DiffTestRunnerBase(NofibDiffTestState)
  with ParallelTestExecution

