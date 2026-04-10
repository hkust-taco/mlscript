package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path
import io.PlatformPath.given

object AppsDiffTestState extends DiffTestRunner.State:
  
  override def testDir = TestFolders.appsDiffDir(workingDir)

class AppsDiffTestRunner
  extends DiffTestRunnerBase(AppsDiffTestState)
  with ParallelTestExecution

