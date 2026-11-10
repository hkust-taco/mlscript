package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import hkmc2.utils._
import os.Path
import io.PlatformPath.given

object HandlerDiffTestState extends DiffTestRunner.State:

  override def testDir = TestFolders.handlerDiffDir(workingDir)

class HandlerDiffTestRunner
  extends DiffTestRunnerBase(HandlerDiffTestState)
  with ParallelTestExecution

