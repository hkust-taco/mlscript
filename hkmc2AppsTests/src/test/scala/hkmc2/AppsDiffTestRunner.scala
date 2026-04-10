package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path
import io.PlatformPath.given

object AppsDiffTestState extends DiffTestRunner.State:

  override val allFiles = TestFolders.appsDiffDirs(workingDir).flatMap(dir =>
    os.walk(dir)
      .filter(_.toIO.isFile)
      .filter(_.ext == "mls")
  ).toIndexedSeq

class AppsDiffTestRunner
  extends DiffTestRunnerBase(AppsDiffTestState)
  with ParallelTestExecution

