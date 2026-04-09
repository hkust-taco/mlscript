package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path
import io.PlatformPath.given

object NofibDiffTestState extends DiffTestRunner.State:

  override val allFiles = os.walk(dir/"mlscript"/"nofib")
    .filter(_.toIO.isFile)
    .filter(_.ext == "mls")

class NofibDiffTestRunner
  extends DiffTestRunnerBase(NofibDiffTestState)
  with ParallelTestExecution

