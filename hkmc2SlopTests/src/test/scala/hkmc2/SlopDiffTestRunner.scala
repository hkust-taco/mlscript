package hkmc2

import org.scalatest.ParallelTestExecution


object SlopDiffTestState extends DiffTestRunner.State:

  override def testDir = TestFolders.slopDiffDir(workingDir)

class SlopDiffTestRunner
  extends DiffTestRunnerBase(SlopDiffTestState)
  with ParallelTestExecution
