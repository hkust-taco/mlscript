package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._


class MainDiffMaker(val rootPath: Str, val file: os.Path, val preludeFile: os.Path, val predefFile: os.Path, val relativeName: Str)
  extends LlirDiffMaker


