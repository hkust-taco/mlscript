package hkmc2.codegen.cpp

import mlscript._
import mlscript.utils.shorthands._
import scala.collection.mutable.ListBuffer

final class CppCompilerHost(val auxPath: Str, val output: Str => Unit):
  import scala.sys.process._
  private def ifAnyCppCompilerExists(): Boolean =
    Seq("g++", "--version").! == 0 || Seq("clang++", "--version").! == 0

  private def isMakeExists(): Boolean =
    import scala.sys.process._
    Seq("make", "--version").! == 0

  val ready = ifAnyCppCompilerExists() && isMakeExists()
  
  def compileAndRun(src: Str): Unit =
    if !ready then
      return
    val srcPath = os.temp(contents = src, suffix = ".cpp")
    val binPath = os.temp(suffix = ".mls.out")
    var stdout = ListBuffer[Str]()
    var stderr = ListBuffer[Str]()
    val buildLogger = ProcessLogger(stdout :+= _, stderr :+= _)
    val buildResult = Seq("make", "-B", "-C", auxPath, "auto", s"SRC=$srcPath", s"DST=$binPath") ! buildLogger
    if buildResult != 0 then
      output("Compilation failed: ")
      for line <- stdout do output(line)
      for line <- stderr do output(line)
      return
  
    stdout.clear()
    stderr.clear()
    val runCmd = Seq(binPath.toString)
    val runResult = runCmd ! buildLogger
    if runResult != 0 then
      output("Execution failed: ")
      for line <- stdout do output(line)
      for line <- stderr do output(line)
      return

    output("Execution succeeded: ")
    for line <- stdout do output(line)