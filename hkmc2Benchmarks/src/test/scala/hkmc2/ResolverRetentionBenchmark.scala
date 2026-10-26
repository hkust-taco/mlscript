package hkmc2

import java.lang.management.ManagementFactory
import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


/** Run in a fresh JVM after compiling the benchmark project. Timings cover
  * uncached compilation through optimization, excluding JVM startup, prelude
  * setup, fixture creation and Scala compilation. Each sample owns a fresh
  * compiler cache; the import workload precompiles its shared source library.
  * Explicit GC between samples is outside the timed region. Keep the returned
  * artifacts alive until the next sample so every variant does the same work.
  */
object ResolverRetentionBenchmark:
  private var result: Any = ()

  def main(args: Array[String]): Unit =
    require(args.length == 5, "Usage: <revision> <fork> <warmups> <samples> <output.csv>")
    val Array(revision, forkText, warmupText, sampleText, outputText) = args: @unchecked
    val fork = forkText.toInt
    val warmups = warmupText.toInt
    val samples = sampleText.toInt
    require(warmups > 0 && samples > 0)
    val output = os.Path(outputText, os.pwd)
    val dir = os.temp.dir(prefix = "resolver-benchmark-")
    val library = dir / "Library.mls"
    os.write(library,
      """#lang(0.3.x, strictResolution: true)
        |module Library with
        |  fun identity[A](value: A) = value
        |  fun pair[A](value: A) = [value, {item: value}]
        |""".stripMargin)
    val consumers = (0 until 12).map: index =>
      val file = dir / s"Consumer$index.mls"
      os.write(file,
        s"""#lang(0.3.x, strictResolution: true)
           |import "./Library.mls"
           |module Consumer$index with
           |  class Item(val value: Int)
           |  fun run() = [Library.identity(Item(1)).value, Library.pair(Item(2)).0.value]
           |""".stripMargin)
      file
    val privateBodies = dir / "PrivateBodies.mls"
    val bodies = (0 until 200).map: index =>
      s"""  private fun unused$index[A](value: A) =
         |    fun wrap[B](item: B) = [item, {stored: item}]
         |    wrap[A](value)""".stripMargin
    os.write(privateBodies,
      "#lang(0.3.x, strictResolution: true)\nmodule PrivateBodies with\n  fun identity[A](value: A) = value\n" +
        bodies.mkString("\n") + "\n")
    val workloads = Vector("finger-tree", "generic-imports", "private-bodies")
    val cpu = ManagementFactory.getThreadMXBean
    require(cpu.isCurrentThreadCpuTimeSupported, "The benchmark requires thread CPU timing")
    cpu.setThreadCpuTimeEnabled(true)
    if !os.exists(output) then os.write(output, "revision,fork,workload,sample,wall_ms,cpu_ms\n", createFolders = true)
    try
      for iteration <- 0 until warmups + samples do
        for offset <- workloads.indices do
          val workload = workloads((offset + iteration + fork) % workloads.size)
          result = ()
          System.gc()
          val cctx = TestFolders.compilerCtx(os.pwd)
          given DebugPrinter = new DebugPrinter()
          val trace = TraceLogger.silent
          given Raise = diagnostic => throw new IllegalStateException(diagnostic.theMsg.toString)
          val prelude = cctx.getPrelude(cctx.paths.preludeFile)(using trace, summon[Raise]).ctx
          cctx.getElaboratedBlock(cctx.paths.runtimeSourceFile, prelude)(using trace, summon[Raise])
          if workload == "generic-imports" then cctx.getElaboratedBlock(library, prelude)(using trace, summon[Raise])
          val files = workload match
            case "finger-tree" => Seq(TestFolders.compileTestDir(os.pwd) / "FingerTreeList.mls")
            case "generic-imports" => consumers
            case "private-bodies" => Seq(privateBodies)
            case other => throw new IllegalArgumentException(s"Unknown workload: $other")
          val cpuStart = cpu.getCurrentThreadCpuTime
          val start = System.nanoTime()
          result = files.map(file => cctx.getElaboratedBlock(file, prelude)(using trace, summon[Raise]))
          val wallMs = (System.nanoTime() - start) / 1000000.0
          val cpuMs = (cpu.getCurrentThreadCpuTime - cpuStart) / 1000000.0
          if iteration >= warmups then
            val row = s"$revision,$fork,$workload,${iteration - warmups},$wallMs,$cpuMs\n"
            os.write.append(output, row)
            print(row)
    finally os.remove.all(dir)
