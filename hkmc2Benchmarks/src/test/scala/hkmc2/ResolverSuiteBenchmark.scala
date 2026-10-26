package hkmc2

import java.lang.management.ManagementFactory
import java.lang.ref.{Reference, WeakReference}
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicInteger
import org.scalatest.{Args, Reporter}
import org.scalatest.events.{Event, SuiteAborted, TestFailed, TestSucceeded}
import scala.jdk.CollectionConverters.*

import hkmc2.utils.*, shorthands.*


/** Run every ctest case sequentially in sorted order, repeatedly in one JVM.
  * Each batch shares a fresh CompilerCtx across all files, including imports,
  * prelude setup, JS generation and output writes. No explicit GC occurs during
  * the timing/allocation loop.
  * A separate final batch measures the heap held by the completed session.
  */
object ResolverSuiteBenchmark:
  private final class Batch(context: CompilerCtx) extends CompileTestRunnerBase(
    compileDirs = TestFolders.mainCompileDirs(os.pwd),
    excludedDirs = TestFolders.mainExcludedCompileDirs(os.pwd),
  ):
    protected def cctx: CompilerCtx =
      require(context != null, "The compilation session must be available during suite construction")
      context
    override def newInstance: Batch = new Batch(context)

  private final class Results extends Reporter:
    val succeeded = new AtomicInteger
    val failures = new ConcurrentLinkedQueue[String]
    def apply(event: Event): Unit = event match
      case _: TestSucceeded => succeeded.incrementAndGet(); ()
      case failed: TestFailed => failures.add(s"${failed.testName}: ${failed.message}"); ()
      case aborted: SuiteAborted => failures.add(aborted.message); ()
      case _ => ()

  def main(args: Array[String]): Unit =
    require(args.length == 5, "Usage: <revision> <fork> <warmups> <samples> <output-directory>")
    val Array(revision, fork, warmupText, sampleText, outputText) = args: @unchecked
    val warmups = warmupText.toInt
    val samples = sampleText.toInt
    require(warmups > 0 && samples > 0)
    require(Runtime.getRuntime.availableProcessors() == 1, "Run with -XX:ActiveProcessorCount=1")
    val output = os.Path(outputText, os.pwd)
    os.makeDir.all(output)
    val allocation = ManagementFactory.getThreadMXBean match
      case bean: com.sun.management.ThreadMXBean => bean
      case _ => throw new UnsupportedOperationException("JVM allocation counters are unavailable")
    require(allocation.isThreadAllocatedMemorySupported)
    allocation.setThreadAllocatedMemoryEnabled(true)
    require(allocation.getTotalThreadAllocatedBytes >= 0, "A JVM-wide allocation counter is required")
    val process = ManagementFactory.getOperatingSystemMXBean match
      case bean: com.sun.management.OperatingSystemMXBean => bean
      case _ => throw new UnsupportedOperationException("Process CPU timing is unavailable")
    val memory = ManagementFactory.getMemoryMXBean
    val compilation = ManagementFactory.getCompilationMXBean
    require(compilation.isCompilationTimeMonitoringSupported)
    val collectors = ManagementFactory.getGarbageCollectorMXBeans.asScala.toVector
    def gcCount: Long = collectors.map(_.getCollectionCount).sum
    def gcMillis: Long = collectors.map(_.getCollectionTime).sum
    def collectedHeap(): Long =
      val before = gcCount
      System.gc()
      require(gcCount > before, "The retained-heap measurement requires a completed explicit GC")
      memory.getHeapMemoryUsage.getUsed
    val manifest = new Batch(TestFolders.compilerCtx(os.pwd)).testNames.toVector.sorted
    val manifestFile = output / "ctest-manifest.txt"
    val manifestText = manifest.mkString("", "\n", "\n")
    if os.exists(manifestFile) then require(os.read(manifestFile) == manifestText, "The ctest corpus changed")
    else os.write(manifestFile, manifestText)
    def compileBatch(): CompilerCtx =
      val context = TestFolders.compilerCtx(os.pwd)
      val batch = new Batch(context)
      require(batch.testNames.toSet == manifest.toSet)
      val results = new Results
      // Supplying one name and no distributor makes ScalaTest run synchronously.
      // Keep its real test bodies, per-test instances, timeouts and diagnostics.
      for name <- manifest do
        val status = batch.run(S(name), Args(results))
        status.waitUntilCompleted()
        require(status.succeeds() && results.failures.isEmpty, results.failures.iterator.asScala.mkString("\n"))
      require(results.succeeded.get() == manifest.size, "Every ctest case must execute successfully")
      context
    val timings = output / "samples.csv"
    if !os.exists(timings) then
      os.write(timings, "revision,fork,phase,sample,tests,wall_ms,process_cpu_ms,allocated_bytes,gc_count,gc_ms,jit_ms,heap_used_after_bytes\n")
    val heaps = output / "retained-heap.csv"
    if !os.exists(heaps) then
      os.write(heaps, "revision,fork,tests,held_after_gc_bytes,released_after_gc_bytes,session_retained_bytes\n")
    for iteration <- 0 until warmups + samples do
      val collectionsBefore = gcCount
      val gcBefore = gcMillis
      val jitBefore = compilation.getTotalCompilationTime
      val allocatedBefore = allocation.getTotalThreadAllocatedBytes
      val cpuBefore = process.getProcessCpuTime
      val started = System.nanoTime()
      val context = compileBatch()
      val wallMs = (System.nanoTime() - started) / 1000000.0
      val cpuMs = (process.getProcessCpuTime - cpuBefore) / 1000000.0
      val allocated = allocation.getTotalThreadAllocatedBytes - allocatedBefore
      val collections = gcCount - collectionsBefore
      val gcMs = gcMillis - gcBefore
      val jitMs = compilation.getTotalCompilationTime - jitBefore
      val usedHeap = memory.getHeapMemoryUsage.getUsed
      Reference.reachabilityFence(context)
      require(allocated > 0 && cpuMs > 0)
      val phase = if iteration < warmups then "warmup" else "measured"
      val sample = if iteration < warmups then iteration else iteration - warmups
      val row = s"$revision,$fork,$phase,$sample,${manifest.size},$wallMs,$cpuMs,$allocated,$collections,$gcMs,$jitMs,$usedHeap\n"
      os.write.append(timings, row)
      print(s"MEASURE $row")
    // Return no strong reference to the session, so it can be collected before
    // the second reading. Keep it live explicitly for the first GC and verify
    // that the second GC actually released it.
    def heldHeap(): (Long, WeakReference[CompilerCtx]) =
      val context = compileBatch()
      val reference = new WeakReference(context)
      val heap = collectedHeap()
      Reference.reachabilityFence(context)
      (heap, reference)
    val (held, reference) = heldHeap()
    val released = collectedHeap()
    require(reference.get() == null, "The completed session is still strongly reachable")
    val row = s"$revision,$fork,${manifest.size},$held,$released,${held - released}\n"
    os.write.append(heaps, row)
    print(s"HEAP $row")
