package hkmc2

import java.util.concurrent.{ConcurrentLinkedQueue, CountDownLatch, Executors, ThreadFactory, TimeUnit, TimeoutException}
import java.util.concurrent.atomic.AtomicInteger
import collection.concurrent.TrieMap
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.*
import scala.jdk.CollectionConverters.*

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.CompilerCache.{ActiveDependencyGraph, ArtifactCache}


class CompilerCacheTest extends AnyFunSuite:
  private given ExecutionContext = ExecutionContext.global

  // Allow more time for both worker startup and completion on shared CI runners.
  private val (startupTimeout, completionTimeout) =
    if sys.env.contains("CI") then (15.seconds, 15.seconds)
    else (5.seconds, 10.seconds)

  private final class Entry

  private def newCache(): ArtifactCache[Entry] =
    new ArtifactCache[Entry](TrieMap.empty, TrieMap.empty)

  test("artifact cache evaluates independent paths concurrently"):
    val cache = newCache()
    val bothStarted = new CountDownLatch(2)
    val release = new CountDownLatch(1)

    def request(path: io.Path): Future[Entry] = Future:
      cache.getOrCreate(path)(_ => true,
        {
          bothStarted.countDown()
          release.await()
          new Entry
        })

    val requests = List(request(io.Path("/A.mls")), request(io.Path("/B.mls")))
    val overlapped =
      try bothStarted.await(startupTimeout.toMillis, TimeUnit.MILLISECONDS)
      finally release.countDown()
    Await.result(Future.sequence(requests), completionTimeout)

    assert(overlapped, "Building one path should not hold the cache monitor while it evaluates")

  test("artifact cache publishes one identity for concurrent requests to the same path"):
    val cache = newCache()
    val buildStarted = new CountDownLatch(1)
    val release = new CountDownLatch(1)
    val buildCount = new AtomicInteger
    val path = io.Path("/A.mls")

    def request(): Future[Entry] = Future:
      cache.getOrCreate(path)(_ => true,
        {
          buildCount.incrementAndGet()
          buildStarted.countDown()
          release.await()
          new Entry
        })

    val first = request()
    assert(buildStarted.await(startupTimeout.toMillis, TimeUnit.MILLISECONDS), "The first artifact build should start")
    val second = request()
    release.countDown()
    val firstResult = Await.result(first, completionTimeout)
    val secondResult = Await.result(second, completionTimeout)

    assert(buildCount.get() == 1, "Concurrent requesters should share one build for a path")
    assert(firstResult eq secondResult, "Concurrent requesters should observe one artifact identity")

  test("active dependency graph detects cycles of more than two artifacts"):
    val graph = new ActiveDependencyGraph
    val fileA = io.Path("/A.mls")
    val fileB = io.Path("/B.mls")
    val fileC = io.Path("/C.mls")

    graph.withDependency(fileA, fileB)(cycle => fail(s"Unexpected cycle: $cycle")):
      graph.withDependency(fileB, fileC)(cycle => fail(s"Unexpected cycle: $cycle")):
        graph.withDependency(fileC, fileA)(cycle => assert(cycle == List(fileC, fileA, fileB, fileC))):
          fail("The dependency closing the cycle should not be requested")

  test("active dependency graph permits shared acyclic dependencies"):
    val graph = new ActiveDependencyGraph
    val fileA = io.Path("/A.mls")
    val fileB = io.Path("/B.mls")
    val fileC = io.Path("/C.mls")

    graph.withDependency(fileA, fileC)(cycle => fail(s"Unexpected cycle: $cycle")):
      graph.withDependency(fileB, fileC)(cycle => fail(s"Unexpected cycle: $cycle")):
        succeed

  test("active dependency graph releases dependencies after failures"):
    val graph = new ActiveDependencyGraph
    val fileA = io.Path("/A.mls")
    val fileB = io.Path("/B.mls")

    intercept[IllegalStateException]:
      graph.withDependency(fileA, fileB)(cycle => fail(s"Unexpected cycle: $cycle")):
        throw new IllegalStateException("failed request")
    graph.withDependency(fileB, fileA)(cycle => fail(s"Stale dependency caused a cycle: $cycle")):
      succeed

  test("concurrent circular imports do not deadlock artifact path locks"):
    import io.PlatformPath.given

    val tempDir = os.temp.dir(prefix = "compiler-cache-deadlock-")
    val fileA: io.Path = tempDir / "A.mls"
    val fileB: io.Path = tempDir / "B.mls"
    os.write(tempDir / "A.mls",
      """|import "./B.mls"
         |
         |module A with...
         |fun value() = B.value()
         |""".stripMargin)
    os.write(tempDir / "B.mls",
      """|import "./A.mls"
         |
         |module B with...
         |fun value() = A.value()
         |""".stripMargin)

    // ParserSetup reads a source only after getOrCreate has acquired that source's path lock.
    // Holding both reads at this barrier therefore ensures the two root builds own A and B's
    // locks respectively before either can process its import and request the opposite lock.
    val bothRootsLocked = new CountDownLatch(2)
    val synchronizedRoots = Set(fileA, fileB)
    val underlyingFs = io.FileSystem.default
    val synchronizedFs = new io.FileSystem:
      def read(path: io.Path): String =
        if synchronizedRoots.contains(path) then
          bothRootsLocked.countDown()
          assert(bothRootsLocked.await(startupTimeout.toMillis, TimeUnit.MILLISECONDS),
            "Both root compilations should reach source parsing while holding their path locks")
        underlyingFs.read(path)

      def write(path: io.Path, content: String): Unit = underlyingFs.write(path, content)
      def exists(path: io.Path): Boolean = underlyingFs.exists(path)
      def getLastChangedTimestamp(path: io.Path): Long =
        underlyingFs.getLastChangedTimestamp(path)

    val workerThreads = new ConcurrentLinkedQueue[Thread]
    val threadFactory: ThreadFactory = runnable =>
      val thread = new Thread(runnable, "compiler-cache-deadlock-reproducer")
      thread.setDaemon(true)
      workerThreads.add(thread)
      thread
    val executor = Executors.newFixedThreadPool(2, threadFactory)
    val executionContext = ExecutionContext.fromExecutorService(executor)
    val diagnostics = new ConcurrentLinkedQueue[Diagnostic]

    try
      val paths = TestFolders.compilerPaths(os.pwd)
      given CompilerCtx = CompilerCtx.fresh(
        synchronizedFs,
        paths,
        Config.default(TestFolders.mainTestDir(os.pwd)),
      )

      def compile(file: io.Path): Future[Unit] = Future({
        val compiler = MLsCompiler(mkRaise = _ => diagnostic =>
          diagnostics.add(diagnostic)
          ())
        compiler.compileModule(file)
      })(using executionContext)

      try Await.result(Future.sequence(List(compile(fileA), compile(fileB))), completionTimeout)
      catch case timeout: TimeoutException =>
        val workerStacks = workerThreads.asScala.map: thread =>
          s"${thread.getName}: ${thread.getState}\n${thread.getStackTrace.mkString("\n")}"
        fail(s"Concurrent circular imports did not finish:\n${workerStacks.mkString("\n\n")}", timeout)
      assert(diagnostics.asScala.exists(_.theMsg.contains("Circular imports")),
        "A circular import diagnostic should be reported")
    finally
      executionContext.shutdownNow()
      os.remove.all(tempDir)


  test("WASM roots share cached dependencies and restore deleted outputs"):
    import io.PlatformPath.given
    val tempDir = os.temp.dir(prefix = "wasm-cache-")
    val fixtures = TestFolders.compileTestDir(os.pwd)/"wasm"/"modules"/"diamond"
    val executor = Executors.newFixedThreadPool(2)
    val executionContext = ExecutionContext.fromExecutorService(executor)
    try
      os.list(fixtures).filter(_.ext == "mls").foreach: source =>
        os.copy(source, tempDir/source.last)
      val left: io.Path = tempDir/"Left.mls"
      val right: io.Path = tempDir/"Right.mls"
      val counterWat: io.Path = tempDir/"Counter.wat"
      val reads = TrieMap.empty[io.Path, AtomicInteger]
      val writes = TrieMap.empty[io.Path, AtomicInteger]
      val bothRootsLocked = new CountDownLatch(2)
      val fs = new io.FileSystem:
        def read(path: io.Path): String =
          reads.getOrElseUpdate(path, new AtomicInteger).incrementAndGet()
          if path == left || path == right then
            bothRootsLocked.countDown()
            assert(bothRootsLocked.await(startupTimeout.toMillis, TimeUnit.MILLISECONDS))
          io.FileSystem.default.read(path)
        def write(path: io.Path, content: String): Unit =
          writes.getOrElseUpdate(path, new AtomicInteger).incrementAndGet()
          io.FileSystem.default.write(path, content)
        def exists(path: io.Path): Boolean = io.FileSystem.default.exists(path)
        def getLastChangedTimestamp(path: io.Path): Long = io.FileSystem.default.getLastChangedTimestamp(path)
      given CompilerCtx = CompilerCtx.fresh(fs, TestFolders.compilerPaths(os.pwd), Config.default(TestFolders.mainTestDir(os.pwd)))
      val compiler = MLsCompiler(_ => diagnostic => fail(diagnostic.toString))
      val requests = List(left, right).map: root =>
        Future(compiler.compileModule(root))(using executionContext)
      Await.result(Future.sequence(requests), 30.seconds)
      assert(writes(counterWat).get() == 1, "Concurrent roots should materialize their shared dependency once")
      val oldCounter = os.read(tempDir/"Counter.wat")
      val oldLeft = os.read(tempDir/"Left.mjs")
      os.remove(tempDir/"Counter.wat")
      os.remove(tempDir/"Left.mjs")
      compiler.compileModule(left)
      assert(reads.filter(_._1.ext == "mls").values.forall(_.get() == 1),
        "Regenerating backend outputs must reuse frontend artifacts")
      assert(os.read(tempDir/"Counter.wat") == oldCounter)
      assert(os.read(tempDir/"Left.mjs") == oldLeft)
    finally
      executionContext.shutdownNow()
      os.remove.all(tempDir)

  test("cached frontend and backend failures do not become successful compilations"):
    import io.PlatformPath.given
    val tempDir = os.temp.dir(prefix = "compiler-cached-errors-")
    try
      // These requests exercise cache/error state, not source-language diagnostic wording
      // (which is covered by the normal ModuleErrors diff test).
      os.write(tempDir/"Nested.mls", "fun Nested() =\n  #config(target: Wasm)\n  42")
      os.write(tempDir/"Dynamic.mls", "#config(target: Wasm)\nmodule M with\n  val value = 42\nfun Dynamic() = M")
      val wasmSource = TestFolders.compileTestDir(os.pwd)/"wasm"/"modules"/"Answer.mls"
      val quoted = codegen.js.JSBuilder.makeStringLiteral(wasmSource.toString)
      os.write(tempDir/"Mixed.mls", s"import $quoted\nfun Mixed() = Answer()")
      given CompilerCtx = TestFolders.compilerCtx(os.pwd)
      val diagnostics = collection.mutable.ArrayBuffer.empty[Diagnostic]
      val compiler = MLsCompiler(_ => diagnostic => { diagnostics += diagnostic; () })
      for _ <- 0 until 2; name <- List("Nested", "Dynamic", "Mixed") do
        diagnostics.clear()
        compiler.compileModule(tempDir/s"$name.mls")
        assert(diagnostics.exists(_.isInstanceOf[ErrorReport]), s"Errors for $name must be reported on every request")
        assert(!os.exists(tempDir/s"$name.mjs"))
    finally os.remove.all(tempDir)
