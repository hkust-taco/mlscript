package hkmc2

import java.util.concurrent.{ConcurrentLinkedQueue, CountDownLatch, Executors, ThreadFactory, TimeUnit, TimeoutException}
import java.util.concurrent.atomic.AtomicInteger
import collection.concurrent.TrieMap
import scala.concurrent.{Await, ExecutionContext, ExecutionContextExecutorService, Future}
import scala.concurrent.duration.*
import scala.jdk.CollectionConverters.*

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAll

import hkmc2.CompilerCache.{ActiveDependencyGraph, ArtifactCache}


class CompilerCacheTest extends AnyFunSuite with BeforeAndAfterAll:
  // Global executor threads inherit the test class loader and keep its compiled-module caches
  // reachable after SBT finishes this run. Terminating this suite's workers releases that loader.
  private given executionContext: ExecutionContextExecutorService =
    ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(2))

  override protected def afterAll(): Unit =
    try
      executionContext.shutdownNow()
      assert(executionContext.awaitTermination(completionTimeout.toMillis, TimeUnit.MILLISECONDS),
        "Compiler cache test workers should terminate when their suite finishes")
    finally super.afterAll()

  // Allow more time for both worker startup and completion on shared CI runners.
  private val (startupTimeout, completionTimeout) =
    if TimeOutTests.OnCI then (15.seconds, 15.seconds)
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
      def append(path: io.Path, content: String): Unit = underlyingFs.append(path, content)
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

      def compile(file: io.Path): Future[Boolean] = Future({
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
        def append(path: io.Path, content: String): Unit = io.FileSystem.default.append(path, content)
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

  test("JavaScript and WASM compilation preserve the shared runtime IR"):
    // Cross-backend cache isolation is not observable through source-language diff tests.
    import io.PlatformPath.given
    val tempDir = os.temp.dir(prefix = "wasm-runtime-isolation-")
    try
      val jsFile: io.Path = tempDir/"JavaScriptUnit.mls"
      val wasmFile: io.Path = tempDir/"WasmUnit.mls"
      os.write(tempDir/"JavaScriptUnit.mls", "#lang(0.3.x)\nfun JavaScriptUnit() = ()")
      os.write(tempDir/"WasmUnit.mls", "#lang(0.3.x)\n#config(target: Wasm)\nfun WasmUnit() = ()")
      given CompilerCtx = TestFolders.compilerCtx(os.pwd)
      given DebugPrinter = new DebugPrinter(None)
      given utils.TraceLogger = utils.TraceLogger.silent
      given Raise = diagnostic => fail(diagnostic.toString)
      val cctx = summon[CompilerCtx]
      val prelude = cctx.getPrelude(cctx.paths.preludeFile).ctx
      val runtime = cctx.getElaboratedBlock(cctx.paths.runtimeSourceFile, prelude)
      val unit = runtime.state.unitSymbol
      val originalUnit = unit.irClsLikeDefn.get
      val originalHeader = unit.irClassHeader.get
      val compiler = MLsCompiler(_ => summon[Raise])
      assert(compiler.compileModule(jsFile))
      val jsArtifact = cctx.getElaboratedBlock(jsFile, prelude)
      val originalJs = os.read(tempDir/"JavaScriptUnit.mjs")

      val bothStarted = new CountDownLatch(2)
      val requests = List(jsFile, wasmFile).map: file =>
        Future:
          bothStarted.countDown()
          assert(bothStarted.await(startupTimeout.toMillis, TimeUnit.MILLISECONDS))
          assert(compiler.compileModule(file))
      Await.result(Future.sequence(requests), completionTimeout)

      assert(unit.irClsLikeDefn.exists(_ eq originalUnit),
        "Generating Wasm support must preserve the cached JavaScript runtime's Unit definition")
      assert(unit.irClassHeader.exists(_ eq originalHeader),
        "Generating Wasm support must preserve the cached JavaScript runtime's Unit class header")
      assert(cctx.getElaboratedBlock(cctx.paths.runtimeSourceFile, prelude) eq runtime)
      assert(cctx.getElaboratedBlock(jsFile, prelude) eq jsArtifact)
      assert(compiler.compileModule(jsFile))
      assert(os.read(tempDir/"JavaScriptUnit.mjs") == originalJs,
        "Reusing the JavaScript artifact after Wasm compilation must produce the same output")
    finally os.remove.all(tempDir)

  test("WASM units with errors are not emitted, and their importers say why on every request"):
    import io.PlatformPath.given
    val tempDir = os.temp.dir(prefix = "compiler-cached-errors-")
    try
      // These requests exercise cache/error state, not source-language diagnostic wording
      // (which is covered by the WasmFailedImports and ModuleErrors diff tests).
      os.write(tempDir/"Broken.mls", "#lang(0.3.x)\n#config(target: Wasm)\nfun Broken() = missing")
      os.write(tempDir/"Importer.mls", "#lang(0.3.x)\n#config(target: Wasm)\nimport \"./Broken.mls\"\nfun Importer() = Broken()")
      os.write(tempDir/"Dynamic.mls", "#lang(0.3.x)\n#config(target: Wasm)\nmodule M with\n  val value = 42\nfun Dynamic() = M")
      given CompilerCtx = TestFolders.compilerCtx(os.pwd)
      val diagnostics = collection.mutable.ArrayBuffer.empty[Diagnostic]
      val compiler = MLsCompiler(_ => diagnostic => { diagnostics += diagnostic; () })
      def reportsErrors(name: String): Boolean =
        diagnostics.clear()
        compiler.compileModule(tempDir/s"$name.mls")
        diagnostics.exists(_.isInstanceOf[ErrorReport])
      assert(reportsErrors("Broken"), "Building an artifact must report its errors")
      // Every request after the first reuses the frontend artifacts. `Importer` has no errors itself, but its import
      // cannot be compiled, and the backend failure of `Dynamic` is not memoized.
      for _ <- 0 until 2 do
        assert(reportsErrors("Importer"), "A module must report an import that cannot be compiled on every request")
        assert(reportsErrors("Dynamic"), "A backend failure must be reported on every request")
      assert(!compiler.compileModule(tempDir/"Broken.mls"), "Reusing an artifact with errors must not compile it")
      for name <- List("Broken", "Importer", "Dynamic") do
        assert(os.exists(tempDir/s"$name.mjs") && !os.exists(tempDir/s"$name.wat"),
          s"The failed WASM unit $name must have a diagnostic loader and no WAT")
    finally os.remove.all(tempDir)
