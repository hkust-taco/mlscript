package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import org.scalatest.time.{Seconds, Span}

import hkmc2.utils.*, shorthands.*


abstract class TimeOutTests
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
  with TimeLimitedTests
:
  
  // * Note: ScalaTest creates one instance of the class per test that runs in parallel.
  // * So this state is not actually shared, and is not a concurrency issue.
  var testName: Str = "‹unknown›"
  override def withFixture(test: NoArgTest) =
    testName = test.name
    super.withFixture(test)
  override val defaultTestSignaler: Signaler = new Signaler:
    @annotation.nowarn("msg=method stop in class Thread is deprecated") def apply(testThread: Thread): Unit =
      println(s"[${Thread.currentThread().getName}] running ${testThread.getName} has run out of time!")
      println(s"!! Test $testName at $testThread has run out out time !! stopping..." +
        "\n\tNote: you can increase this limit by changing TimeOutTests.TimeLimit")
      // * Thread.stop() is considered bad practice because normally it's better to implement proper logic
      // * to terminate threads gracefully, avoiding leaving applications in a bad state.
      // * But here we DGAF since all the test is doing is running a type checker and some Node REPL,
      // * which would be a much bigger pain to make receptive to "gentle" interruption.
      // * It would feel extremely wrong to intersperse the pure type checker algorithms
      // * with ugly `Thread.isInterrupted` checks everywhere...
      try testThread.stop()
      catch _ =>
        // * Thread.stop() is no longer supported in recent JVMs,
        // * and unfortunately there is no good alternative other than terminating the entire process.
        // * (Perhaps using Futures might be a viable alternative in the *future*, though.)
        System.exit(-1)

end TimeOutTests

object TimeOutTests:
  /** The default wall-clock limit of each test. CI runners are several times slower than
    * development machines, and their speed varies between runs by tens of percent,
    * so tests get a longer limit there. GitHub Actions sets `CI`.
    */
  val TimeLimit: Span =
    if sys.env.get("CI").isDefined then Span(60, Seconds)
    else Span(25, Seconds)

