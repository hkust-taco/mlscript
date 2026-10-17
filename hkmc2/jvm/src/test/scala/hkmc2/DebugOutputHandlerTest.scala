package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import io.PlatformPath.given


class DebugOutputHandlerTest extends AnyFunSuite:
  // Diff tests cover the emitted traces. This measures total I/O, which a golden file cannot
  // distinguish from repeatedly rewriting the same growing log.
  test("file debug output writes a linear amount of data"):
    val dir = os.temp.dir(prefix = "debug-output-")
    val underlying = io.FileSystem.default
    var writtenChars = 0L
    val fs = new io.FileSystem:
      def read(path: io.Path): String = underlying.read(path)
      def exists(path: io.Path): Boolean = underlying.exists(path)
      def getLastChangedTimestamp(path: io.Path): Long = underlying.getLastChangedTimestamp(path)
      def write(path: io.Path, content: String): Unit =
        writtenChars += content.length
        underlying.write(path, content)
      def append(path: io.Path, content: String): Unit =
        writtenChars += content.length
        underlying.append(path, content)
    try
      os.write(dir / "trace.log", "old session contents")
      val output = DebugOutputHandler(fs, dir, _ => fail("Unexpected standard output"))
      val lines = (1 to 2000).map(i => s"debug line $i")
      lines.foreach(output.emit(Config.DebugOutput.File("trace.log"), _))
      val expected = lines.mkString("", "\n", "\n")
      assert(os.read(dir / "trace.log") == expected)
      assert(writtenChars == expected.length,
        "Only new output should be written, without copying accumulated contents")
    finally os.remove.all(dir)
