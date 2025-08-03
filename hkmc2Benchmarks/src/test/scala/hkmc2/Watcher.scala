package hkmc2

import better.files.*

object MainWatcher extends Watcher(File("./hkmc2Benchmarks/src/test") :: File("../hkmc2/shared/src") :: File("./src") :: Nil):
  def main(args: Array[String]): Unit = run
