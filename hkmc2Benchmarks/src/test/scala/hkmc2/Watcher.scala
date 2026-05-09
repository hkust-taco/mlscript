package hkmc2

import better.files.*

object MainWatcher extends Watcher(File("../hkmc2/shared/src") :: File("./src") :: File("../hkmc2DiffTests/src") :: Nil):
  def main(args: Array[String]): Unit = run
