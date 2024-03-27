package hkmc2

import scala.collection.mutable
import mlscript.utils.*, shorthands.*

import better.files.*
import io.methvin.better.files.*
import io.methvin.watcher.DirectoryWatcher

// Note: when SBT's `fork` is set to `false`, the path should be `File("hkmc2/shared/")` instead...
object MainWatcher extends Watcher(File("../shared/")):
  def main(args: Array[String]): Unit = run

class Watcher(dir: File):
  
  println((fansi.Color.Blue("Watching directory ") ++ fansi.Color.DarkGray(dir.toString)).toString)
  
  val watcher: DirectoryWatcher = DirectoryWatcher.builder()
    .logger(org.slf4j.helpers.NOPLogger.NOP_LOGGER)
    .path(dir.toJava.toPath)
    .fileHasher(null) // so that simple save events trigger processing eve if there's no file change
    .listener(new io.methvin.watcher.DirectoryChangeListener {
      def onEvent(event: io.methvin.watcher.DirectoryChangeEvent): Unit = try
        // println(event)
        import java.nio.file.StandardWatchEventKinds
        import java.nio.file.WatchEvent
        import java.nio.file.Path
        val et = event.eventType
        val file = File(event.path)
        val count = event.count
        et match
          case io.methvin.watcher.DirectoryChangeEvent.EventType.OVERFLOW => ???
          case _ =>
            et.getWatchEventKind.asInstanceOf[WatchEvent.Kind[Path]] match
              case StandardWatchEventKinds.ENTRY_CREATE => onCreate(file, count)
              case StandardWatchEventKinds.ENTRY_MODIFY => onModify(file, count)
              case StandardWatchEventKinds.ENTRY_DELETE => onDelete(file, count)
      catch ex =>
        System.err.println("Unexpected error in watcher: " + ex)
        ex.printStackTrace()
        watcher.close()
        throw ex
    })
    .build();
    
  def run: Unit =
    try watcher.watch()
    finally watcher.close()
  
  def go(file: File) =
    // println(s"go $file")
    val isMls = file.toString.endsWith(".mls")
    if file.toString.endsWith(".scala") then
      watcher.close()
    else if isMls || file.toString.endsWith(".cmd") then
      val dm = new DiffMaker:
        def doFail(msg: String): Unit =
          System.err.println(fansi.Color.Red("FAILURE: ").toString + msg)
        override def unhandled(fileName: Str, blockLineNum: Int, exc: Throwable): Unit =
          exc.printStackTrace()
          super.unhandled(fileName, blockLineNum, exc)
      // update(file) // TODO
      // ()
      Thread.sleep(100)
      dm(os.Path(file.pathAsString))
  
  def show(file: File) =
    fansi.Color.Yellow:
      file.toString.stripPrefix(dir.toString)
  
  def pre = fansi.Color.Blue(">> ").toString
  
  def onCreate(file: File, count: Int) =
    println(pre + show(file).toString + fansi.Color.Blue(" created"))
    go(file)
  
  def onModify(file: File, count: Int) =
    println(pre + show(file).toString + fansi.Color.Blue(s" modified $count times"))
    go(file)
  
  def onDelete(file: File, count: Int) =
    println(pre + show(file).toString + fansi.Color.Blue(" deleted"))
    // go(file)


