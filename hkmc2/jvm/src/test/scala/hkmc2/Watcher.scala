package hkmc2

import scala.collection.mutable
import mlscript.utils.*, shorthands.*

import better.files.*
import io.methvin.better.files.*
import io.methvin.watcher.{DirectoryWatcher, PathUtils}
import io.methvin.watcher.hashing.{FileHash, FileHasher}
import java.time.LocalDateTime
import java.time.temporal._

// Note: when SBT's `fork` is set to `false`, the path should be `File("hkmc2/")` instead...
object MainWatcher extends Watcher(File("../")):
  def main(args: Array[String]): Unit = run

class Watcher(dir: File):
  val dirPath = os.Path(dir.pathAsString)
  
  println((fansi.Color.Blue("Watching directory ") ++ fansi.Color.DarkGray(dir.toString)).toString)
  
  val fileHashes = mutable.Map.empty[File, FileHash]
  val completionTime = mutable.Map.empty[File, LocalDateTime]
  val fileHasher = FileHasher.DEFAULT_FILE_HASHER
  
  val watcher: DirectoryWatcher = DirectoryWatcher.builder()
    .logger(org.slf4j.helpers.NOPLogger.NOP_LOGGER)
    .path(dir.toJava.toPath)
    .fileHashing(false) // so that simple save events trigger processing eve if there's no file change
    .listener(new io.methvin.watcher.DirectoryChangeListener {
      def onEvent(event: io.methvin.watcher.DirectoryChangeEvent): Unit = try
        // println(event)
        val hash = PathUtils.hash(fileHasher, event.path)
        val file = File(event.path)
        val old = fileHashes.get(event.path)
        fileHashes(event.path) = hash
        old match
          case S(existingHash) =>
            if existingHash === hash then
              // if file.extension =/= S(".cmd") then return
              // else
              val newTime = LocalDateTime.now()
              completionTime.get(event.path) match
                case S(time) =>
                  val diff = time.until(newTime, ChronoUnit.SECONDS)
                  if diff <= 1 then
                    // println(s"Debounced $time -> $newTime = $diff s")
                    return
                case N =>
                  System.err.println("It seems the previous completion time was not recorded")
                  return
          case N =>
        import java.nio.file.StandardWatchEventKinds
        import java.nio.file.WatchEvent
        import java.nio.file.Path
        val et = event.eventType
        val count = event.count
        et match
          case io.methvin.watcher.DirectoryChangeEvent.EventType.OVERFLOW => ???
          case _ =>
            et.getWatchEventKind.asInstanceOf[WatchEvent.Kind[Path]] match
              case StandardWatchEventKinds.ENTRY_CREATE => onCreate(file, count)
              case StandardWatchEventKinds.ENTRY_MODIFY => onModify(file, count)
              case StandardWatchEventKinds.ENTRY_DELETE => onDelete(file, count)
        completionTime(event.path) = LocalDateTime.now()
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
      Thread.sleep(100)
      val path = os.Path(file.pathAsString)
      val basePath = path.segments.drop(dirPath.segmentCount).toList.init
      val relativeName = basePath.map(_ + "/").mkString + path.baseName
      val predefPath = os.pwd/os.up/"shared"/"src"/"test"/"mlscript"/"decls"/"Predef.mls"
      semantics.suid.reset // FIXME hack
      val isModuleFile = path.segments.contains("mlscript-compile")
      if isModuleFile
      then
        MLsCompiler(predefPath).compileModule(path)
      else
        val dm = new MainDiffMaker(path, predefPath, relativeName):
          override def unhandled(blockLineNum: Int, exc: Throwable): Unit =
            exc.printStackTrace()
            super.unhandled(blockLineNum, exc)
        dm.run()
      
      
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


