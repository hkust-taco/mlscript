package hkmc2

import scala.collection.mutable
import scala.jdk.CollectionConverters.*

import hkmc2.utils.*, shorthands.*

import better.files.*
import _root_.io.methvin
import methvin.better.files.*
import methvin.watcher.{DirectoryWatcher, PathUtils, DirectoryChangeEvent, DirectoryChangeListener}
import methvin.watcher.hashing.{FileHash, FileHasher}
import java.time.LocalDateTime
import java.time.temporal._
import io.FileSystem, io.PlatformPath.given

// Note: when SBT's `fork` is set to `false`, the path should be `File("hkmc2/")` instead...
// * Only the first path can contain tests. The other paths are only watched for source changes.
object MainWatcher extends Watcher(
    File("../hkmc2/shared/src") ::
    File("./src") ::
    // File("../hkmc2Benchmarks/src") ::
    Nil
):
  def main(args: Array[String]): Unit = run

class Watcher(dirs: Ls[File]):
  val dirPaths = dirs.map(d => os.Path(d.pathAsString))
  
  dirs.foreach: dir =>
    println((fansi.Color.Blue("Watching directory ") ++ fansi.Color.DarkGray(dir.toString)).toString)
  
  val fileHashes = mutable.Map.empty[File, FileHash]
  val completionTime = mutable.Map.empty[File, LocalDateTime]
  val fileHasher = FileHasher.DEFAULT_FILE_HASHER
  
  given cctx: CompilerCtx = CompilerCtx.fresh(FileSystem.default)
  
  val watcher: DirectoryWatcher = DirectoryWatcher.builder()
    .logger(org.slf4j.helpers.NOPLogger.NOP_LOGGER)
    .paths(dirs.map(_.toJava.toPath).asJava)
    .fileHashing(false) // so that simple save events trigger processing eve if there's no file change
    .listener(new DirectoryChangeListener {
      def onEvent(event: DirectoryChangeEvent): Unit = try
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
          case DirectoryChangeEvent.EventType.OVERFLOW => ???
          case _ =>
            et.getWatchEventKind.asInstanceOf[WatchEvent.Kind[Path]] match
              case StandardWatchEventKinds.ENTRY_CREATE => onCreate(file, count)
              case StandardWatchEventKinds.ENTRY_MODIFY => onModify(file, count)
              case StandardWatchEventKinds.ENTRY_DELETE => onDelete(file, count)
        completionTime(event.path) = LocalDateTime.now()
      catch ex =>
        // System.err.println("Unexpected error in watcher: " + ex)
        ex.printStackTrace()
        System.err.println("Unexpected error in watcher (" + ex.getClass() + ")")
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
      val basePath = path.segments.drop(dirPaths.head.segmentCount).toList.init
      val relativeName = basePath.map(_ + "/").mkString + path.baseName
      val rootPath = os.pwd/os.up
      val testBasePath = rootPath/"hkmc2"/"shared"/"src"/"test"
      val preludePath = testBasePath/"mlscript"/"decls"/"Prelude.mls"
      val predefPath = testBasePath/"mlscript-compile"/"Predef.mls"
      val isModuleFile = path.segments.contains("mlscript-compile")
      if isModuleFile
      then
        given Config = Config.default(testBasePath)
        MLsCompiler(
          paths = new MLsCompiler.Paths:
            val preludeFile = preludePath
            val runtimeFile = testBasePath/"mlscript-compile"/"Runtime.mjs"
            val runtimeSourceFile = testBasePath/"mlscript-compile"/"Runtime.mls"
            val termFile = testBasePath/"mlscript-compile"/"Term.mjs",
          mkRaise = ReportFormatter(System.out.println, colorize = true).mkRaise
        ).compileModule(path)
      else
        val dm = new MainDiffMaker(rootPath.toString, path, preludePath, predefPath, relativeName):
          def cctx = Watcher.this.cctx
          override def unhandled(blockLineNum: Int, exc: Throwable): Unit =
            exc.printStackTrace()
            super.unhandled(blockLineNum, exc)
        dm.run()
      
  
  def show(file: File) =
    fansi.Color.Yellow:
      file.toString.stripPrefix(dirs.head.toString)
  
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


