package hkmc2

import io.*, mlscript.utils.*, shorthands.*
import scala.scalajs.js, js.annotation.*, js.JSConverters.*
import scala.collection.mutable.Buffer

@JSExportTopLevel("std")
object std:
  @JSExport
  val prelude = generated.MLscript.preludeFile
  
  @JSExport
  val files =
    val buffer = Buffer.empty[js.Tuple2[String, String]]
    generated.MLscript.sourceFiles.foreach:
      case (fileName, (mlsSourceOpt, mjsSourceOpt)) =>
        mlsSourceOpt match
          case Some(mlsSource) =>
            buffer += js.Tuple2(fileName, mlsSource)
          case None => ()
        mjsSourceOpt match
          case Some(mjsSource) =>
            buffer += js.Tuple2(fileName.dropRight(3) + "mjs", mjsSource)
          case None => ()
    buffer.toJSArray
  
  @JSExport
  def defaultFileSystem: InMemoryFileSystem =
    new InMemoryFileSystem(files.map(t => (t._1, t._2)).toMap + ("/Prelude.mls" -> prelude))
  
  @JSExport
  def defaultPaths: Paths =
    new Paths("/Prelude.mls", "/Runtime.mjs", "/Term.mjs")