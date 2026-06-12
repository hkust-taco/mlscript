package hkmc2

import scala.util.Try
import scala.scalajs.js.annotation.*
import org.scalajs.dom
import org.scalajs.dom.document
import hkmc2.utils.shorthands._
import scala.util.matching.Regex
import scala.scalajs.js, js.JSConverters.*
import scala.collection.immutable
import scala.collection.mutable.Map as MutMap

import io.*
import scala.collection.mutable.{ArrayBuffer, Buffer}

@JSExportTopLevel("Compiler")
class Compiler(paths: MLsCompiler.Paths)(using cctx: CompilerCtx):
  private given Config = Config.default(io.Path("/"))
  
  private var pathDiagnosticsMap = MutMap.empty[Str, (Int, Buffer[Diagnostic])]
  
  private def mkRaise(path: io.Path): Raise = d =>
    pathDiagnosticsMap.getOrElseUpdate(path.toString, (pathDiagnosticsMap.size, Buffer.empty))._2 += d
  
  private val compiler = MLsCompiler(paths, mkRaise)
  
  private def collectDiagnostics(): js.Array[js.Dynamic] =
    pathDiagnosticsMap.toArray.sortBy(_._2._1).map:
      case (path, (_, diagnostics)) => js.Dynamic.literal(
        path = path,
        diagnostics = diagnostics.iterator.map: d =>
          js.Dynamic.literal(
            kind = d.kind.toString().toLowerCase(),
            source = d.source.toString().toLowerCase(),
            mainMessage = d.theMsg,
            allMessages = d.allMsgs.iterator.map:
              case (message, loc) =>
                lazy val ctx = ShowCtx.mk:
                  message.bits.collect:
                    case Message.Code(t) => t
                js.Dynamic.literal(
                  messageBits = message.bits.map:
                    case Message.Text(text) => js.Dynamic.literal(text = text)
                    case Message.Code(ty) => ty.showIn(0)(using ctx)
                  .toJSArray,
                  location = loc match
                    case S(loc) => js.Dynamic.literal(
                      start = loc.spanStart,
                      end = loc.spanEnd
                    )
                    case N => null
                )
            .toJSArray
          )
        .toJSArray)
    .toJSArray
  
  @JSExport
  def compile(filePath: Str): js.Array[js.Dynamic] =
    compiler.compileModule(Path(filePath))
    val perFileDiagnostics = collectDiagnostics()
    pathDiagnosticsMap = MutMap.empty
    perFileDiagnostics

@JSExportTopLevel("Paths")
final class Paths(prelude: Str, runtime: Str, term: Str) extends MLsCompiler.Paths:
  val preludeFile = Path(prelude)
  val runtimeFile = Path(runtime)
  val termFile = Path(term)
