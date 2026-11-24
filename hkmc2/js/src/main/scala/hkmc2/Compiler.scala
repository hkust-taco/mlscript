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
class Compiler(using cctx: CompilerCtx):
  
  private var pathDiagnosticsMap = MutMap.empty[Str, (Int, Buffer[Diagnostic])]
  
  private def mkRaise(path: io.Path): Raise = d =>
    pathDiagnosticsMap.getOrElseUpdate(path.toString, (pathDiagnosticsMap.size, Buffer.empty))._2 += d
  
  private val compiler = MLsCompiler(mkRaise)
  
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
  def compile(filePath: Str): CompilationResult =
    val written = compiler.compileModule(Path(filePath))
    val perFileDiagnostics = collectDiagnostics()
    pathDiagnosticsMap = MutMap.empty
    new CompilationResult:
      val compiled = written
      val diagnostics = perFileDiagnostics

/** The result of [[Compiler.compile]], a plain JavaScript object. */
trait CompilationResult extends js.Object:
  /** Whether the requested module's code was emitted (see `MLsCompiler.compileModule`); a diagnostic loader does not count.
    * A request that reuses a cached WASM artifact with errors reports no diagnostics, so only this distinguishes it
    * from a successful compilation. */
  val compiled: Bool
  /** The diagnostics reported by this request, grouped by file, in the order in which the files first reported one. */
  val diagnostics: js.Array[js.Dynamic]

@JSExportTopLevel("Paths")
final class Paths(prelude: Str, runtime: Str, runtimeSource: Str, term: Str) extends MLsCompiler.Paths:
  val preludeFile = Path(prelude)
  val runtimeFile = Path(runtime)
  val runtimeSourceFile = Path(runtimeSource)
  val termFile = Path(term)
