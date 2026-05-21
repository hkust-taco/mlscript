package hkmc2.analysis

import hkmc2.*
import hkmc2.io
import hkmc2.semantics.*
import hkmc2.semantics.Elaborator.{Ctx, State}
import hkmc2.utils.*
import mlscript.utils.*, shorthands.*

class Analyzer(paths: MLsCompiler.Paths, mkRaise: io.Path => Raise)(using cctx: CompilerCtx, config: Config):
  import paths.*

  private var dbgParsing = false
  private var dbgElab = false

  def analyze(file: io.Path): AnalysisDocument =
    val wd = file.up

    given Raise = mkRaise(file)

    given Elaborator.State = new Elaborator.State:
      override def dbg: Bool = dbgElab

    given SymbolPrinter = new SymbolPrinter(
      Scope.empty(Scope.Cfg.default.copy(
        escapeChars = false,
        useSuperscripts = true,
        includeZero = true,
      ))
    )

    val etl = new TraceLogger:
      override def doTrace: Bool = false
    val rtl = new TraceLogger:
      override def doTrace: Bool = false

    val preludeParse = ParserSetup(preludeFile, dbgParsing)
    val mainParse = ParserSetup(file, dbgParsing)

    val elab = Elaborator(etl, wd, Ctx.empty)

    val initState = State.init.nestLocal("prelude")
    val (_, newCtx) = elab.importFrom(preludeParse.resultBlk)(using initState)

    newCtx.nestLocal("file:" + file.baseName).givenIn:
      given CompilerCtx = cctx.derive(file)
      val elab = Elaborator(etl, wd, newCtx)
      val parsed = mainParse.resultBlk
      val (blk0, _) = elab.importFrom(parsed)
      Config.extractConfigFromStats(blk0).givenIn:
        val resolver = Resolver(rtl)
        resolver.traverseBlock(blk0)(using Resolver.ICtx.empty)
        val builder = SymbolTreeBuilder(file, mainParse.origin, parsed, blk0)
        AnalysisDocument(
          "mlscript.symbol-tree",
          1,
          N,
          file.toString,
          S(builder.buildRoot()),
          Nil,
          builder.dependencies(),
        )

end Analyzer
