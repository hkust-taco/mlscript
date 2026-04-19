package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.semantics.*
import hkmc2.syntax.Keyword.`override`
import semantics.Elaborator.{Ctx, State}


class ParserSetup(file: io.Path, dbgParsing: Bool)(using state: Elaborator.State, raise: Raise, cctx: CompilerCtx):
  
  val block = cctx.fs.read(file)
  val fph = new FastParseHelpers(block)
  val origin = Origin(file, 0, fph)
  
  val lexer = new syntax.Lexer(origin, dbg = dbgParsing)
  val tokens = lexer.bracketedTokens
  
  // if showParse.isSet || dbgParsing.isSet then
  //   output(syntax.Lexer.printTokens(tokens))
  
  val rules = syntax.ParseRules()
  val parser = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing):
    def doPrintDbg(msg: => Str): Unit =
      // if dbg then output(msg)
      if dbg then println(msg)
  
  val result = parser.parseAll(parser.block(allowNewlines = true))
  
  val resultBlk = new syntax.Tree.Block(result)

object MLsCompiler:
  /** The class contains the necessary paths to files for the MLscript compiler. */
  trait Paths:
    def preludeFile: io.Path
    def runtimeFile: io.Path
    def termFile: io.Path

/**
  * The compiler that compiles MLscript code into JavaScript modules.
  *
  * @param paths required paths needed by the compiler
  * @param mkRaise generates a separate `Raise` function for each file.
  * @param config the compiler's configuration object
  * @param fs the file system interface
  */
class MLsCompiler
    (paths: MLsCompiler.Paths, mkRaise: io.Path => Raise)
    (using cctx: CompilerCtx, config: Config):
  import paths.*
  
  
  
  // TODO adapt logic
  given DebugPrinter = new DebugPrinter
  val etl = new TraceLogger{override def doTrace: Bool = false}
  val ltl = new TraceLogger{override def doTrace: Bool = false}
  // val ltl = new TraceLogger{override def doTrace: Bool = true}
  val rtl = new TraceLogger{override def doTrace: Bool = false}
  
  
  var dbgParsing = false
  var dbgElab = false

  private def emitJs(
      file: io.Path,
      wd: io.Path,
      program: codegen.Program,
      exportedSymbol: Opt[BlockMemberSymbol],
  )(using Raise, Elaborator.State, Elaborator.Ctx): Unit =
    val jsb = ltl.givenIn:
      codegen.js.JSBuilder()
    val baseScp: utils.Scope =
      utils.Scope.empty(utils.Scope.Cfg.default)
    // * This line serves for `import.meta.url`, which retrieves directory and file names of mjs files.
    // * Having `module id"import" with ...` in `prelude.mls` will generate `globalThis.import` that is undefined.
    baseScp.addToBindings(Elaborator.State.importSymbol, "import", shadow = false)
    val nestedScp = baseScp.nest
    val je = nestedScp.givenIn:
      jsb.program(program, exportedSymbol, wd)
    cctx.fs.write(file.up / io.RelPath(s"${file.baseName}.mjs"), je.stripBreaks.mkString(100))

  private def wasmGlue(wat: Str, compiled: codegen.wasm.text.CompiledWasmModule): Str =
    s"""|import binaryen from "binaryen"
        |
        |const __mlx_wat = ${wat.escaped}
        |
        |function binaryenCompileToModule(wat, importObject) {
        |  const mod = binaryen.parseText(wat)
        |  mod.setFeatures(binaryen.Features.All)
        |  if (!mod.validate()) throw new Error("Generated WAT is invalid")
        |  const modBuf = mod.emitBinary()
        |  mod.dispose()
        |  return WebAssembly.instantiate(modBuf, importObject)
        |}
        |
        |function __mlx_importObject() {
        |  return {
        |    system: {
        |      memory: new WebAssembly.Memory({ initial: ${compiled.systemMemMinPages} })
        |    }
        |  }
        |}
        |
        |const __mlx_wasmPromise = binaryenCompileToModule(__mlx_wat, __mlx_importObject())
        |
        |export const __mlx_wasm = () => __mlx_wasmPromise
        |
        |export default __mlx_wasm().then(({ instance }) => instance.exports[${compiled.entryName.escaped}]())
        |""".stripMargin

  private def emitWasm(
      file: io.Path,
      wd: io.Path,
      program: codegen.Program,
      exportedSymbol: Opt[BlockMemberSymbol],
  )(using Raise, Elaborator.State): Unit =
    val baseScp: utils.Scope =
      utils.Scope.empty(utils.Scope.Cfg.default)
    val nestedScp = baseScp.nest
    val watb = ltl.givenIn:
      new codegen.wasm.text.WatBuilder()
    val compiled = nestedScp.givenIn:
      watb.program(program, exportedSymbol, wd, Nil, Set.empty)
    val watStr = compiled.wat.mkString(100)
    cctx.fs.write(file.up / io.RelPath(s"${file.baseName}.wat"), watStr)
    cctx.fs.write(file.up / io.RelPath(s"${file.baseName}.mjs"), wasmGlue(watStr, compiled))
  
  
  def compileModule(file: io.Path): Unit =
    
    val wd = file.up
    
    given Raise = mkRaise(file)
    
    given Elaborator.State = new Elaborator.State:
      override def dbg: Bool = dbgElab
    
    val preludeParse = ParserSetup(preludeFile, dbgParsing)
    val mainParse = ParserSetup(file, dbgParsing)
    
    val elab = Elaborator(etl, wd, Ctx.empty)
    
    val initState = State.init.nestLocal("prelude")
    
    val (pblk, newCtx) = elab.importFrom(preludeParse.resultBlk)(using initState)
    
    newCtx.nestLocal("file:"+file.baseName).givenIn:
      given CompilerCtx = cctx.derive(file)
      val elab = Elaborator(etl, wd, newCtx)
      val parsed = mainParse.resultBlk
      val (blk0, _) = elab.importFrom(parsed)
      val resolver = Resolver(rtl)
      resolver.traverseBlock(blk0)(using Resolver.ICtx.empty)
      def findQuote(t: semantics.Statement): Bool = t match
        case Term.Quoted(_) | Term.Unquoted(_) => true
        case Term.Ref(sym) => sym === State.termSymbol
        case _ => t.subTerms.exists(findQuote)
      val hasQuote = findQuote(blk0)
      val effectiveCfg = blk0.stats.collect:
        case sc: SetConfig => sc.modify
      .foldLeft(config): (cfg, modify) =>
        modify(cfg)
      val blk =
        effectiveCfg.target match
          case CompilationTarget.JS =>
            new Term.Blk(
              Import(State.runtimeSymbol, runtimeFile.toString, runtimeFile) ::
                // Only import `Term.mls` when necessary.
                (if hasQuote then
                  Import(State.termSymbol, termFile.toString, termFile) :: blk0.stats
                else
                  blk0.stats),
              blk0.res
            )
          case CompilationTarget.Wasm =>
            blk0
      effectiveCfg.givenIn:
        val low = ltl.givenIn:
          new codegen.Lowering()
            with codegen.LoweringSelSanityChecks
        val le_0 = low.program(blk)
        val nme = file.baseName
        val exportedSymbol = parsed.definedSymbols.find(_._1 === nme).map(_._2)
        val le_1 = ltl.givenIn:
          codegen.BlockSimplifier(exportedSymbol.toSet)(le_0)
        val le_2 = ltl.givenIn:
          codegen.DeadParamElim(le_1)
        effectiveCfg.target match
          case CompilationTarget.JS =>
            emitJs(file, wd, le_2, exportedSymbol)
          case CompilationTarget.Wasm =>
            emitWasm(file, wd, le_2, exportedSymbol)
  
  
end MLsCompiler
