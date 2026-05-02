package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.Message.MessageContext
import hkmc2.semantics.*
import hkmc2.syntax.Keyword.`override`
import semantics.Elaborator.{Ctx, State}

import codegen.wasm.text.{
  CompiledWasmModule, SessionFunc, SessionGlobal, SessionSingleton, WatBuilder,
}


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
  * The compiler that compiles MLscript code into JavaScript or WebAssembly modules.
  *
  * @param paths required paths needed by the compiler
  * @param mkRaise generates a separate `Raise` function for each file.
  * @param config the compiler's configuration object
  * @param cctx the compilation context (including the file system interface)
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

  /** Symbols a module wants preserved through optimization passes and surfaced to
    * downstream importers: the exported module itself, its members, and their type symbols. */
  private def preservedSymbolsFor(exportedSymbol: Opt[BlockMemberSymbol]): Set[codegen.Local] =
    val members = exportedSymbol.iterator.flatMap: sym =>
      sym.modOrObjTree.iterator.flatMap(_.definedSymbols.valuesIterator)
    .toSet
    (exportedSymbol.iterator ++ members.iterator ++ members.iterator.flatMap(_.tsym.toSeq))
      .map(sym => sym: codegen.Local).toSet

  /** JS-specific emit: build module source and write the `.mjs` file. */
  private def emitJs(
      file: io.Path,
      wd: io.Path,
      program: codegen.Program,
      exportedSymbol: Opt[BlockMemberSymbol],
  )(using Raise, State, Ctx, Config): Unit =
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

  /** Resolves a Wasm module's `.mjs` import path back to its `.mls` source, if present on disk. */
  private def resolveImportSource(importPath: Str, moduleDir: io.Path): Opt[io.Path] =
    val importedPath =
      if importPath.startsWith("/")
      then io.Path(importPath)
      else moduleDir / io.RelPath(importPath)
    if importedPath.ext === "mjs" then
      val resolved = importedPath.up / io.RelPath(s"${importedPath.baseName}.mls")
      resolved.optionIf(cctx.fs.exists(resolved))
    else N

  /** JavaScript glue that loads the module's `.wat`, links its Wasm dependencies,
    * and re-exports the program result. */
  private def wasmGlue(
      wd: io.Path,
      moduleBaseName: Str,
      compiled: CompiledWasmModule,
      exportedSymbol: Opt[BlockMemberSymbol],
      dependencies: Seq[(Str, Str)],
  ): Str =
    def relativeImportPath(path: Str): Str =
      if path.startsWith("/")
      then "./" + io.Path(path).relativeTo(wd).map(_.toString).getOrElse(path)
      else path
    val dependencyImports = dependencies.zipWithIndex.map:
      case ((importPath, _), idx) =>
        s"""import { __mlx_wasm as __mlx_dep_$idx } from "${relativeImportPath(importPath)}";"""
    val dependencyImportStmts =
      if dependencyImports.isEmpty then ""
      else dependencyImports.mkString("", "\n", "\n\n")
    val dependencyBindings = dependencies.zipWithIndex.map:
      case ((_, moduleName), idx) =>
        s"""  importObject[${moduleName.escaped}] = (await __mlx_dep_$idx()).instance.exports"""
    val dependencyBindingStmts =
      if dependencyBindings.isEmpty then ""
      else dependencyBindings.mkString("", "\n", "\n")
    val exportedValueExpr = exportedSymbol.flatMap: sym =>
      compiled.sessionExports.collectFirst:
        case f: SessionFunc if f.sym === sym =>
          if sym.modOrObjTree.nonEmpty then s"""instance.exports[${f.exportName.escaped}]()"""
          else s"""instance.exports[${f.exportName.escaped}]"""
        case g: SessionGlobal if g.sym === sym => s"""instance.exports[${g.exportName.escaped}].value"""
        case s: SessionSingleton if s.blockSym === sym => s"""instance.exports[${s.exportName.escaped}].value"""
    .getOrElse(s"""instance.exports[${compiled.entryName.escaped}]()""")
    s"""|import { __mlx_compileWatFromUrl, __mlx_buildSystem } from "./RuntimeWASM.mjs"
        |$dependencyImportStmts
        |
        |const __mlx_wat_url = new URL("./${moduleBaseName}.wat", import.meta.url)
        |
        |async function __mlx_importObject() {
        |  const importObject = {
        |    system: await __mlx_buildSystem(${compiled.systemMemMinPages})
        |  }
        |$dependencyBindingStmts
        |  return importObject
        |}
        |
        |const __mlx_wasmPromise = __mlx_importObject()
        |  .then(importObject => __mlx_compileWatFromUrl(__mlx_wat_url, importObject))
        |
        |export const __mlx_wasm = () => __mlx_wasmPromise
        |
        |const { instance } = await __mlx_wasm()
        |
        |export default $exportedValueExpr
        |""".stripMargin

  /** Source of the shared `RuntimeWASM.mjs` helper module. */
  private val wasmRuntimeMjsSource: Str =
    """|import binaryen from "binaryen"
       |
       |async function __mlx_loadWatText(url) {
       |  if (url.protocol === "file:") {
       |    const { readFile } = await import("node:fs/promises")
       |    return readFile(url, "utf8")
       |  }
       |  const response = await fetch(url)
       |  if (!response.ok) throw new Error(`Failed to load WAT from ${url}`)
       |  return response.text()
       |}
       |
       |export async function __mlx_compileWatFromUrl(url, importObject) {
       |  const wat = await __mlx_loadWatText(url)
       |  const mod = binaryen.parseText(wat)
       |  mod.setFeatures(binaryen.Features.All)
       |  if (!mod.validate()) throw new Error(`Generated WAT is invalid: ${url}`)
       |  const modBuf = mod.emitBinary()
       |  mod.dispose()
       |  return WebAssembly.instantiate(modBuf, importObject)
       |}
       |
       |const __mlx_intrinsicsPromise =
       |  __mlx_compileWatFromUrl(new URL("./RuntimeWASM.wat", import.meta.url), {})
       |
       |export async function __mlx_buildSystem(systemMemMinPages) {
       |  const mem = new WebAssembly.Memory({ initial: systemMemMinPages })
       |  const decodeUtf16 = new TextDecoder("utf-16le")
       |  const intrinsicModule = await __mlx_intrinsicsPromise
       |  return {
       |    mem,
       |    mlx_str_from_utf16: (ptr, byteLen) =>
       |      decodeUtf16.decode(new Uint8Array(mem.buffer, ptr, byteLen)),
       |    ...intrinsicModule.instance.exports
       |  }
       |}
       |""".stripMargin

  /** Ensures the shared Wasm runtime helpers (`RuntimeWASM.{wat,mjs}`) are present
    * in the given output directory. */
  private def ensureWasmRuntimeArtifacts(moduleDir: io.Path)(using Raise, State): Unit =
    val watFile = moduleDir / io.RelPath("RuntimeWASM.wat")
    val mjsFile = moduleDir / io.RelPath("RuntimeWASM.mjs")
    if !cctx.fs.exists(watFile) then
      val baseScp = utils.Scope.empty(utils.Scope.Cfg.default)
      val watb = ltl.givenIn:
        new WatBuilder()
      val wat = baseScp.nest.givenIn:
        watb.intrinsicSupportModule().mkString(100)
      cctx.fs.write(watFile, wat)
    if !cctx.fs.exists(mjsFile) then
      cctx.fs.write(mjsFile, wasmRuntimeMjsSource)

  /** Compiles an imported Wasm module, or scans cached full elaboration for its session exports. */
  private def compileWasmDep(
      file: io.Path,
      prelude: Ctx,
      memo: mutable.Map[io.Path, Opt[CompiledWasmModule]],
  )(using State, CompilerCtx): Opt[CompiledWasmModule] =
    memo.get(file) match
      case S(cached) => cached
      case N =>
        given Raise = mkRaise(file)
        val cachedArtifact = CompilerCtx.get.getCachedElaboratedBlock(file, full = true)
        val artifact = cachedArtifact.getOrElse:
          etl.givenIn:
            CompilerCtx.get.getElaboratedBlock(file, prelude, true)
        val blk = artifact.term
        val effectiveCfg = Config.extractConfigFromStats(blk)
        val compiled =
          if effectiveCfg.target =/= CompilationTarget.Wasm then
            raise(ErrorReport(
              msg"Wasm modules can only import Wasm-targeted `.mls` files; " +
                msg"`${file.toString}` targets `${effectiveCfg.target.toString}`" -> N :: Nil,
              source = Diagnostic.Source.Compilation))
            N
          else
            prelude.givenIn:
              val exportedSymbol = artifact.tree.definedSymbols.find(_._1 === file.baseName).map(_._2)
              val preservedSymbols = preservedSymbolsFor(exportedSymbol)
              effectiveCfg.givenIn:
                val low = ltl.givenIn:
                  new codegen.Lowering() with codegen.LoweringSelSanityChecks
                val le0 = low.program(blk)
                val le1 = ltl.givenIn:
                  codegen.BlockSimplifier(preservedSymbols)(le0)
                val program = ltl.givenIn:
                  codegen.DeadParamElim(le1)
                val symbolsToExport = preservedSymbols ++ program.main.definedVars
                cachedArtifact match
                  case S(_) =>
                    val watb = ltl.givenIn:
                      new WatBuilder()
                    val exportScope = utils.Scope.empty(utils.Scope.Cfg.default).nest
                    val sessionExports = exportScope.givenIn:
                      watb.extractExports(
                        program.main,
                        Seq.empty,
                        symbolsToExport,
                        file.baseName,
                      )
                    S(CompiledWasmModule(hkmc2.document.Document.empty, "entry", 0, sessionExports))
                  case N =>
                    emitWasm(file, program, exportedSymbol, preservedSymbols, prelude, memo)
        memo(file) = compiled
        compiled

  /** Wasm-specific emit: compile any `.mls` dependencies, run `WatBuilder`, write
    * `.wat`, `.mjs` glue, and ensure shared `RuntimeWASM.{wat,mjs}` helpers exist. */
  private def emitWasm(
      file: io.Path,
      program: codegen.Program,
      exportedSymbol: Opt[BlockMemberSymbol],
      preservedSymbols: Set[codegen.Local],
      prelude: Ctx,
      memo: mutable.Map[io.Path, Opt[CompiledWasmModule]],
  )(using Raise, State, CompilerCtx): Opt[CompiledWasmModule] =
    val moduleDir = file.up
    val moduleBaseName = file.baseName
    val edges = mutable.ArrayBuffer.empty[(Str, Str)]
    val compiledDeps = mutable.ArrayBuffer.empty[CompiledWasmModule]
    var failed = false
    program.imports.foreach:
      case (sym, importPath) =>
        resolveImportSource(importPath, moduleDir) match
          case S(sourceFile) =>
            compileWasmDep(sourceFile, prelude, memo) match
              case S(dep) =>
                edges += (importPath -> sourceFile.baseName)
                compiledDeps += dep
              case N => failed = true
          case N =>
            raise(ErrorReport(
              msg"Wasm modules currently only support imports of Wasm-targeted `.mls` files; " +
                msg"`${importPath}` cannot be resolved that way" -> sym.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
            failed = true
    if failed then N
    else
      val sessionImports =
        val seen = mutable.LinkedHashSet.empty[Str]
        compiledDeps.iterator.flatMap(_.sessionExports).filter(b => seen.add(b.bindingKey)).toSeq
      val baseScp = utils.Scope.empty(utils.Scope.Cfg.default)
      val watb = ltl.givenIn:
        new WatBuilder()
      val symbolsToExport = preservedSymbols ++ program.main.definedVars
      val compiled = baseScp.nest.givenIn:
        watb.program(
          program,
          exportedSymbol,
          moduleDir,
          sessionImports,
          symbolsToExport,
          moduleBaseName,
        )
      ensureWasmRuntimeArtifacts(moduleDir)
      cctx.fs.write(moduleDir / io.RelPath(s"$moduleBaseName.wat"), compiled.wat.mkString(100))
      cctx.fs.write(
        moduleDir / io.RelPath(s"$moduleBaseName.mjs"),
        wasmGlue(moduleDir, moduleBaseName, compiled, exportedSymbol, edges.toSeq),
      )
      S(compiled)

  def compileModule(file: io.Path): Unit =
    
    val wd = file.up
    
    given Raise = mkRaise(file)
    
    given Elaborator.State = new Elaborator.State:
      override def dbg: Bool = dbgElab
    
    val preludeParse = ParserSetup(preludeFile, dbgParsing)
    val mainParse = ParserSetup(file, dbgParsing)
    
    val elab = Elaborator(etl, wd, Ctx.empty)
    
    val initState = State.init.nestLocal("prelude")
    
    val (_, newCtx) = elab.importFrom(preludeParse.resultBlk)(using initState)
    
    newCtx.nestLocal("file:"+file.baseName).givenIn:
      given CompilerCtx = cctx.derive(file)
      val elab = Elaborator(etl, wd, newCtx)
      val parsed = mainParse.resultBlk
      val (blk0, _) = elab.importFrom(parsed)
      val effectiveCfg = Config.extractConfigFromStats(blk0)
      effectiveCfg.givenIn:
        val resolver = Resolver(rtl)
        resolver.traverseBlock(blk0)(using Resolver.ICtx.empty)
        def findQuote(t: semantics.Statement): Bool = t match
          case Term.Quoted(_) | Term.Unquoted(_) => true
          case Term.Ref(sym) => sym === State.termSymbol
          case _ => t.subTerms.exists(findQuote)
        val hasQuote = findQuote(blk0)
        val exportedSymbol = parsed.definedSymbols.find(_._1 === file.baseName).map(_._2)
        val preservedSymbols = preservedSymbolsFor(exportedSymbol)
        val blk = effectiveCfg.target match
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
        val low = ltl.givenIn:
          new codegen.Lowering()
            with codegen.LoweringSelSanityChecks
        val le_0 = low.program(blk)
        val le_1 = ltl.givenIn:
          codegen.BlockSimplifier(preservedSymbols)(le_0)
        val le_2 = ltl.givenIn:
          codegen.DeadParamElim(le_1)
        effectiveCfg.target match
          case CompilationTarget.JS =>
            emitJs(file, wd, le_2, exportedSymbol)
          case CompilationTarget.Wasm =>
            emitWasm(file, le_2, exportedSymbol, preservedSymbols, newCtx, mutable.Map.empty)

            
end MLsCompiler

