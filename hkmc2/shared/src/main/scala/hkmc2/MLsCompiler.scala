package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.Message.MessageContext
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

  /** Module metadata collected during elaboration. */
  private case class ModuleInfo(
      file: io.Path,
      block: Term.Blk,
      exportedSymbol: Opt[BlockMemberSymbol],
      effectiveCfg: Config,
      hasQuote: Bool,
  )

  /** A Wasm module imported as a dependency. */
  private case class WasmDependency(
      importPath: Str,
      compiled: codegen.wasm.text.CompiledWasmModule,
  )

  /** Result of compiling a module to Wasm with its dependencies. */
  private case class WasmCompilation(
      compiled: codegen.wasm.text.CompiledWasmModule,
      dependencies: Seq[WasmDependency],
  )

  // TODO adapt logic
  given DebugPrinter = new DebugPrinter
  val etl = new TraceLogger{override def doTrace: Bool = false}
  val ltl = new TraceLogger{override def doTrace: Bool = false}
  // val ltl = new TraceLogger{override def doTrace: Bool = true}
  val rtl = new TraceLogger{override def doTrace: Bool = false}

  var dbgParsing = false
  var dbgElab = false

  /** Collects metadata about an elaborated module. */
  private def moduleInfo(
      file: io.Path,
      parsed: syntax.Tree.Block,
      block: Term.Blk,
  )(using Raise, Elaborator.State, Elaborator.Ctx): ModuleInfo =
    def findQuote(t: semantics.Statement): Bool = t match
      case Term.Quoted(_) | Term.Unquoted(_) => true
      case Term.Ref(sym) => sym === Elaborator.State.termSymbol
      case _ => t.subTerms.exists(findQuote)

    val resolver = Resolver(rtl)
    resolver.traverseBlock(block)(using Resolver.ICtx.empty)
    ModuleInfo(
      file = file,
      block = block,
      exportedSymbol = parsed.definedSymbols.find(_._1 === file.baseName).map(_._2),
      effectiveCfg = block.stats.collect:
        case sc: SetConfig => sc.modify
      .foldLeft(config): (cfg, modify) =>
        modify(cfg),
      hasQuote = findQuote(block),
    )

  /** Elaborates and collects metadata for an imported module. */
  private def elaborateImportedModule(
      file: io.Path,
      prelude: Elaborator.Ctx,
  )(using Elaborator.State, CompilerCtx): ModuleInfo =
    val parentCctx = summon[CompilerCtx]
    given Raise = mkRaise(file)
    val parsed = etl.givenIn:
      parentCctx.getElaboratedBlock(file, prelude).tree
    prelude.nestLocal("file:" + file.baseName).givenIn:
      given CompilerCtx = parentCctx.derive(file)
      val elab = Elaborator(etl, file.up, prelude)
      val (blk, _) = elab.importFrom(parsed)
      moduleInfo(file, parsed, blk)

  /** Lowers a module to intermediate representation with optimization passes. */
  private def lowerModule(module: ModuleInfo)(using Raise, Elaborator.State, Elaborator.Ctx): codegen.Program =
    val blk =
      module.effectiveCfg.target match
        case CompilationTarget.JS =>
          new Term.Blk(
            Import(State.runtimeSymbol, runtimeFile.toString, runtimeFile) ::
              // Only import `Term.mls` when necessary.
              (if module.hasQuote then
                Import(State.termSymbol, termFile.toString, termFile) :: module.block.stats
              else
                module.block.stats),
            module.block.res
          )
        case CompilationTarget.Wasm =>
          module.block
    module.effectiveCfg.givenIn:
      val low = ltl.givenIn:
        new codegen.Lowering()
          with codegen.LoweringSelSanityChecks
      val lowered = low.program(blk)
      val simplified = ltl.givenIn:
        codegen.BlockSimplifier(module.exportedSymbol.toSet)(lowered)
      ltl.givenIn:
        codegen.DeadParamElim(simplified)

  /** Resolves an import path to the source `.mls` file if possible. */
  private def resolveImportSource(importPath: Str, moduleDir: io.Path): Opt[io.Path] =
    val importedPath =
      if importPath.startsWith("/")
      then io.Path(importPath)
      else moduleDir / io.RelPath(importPath)
    if importedPath.ext === "mjs" then
      val resolved = importedPath.up / io.RelPath(s"${importedPath.baseName}.mls")
      resolved.optionIf(cctx.fs.exists(resolved))
    else N

  /** Compiles a module to JavaScript and writes the `.mjs` file. */
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

  /** Generates JavaScript glue code for instantiating and importing a Wasm module. */
  private def wasmGlue(
      wd: io.Path,
      wat: Str,
      intrinsicSupportWat: Str,
      compiled: codegen.wasm.text.CompiledWasmModule,
      exportedSymbol: Opt[BlockMemberSymbol],
      dependencies: Seq[WasmDependency],
  ): Str =
    def relativeImportPath(path: Str): Str =
      if path.startsWith("/")
      then "./" + io.Path(path).relativeTo(wd).map(_.toString).getOrElse(path)
      else path

    val dependencyImports = dependencies.zipWithIndex.map:
      case (dependency, idx) =>
        s"""import { __mlx_wasm as __mlx_dep_$idx } from "${relativeImportPath(dependency.importPath)}";"""
    val dependencyImportStmts =
      if dependencyImports.isEmpty then ""
      else dependencyImports.mkString("", "\n", "\n\n")
    val dependencyBindings = dependencies.zipWithIndex.map:
      case (dependency, idx) =>
        s"""  importObject[${dependency.importPath.escaped}] = (await __mlx_dep_$idx()).instance.exports"""
    val dependencyBindingStmts =
      if dependencyBindings.isEmpty then ""
      else dependencyBindings.mkString("", "\n", "\n")
    val exportedValueExpr =
      exportedSymbol.flatMap: sym =>
        compiled.sessionExports.collectFirst:
          case func: codegen.wasm.text.SessionFunc if func.sym === sym =>
            s"""instance.exports[${func.exportName.escaped}]"""
          case global: codegen.wasm.text.SessionGlobal if global.sym === sym =>
            s"""instance.exports[${global.exportName.escaped}].value"""
          case singleton: codegen.wasm.text.SessionSingleton if singleton.blockSym === sym =>
            s"""instance.exports[${singleton.exportName.escaped}].value"""
      .getOrElse(s"""instance.exports[${compiled.entryName.escaped}]()""")
    s"""|import binaryen from "binaryen"
        |$dependencyImportStmts
        |
        |const __mlx_wat = ${wat.escaped}
        |const __mlx_intrinsics_wat = ${intrinsicSupportWat.escaped}
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
        |async function __mlx_buildSystem() {
        |  const mem = new WebAssembly.Memory({ initial: ${compiled.systemMemMinPages} })
        |  const decodeUtf16 = new TextDecoder("utf-16le")
        |  const intrinsicModule = await binaryenCompileToModule(__mlx_intrinsics_wat, {})
        |  return {
        |    mem,
        |    mlx_str_from_utf16: (ptr, byteLen) =>
        |      decodeUtf16.decode(new Uint8Array(mem.buffer, ptr, byteLen)),
        |    ...intrinsicModule.instance.exports
        |  }
        |}
        |
        |async function __mlx_importObject() {
        |  const importObject = {
        |    system: await __mlx_buildSystem()
        |  }
        |$dependencyBindingStmts
        |  return importObject
        |}
        |
        |const __mlx_wasmPromise = __mlx_importObject()
        |  .then(importObject => binaryenCompileToModule(__mlx_wat, importObject))
        |
        |export const __mlx_wasm = () => __mlx_wasmPromise
        |
        |export default __mlx_wasm().then(({ instance }) => $exportedValueExpr)
        |""".stripMargin

  /** Generates WAT for the intrinsics support module. */
  private def wasmIntrinsicSupportWat()(using Raise, Elaborator.State): Str =
    val baseScp: utils.Scope =
      utils.Scope.empty(utils.Scope.Cfg.default)
    val watb = ltl.givenIn:
      new codegen.wasm.text.WatBuilder()
    baseScp.nest.givenIn:
      watb.intrinsicSupportModule().mkString(100)

  /** Compiles a module to Wasm and writes `.wat` and `.mjs` files. */
  private def emitWasm(
      module: ModuleInfo,
      prelude: Elaborator.Ctx,
      memo: mutable.Map[io.Path, WasmCompilation],
  )(using Raise, Elaborator.State, CompilerCtx): codegen.wasm.text.CompiledWasmModule =
    val moduleDir = module.file.up
    val moduleBaseName = module.file.baseName
    val moduleMjsFile = moduleDir / io.RelPath(s"$moduleBaseName.mjs")
    val compilation = memo.getOrElseUpdate(
      module.file,
      locally:
        given Raise = mkRaise(module.file)
        prelude.givenIn:
          val program = lowerModule(module)
          val dependencies = mutable.ArrayBuffer.empty[WasmDependency]
          program.imports.foreach:
            case (sym, importPath) =>
              resolveImportSource(importPath, moduleDir) match
                case S(sourceFile) =>
                  val importedModule = elaborateImportedModule(sourceFile, prelude)
                  if importedModule.effectiveCfg.target =/= CompilationTarget.Wasm then
                    val importedTarget = importedModule.effectiveCfg.target.toString
                    raise(
                      ErrorReport(
                        msg"Wasm modules can only import Wasm-targeted `.mls` files; " +
                          msg"`${sourceFile.toString}` targets `$importedTarget`" ->
                          sym.toLoc :: Nil,
                        source = Diagnostic.Source.Compilation,
                      ),
                    )
                    throw new IllegalStateException(s"Expected Wasm-targeted imported module at ${sourceFile.toString}")
                  dependencies += WasmDependency(
                    importPath,
                    emitWasm(importedModule, prelude, memo),
                  )
                case N =>
                  raise(
                    ErrorReport(
                      msg"Wasm modules currently only support imports of Wasm-targeted `.mls` files; " +
                        msg"`${importPath}` cannot be resolved that way" ->
                        sym.toLoc :: Nil,
                      source = Diagnostic.Source.Compilation,
                    ),
                  )

          val baseScp: utils.Scope =
            utils.Scope.empty(utils.Scope.Cfg.default)
          val nestedScp = baseScp.nest
          val watb = ltl.givenIn:
            new codegen.wasm.text.WatBuilder()
          val sessionImports: Seq[codegen.wasm.text.SessionBinding] =
            val seen = mutable.LinkedHashSet.empty[Str]
            dependencies.iterator
              .flatMap(_.compiled.sessionExports)
              .filter: binding =>
                seen.add(binding.bindingKey)
              .toSeq
          WasmCompilation(
            compiled = nestedScp.givenIn:
              watb.program(
                program,
                module.exportedSymbol,
                moduleDir,
                sessionImports,
                module.exportedSymbol.toSet,
                moduleMjsFile.toString,
              ),
            dependencies = dependencies.toSeq,
          )
    )

    val watStr = compilation.compiled.wat.mkString(100)
    cctx.fs.write(moduleDir / io.RelPath(s"$moduleBaseName.wat"), watStr)
    cctx.fs.write(
      moduleMjsFile,
      wasmGlue(
        moduleDir,
        watStr,
        wasmIntrinsicSupportWat(),
        compilation.compiled,
        module.exportedSymbol,
        compilation.dependencies,
      ),
    )

    compilation.compiled

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
      val module = moduleInfo(file, parsed, blk0)
      module.effectiveCfg.target match
        case CompilationTarget.JS =>
          given Raise = mkRaise(file)
          emitJs(file, wd, lowerModule(module), module.exportedSymbol)
        case CompilationTarget.Wasm =>
          emitWasm(module, newCtx, mutable.Map.empty)

end MLsCompiler
