package hkmc2
package codegen
package wasm

import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import semantics.*, Elaborator.State
import CompilerCache.Artifact
import text.*
import js.JSBuilder.makeStringLiteral
import scala.collection.mutable

final case class WasmRuntime(path: io.Path, watPath: io.Path, compiled: CompiledWasmFile)
final case class WasmGraph(runtime: WasmRuntime, files: Vector[(Artifact, io.Path, CompiledWasmFile)])

object WasmCompiler:
  /** Native ES-module operations and raw foreign-call results are the host boundary.
    * Boxing prevents MLscript's ordinary foreign-call conversion from replacing undefined with Unit. */
  val nativeBridge: Str =
    "{ importModule: url => import(url), apply: (fn, receiver, args) => ({ value: Reflect.apply(fn, receiver, args) }) }"

  /** The error of a module that cannot be compiled because the module of the source import at `loc`, from `file`,
    * could not be compiled. */
  def failedImport(file: io.Path, loc: Opt[Loc]): ErrorReport =
    ErrorReport(
      msg"Cannot compile this module: the imported file `${file.last}` could not be compiled due to an error" -> loc :: Nil,
      source = Diagnostic.Source.Compilation)

  /** Runs `build` with a `Raise` that forwards the diagnostics to `report`. The result is `None` if `build` reported
    * an error, since the module it returns is then incomplete. */
  private def unlessFailed[A](report: Raise)(build: Raise => A): Opt[A] =
    var failed = false
    val tracking: Raise = diagnostic =>
      if !(diagnostic.kind is Diagnostic.Kind.Warning) then failed = true
      report(diagnostic)
    val result = build(tracking)
    Option.unless(failed)(result)

/** Materializes a graph of cached frontend artifacts. Backend memoization and output writing
  * are separate: a valid memoized artifact must still restore missing output files. */
final class WasmCompiler(using cctx: CompilerCtx, tl: TraceLogger):
  private val runtimeLoaderPath = cctx.paths.runtimeSourceFile.up / "RuntimeWasm.mjs"

  private def output(source: io.Path, extension: Str): io.Path = source.up / (source.baseName + extension)

  private def emitFailureLoader(file: io.Path, artifact: Artifact): Unit =
    val out = output(file, ".mjs")
    // The host runtime comes from RuntimeWasm.mls and must never become a failed Wasm source's loader.
    if out =/= runtimeLoaderPath then
      val message = makeStringLiteral(s"Cannot run ${file.last} because its compilation failed.")
      // Declare the normal exports so static imports reach this error during evaluation.
      val loader = s"""throw new Error($message);
export const wasmExports = undefined;
export default undefined;
"""
      artifact.materialize((out -> loader) :: Nil)

  private def specifier(path: io.Path, from: io.Path): Str =
    val relative = path.relativeTo(from).getOrElse:
      lastWords(s"Cannot form a relative WASM module URL from $from to $path")
    // URL escaping is separate from JavaScript string escaping. In particular, # and % in
    // actual filenames must not turn into a fragment or an already-encoded URL component.
    val encoded = relative.toString.replace('\\', '/').getBytes("UTF-8").iterator.map: byte =>
      val n = byte & 255
      if n >= 65 && n <= 90 || n >= 97 && n <= 122 || n >= 48 && n <= 57 || "-._~/".contains(n.toChar)
      then n.toChar.toString else f"%%$n%02X"
    .mkString
    if encoded.startsWith(".") then encoded else "./" + encoded

  /** The runtime module, which every Wasm module imports, or `None` if its source has errors or building it reports one.
    *
    * The runtime module defines the `Unit` object of the runtime unit (`Runtime.mls`), identified by that object's
    * symbol: the elaboration state of every artifact takes it from the runtime unit's artifact (see
    * `State.unitSymbol`). So the runtime module is built with the elaboration state of that artifact and memoized on it.
    * Rebuilding the runtime unit's artifact, when the runtime unit, a file it imports, or the Prelude changes, creates
    * a new `Unit` symbol, and every artifact depends on the runtime unit, so all of them are rebuilt with a new runtime
    * module. Otherwise, the runtime module is built once: the modules that are linked together refer to the bindings
    * of the runtime by the symbols of its interface, so they must all be compiled against the same runtime module.
    */
  def runtime()(using Raise): Opt[WasmRuntime] =
    val source = cctx.paths.runtimeSourceFile
    val prelude = cctx.getPrelude(cctx.paths.preludeFile).ctx
    val artifact = cctx.getElaboratedBlock(source, prelude)
    if artifact.hasErrors then return N
    val wat = source.up / "RuntimeWasm.wat"
    artifact.compiledWasm:
      WasmCompiler.unlessFailed(summon[Raise]): raise =>
        WatBuilder.runtimeModule(using artifact.ctx, tl, artifact.state, raise)
    .map: compiled =>
      artifact.materialize((wat -> compiled.module.wat.mkString(100)) :: Nil)
      WasmRuntime(runtimeLoaderPath, wat, compiled)

  /** Compiles the Wasm modules of `artifact` and of the artifacts it imports, transitively, and writes their outputs.
    * Each module reports its diagnostics to `report` applied to its source path.
    *
    * The result is `None` if the module of `artifact` could not be compiled. A module is not compiled if its artifact
    * has errors, which the request that built the artifact reported, if compiling it reports an error, or if the
    * module of one of its imports could not be compiled, which it reports at that import.
    * Failed modules replace their loaders with diagnostic loaders that throw on import, retaining any existing WAT.
    */
  def compile(file: io.Path, artifact: Artifact, report: io.Path => Raise): Opt[WasmGraph] =
    val runtimeResult = runtime()(using report(cctx.paths.runtimeSourceFile))
    if runtimeResult.isEmpty then emitFailureLoader(file, artifact)
    runtimeResult.flatMap: support =>
      val done = mutable.LinkedHashMap.empty[Artifact, (io.Path, CompiledWasmFile)]
      val failed = mutable.Set.empty[Artifact]

      def build(path: io.Path, art: Artifact): Opt[CompiledWasmFile] =
        val out = output(path, ".mjs")
        if out == support.path then
          report(path)(ErrorReport(
            msg"The output path '${support.path.toString}' is reserved for WASM runtime support" -> N :: Nil,
            source = Diagnostic.Source.Compilation))
          return N
        val dependencies = mutable.LinkedHashMap.empty[Artifact, (io.Path, CompiledWasmFile)]
        def include(a: Artifact): Unit = a.sourceImports.foreach: dep =>
          if !dependencies.contains(dep.artifact) then
            include(dep.artifact)
            dependencies(dep.artifact) = done(dep.artifact)
        include(art)
        val imported = dependencies.values.toVector
        val bindings = FileImport("system", support.compiled.interface) +:
          imported.zipWithIndex.map { case ((_, compiled), i) => FileImport(s"module$i", compiled.interface) }
        art.compiledWasm:
          WasmCompiler.unlessFailed(report(path)): raise =>
            given Raise = raise
            given State = art.state
            given Elaborator.Ctx = art.ctx
            val sourceSymbols = art.sourceImports.iterator.map(_.sym).toSet
            WatBuilder.fresh(FileCompilation(bindings, sourceSymbols)).fileModule(
              art.ir.copy(imports = art.ir.imports.filterNot(_._1 == State.runtimeSymbol)), art.compilationUnit.defaultExport, path.up)
        .map: compiled =>
          val watPath = output(path, ".wat")
          val dependencyPaths = imported.iterator.map { case (source, _) =>
            makeStringLiteral(specifier(output(source, ".mjs"), path.up))
          }.mkString("[", ", ", "]")
          val metadata = s"""{ runtime: { path: ${makeStringLiteral(specifier(support.watPath, path.up))}, entry: ${makeStringLiteral(support.compiled.module.entryName)} },
  wat: ${makeStringLiteral(specifier(watPath, path.up))}, entry: ${makeStringLiteral(compiled.module.entryName)}, pages: ${compiled.module.systemMemMinPages},
  dependencies: $dependencyPaths, export: ${facade(compiled.interface)} }"""
          // RuntimeWasm owns loading, initialization, and host wrappers. Only ESM syntax
          // and the ABI data extracted from this compilation unit are emitted here.
          val loader = s"""import RuntimeWasm from ${makeStringLiteral(specifier(support.path, path.up))};
const loaded = await RuntimeWasm.loadModule(import.meta.url, $metadata, ${WasmCompiler.nativeBridge});
export const wasmExports = loaded.wasmExports;
export default loaded.defaultExport;
"""
          art.materialize(Ls(watPath -> compiled.module.wat.mkString(100), out -> loader))
          compiled
      end build

      def emit(path: io.Path, art: Artifact): Opt[CompiledWasmFile] =
        done.get(art) match
          case S((_, compiled)) => S(compiled)
          case N if failed(art) => N
          case N =>
            val result =
              if art.hasErrors then N
              else
                // Compile every import, even after one fails, so that each one reports why it cannot be compiled.
                val failedImports = art.sourceImports.filter(dep => emit(dep.path, dep.artifact).isEmpty)
                failedImports.foreach(dep => report(path)(WasmCompiler.failedImport(dep.path, dep.loc)))
                if failedImports.isEmpty then build(path, art) else N
            result match
              case S(compiled) => done(art) = path -> compiled
              case N =>
                emitFailureLoader(path, art)
                failed += art
            result

      emit(file, artifact).map: _ =>
        WasmGraph(support, done.iterator.map { case (art, (path, compiled)) => (art, path, compiled) }.toVector)

  private def facade(abi: FileInterface): Str =
    def constructor(sym: ValueSymbol): Opt[AbiFunction] =
      sym.asCls.flatMap(cls => abi.functions.find(_.sym == cls))
    def function(sym: ValueSymbol): Opt[AbiFunction] =
      abi.functions.find(_.sym == sym).orElse(constructor(sym))
    def callable(f: AbiFunction, ctor: Opt[AbiFunction]): Str =
      val optional = f.optionalParams.toVector.sorted.mkString("[", ", ", "]")
      s"""{ kind: "function", name: ${makeStringLiteral(f.name)}, optionalParams: $optional, constructor: ${ctor.fold("null")(callable(_, N))} }"""
    def global(name: Str): Str = s"""{ kind: "global", name: ${makeStringLiteral(name)} }"""
    def value(sym: ValueSymbol): Str =
      // The default export is a binding; exported classes are identified by their definitions.
      val singleton = abi.classes.find(_.sym.bms.contains(sym)).flatMap(_.singleton).flatMap { case (idx, _) =>
        abi.globals.find(_.index == idx).map(g => global(g.name))
      }
      singleton.getOrElse:
        function(sym) match
          case S(f) => callable(f, constructor(sym).filter(_.sym != f.sym))
          case N =>
            abi.globals.find(_.sym == sym).map(g => global(g.name))
              .getOrElse(lastWords(s"Missing WASM default export binding for $sym"))
    abi.defaultExport.fold("""{ kind: "undefined" }"""): sym =>
      abi.namespaces.find(_.sym == sym) match
        case S(ns) =>
          ns.members.toVector.sortBy(_._1).iterator.map: (name, member) =>
            s"""{ name: ${makeStringLiteral(name)}, getter: ${function(member).isEmpty}, value: ${value(member)} }"""
          .mkString("""{ kind: "namespace", members: [""", ", ", "] }")
        case N => value(sym)
