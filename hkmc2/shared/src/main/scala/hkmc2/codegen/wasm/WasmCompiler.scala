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
  private def output(source: io.Path, extension: Str): io.Path = source.up / (source.baseName + extension)

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

  /** The runtime module, which every Wasm module imports, or `None` if building it reported an error.
    *
    * Modules refer to the runtime's bindings through the symbols of its interface, and a module merges the bindings
    * that the interfaces it imports share by these symbols. So all the modules of a session must be compiled against
    * one runtime module: it is held by the artifact of the runtime unit, from which it takes its elaboration state. All
    * artifacts depend on the runtime unit, so they are rebuilt with the runtime module when that unit changes.
    */
  def runtime()(using Raise): Opt[WasmRuntime] =
    val source = cctx.paths.runtimeSourceFile
    val prelude = cctx.getPrelude(cctx.paths.preludeFile).ctx
    val artifact = cctx.getElaboratedBlock(source, prelude)
    val wat = source.up / "RuntimeWasm.wat"
    artifact.compiledWasm:
      WasmCompiler.unlessFailed(summon[Raise]): raise =>
        WatBuilder.runtimeModule(using artifact.ctx, tl, artifact.state, raise)
    .map: compiled =>
      artifact.materialize(Ls(wat -> compiled.module.wat.mkString(100)))
      WasmRuntime(source.up / "RuntimeWasm.mjs", wat, compiled)

  /** Compiles the Wasm modules of `artifact` and of the artifacts it imports, transitively, and writes their outputs.
    * Each module reports its diagnostics to `report` applied to its source path.
    *
    * The result is `None` if `artifact` is invalid, in which case requesting it reported its errors, or if compiling
    * one of the modules reported an error. A module is compiled only if the modules it imports are, but all of these
    * are compiled even after one of them fails, so that each one reports its errors.
    */
  def compile(file: io.Path, artifact: Artifact, report: io.Path => Raise): Opt[WasmGraph] =
    if !artifact.valid then N
    else runtime()(using report(cctx.paths.runtimeSourceFile)).flatMap: support =>
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
            val sourceSymbols = art.sourceImports.map(_.sym).toSet
            art.ir.imports.foreach: (sym, importedPath) =>
              if !sourceSymbols(sym) && sym != State.runtimeSymbol then
                raise(ErrorReport(msg"JavaScript import '$importedPath' is not supported in WASM source" -> sym.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation))
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
            val imports = art.sourceImports.map(dep => emit(dep.path, dep.artifact))
            val result = if imports.contains(N) then N else build(path, art)
            result match
              case S(compiled) => done(art) = path -> compiled
              case N => failed += art
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
