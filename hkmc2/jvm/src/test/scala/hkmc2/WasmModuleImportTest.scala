package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import mlscript.utils._, shorthands._
import io.PlatformPath.given

class WasmModuleImportTest extends AnyFunSuite:

  private val workingDir = os.pwd
  private val mainTestDir = TestFolders.mainTestDir(workingDir)
  private val compileDir = TestFolders.compileTestDir(workingDir)

  private def compiler(report: ReportFormatter)(using CompilerCtx, Config): MLsCompiler =
    MLsCompiler(
      paths = new MLsCompiler.Paths:
        val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
        val runtimeFile = compileDir / "Runtime.mjs"
        val termFile = compileDir / "Term.mjs"
      ,
      mkRaise = report.mkRaise,
    )

  test("compiler wires wasm file imports through generated wat and glue"):
    given CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)
    given Config = Config.default(mainTestDir)

    val report = ReportFormatter(_ => (), colorize = false)
    val wasmDir = compileDir / "wasm"
    val entryFile = wasmDir / "ImportValue.mls"
    val importedModule = wasmDir / "IVal.mjs"
    val importedWat = wasmDir / "IVal.wat"
    val importedRelativePath = "./" + importedModule.relativeTo(wasmDir).toString

    val mlxCompiler = compiler(report)
    if os.exists(importedModule) then os.remove(importedModule)
    if os.exists(importedWat) then os.remove(importedWat)
    mlxCompiler.compileModule(entryFile)

    assert(report.badLines.isEmpty, "Wasm module import fixture should compile without diagnostics")
    assert(os.exists(importedModule), "Compiling an importer should emit dependency glue")
    assert(os.exists(importedWat), "Compiling an importer should emit dependency WAT")
    assert(os.exists(wasmDir / "ImportValue.mjs"), "Importer Wasm glue should be generated")
    assert(os.exists(wasmDir / "ImportValue.wat"), "Importer WAT should be generated")

    val importerWat = os.read(wasmDir / "ImportValue.wat")
    assert(
      importerWat.contains(s""""${importedModule.toString}""""),
      "Importer WAT should import from the generated dependency module",
    )

    val importerGlue = os.read(wasmDir / "ImportValue.mjs")
    assert(
      importerGlue.contains(s"""import { __mlx_wasm as __mlx_dep_0 } from "$importedRelativePath";"""),
      "Importer glue should load the dependency glue module",
    )
    assert(
      importerGlue.contains(s"""importObject["${importedModule.toString}"] = (await __mlx_dep_0()).instance.exports"""),
      "Importer glue should pass dependency exports into instantiation",
    )

    val importedModuleUrl = (wasmDir / "ImportValue.mjs").toIO.toURI.toString
    val runtimeCheck = os.proc(
      "node",
      "--input-type=module",
      "-e",
      """const [url] = process.argv.slice(1);
        |try {
        |  const mod = await import(url);
        |  await mod.__mlx_wasm();
        |  console.log("ok");
        |} catch (err) {
        |  console.error(err?.stack ?? String(err));
        |  process.exit(1);
        |}
        |""".stripMargin,
      importedModuleUrl,
    ).call(cwd = workingDir)
    assert(runtimeCheck.out.text().trim == "ok", "Generated importer glue should instantiate successfully")

end WasmModuleImportTest
