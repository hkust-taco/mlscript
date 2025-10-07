package hkmc2

import mlscript.utils.*, shorthands.*

import codegen.wasm.*
import semantics.Elaborator
import semantics.Term.Blk
import text.WatBuilder
import Diagnostic.Source

import scala.collection.mutable

abstract class WasmDiffMaker extends LlirDiffMaker:

  /**
   * Outputs the compiled module as [[WasmGenerator]] implementation-defined text.
   */
  val wat = NullaryCommand("wat")

  /** Outputs the compiled module as stack-based text. */
  val swat = NullaryCommand("swat")

  /** Outputs the compiled module as folded text (i.e. S-expression). */
  val fwat = NullaryCommand("fwat")

  private val baseScp: utils.Scope =
    utils.Scope.empty

  final lazy val wasmSuppFile: os.Path = predefFile / os.up / "Wasm.mjs"
  final lazy val wasmSuppNme = baseScp.allocateName(Elaborator.State.wasmSymbol)
  final lazy val loadWasm: Unit =
    host.execute(
      s"const $wasmSuppNme = (await import(\"${wasmSuppFile}\")).default;"
    ) match
      case ReplHost.Result(msg) =>
        if msg.startsWith(ReplHost.uncaughtErrorHead) then
          output(s"Failed to load wasm support library: $msg")
      case r => output(s"Failed to load wasm support library: $r")
    ()

  /** Prettifies a JSON-stringified Binaryen-formatted Wat. */
  lazy val prettifyBinaryenWat = (content: Str) =>
    content.substring(2, content.length() - 2).replace("\\\\n", "\n").replace("\\\\\"", "\"")

  override def processTerm(trm: Blk, inImport: Bool)(using
      Config,
      Raise
  ): Unit =
    super.processTerm(trm, inImport)

    val outerRaise: Raise = summon
    val reportedMessages = mutable.Set.empty[Str]

    if wasm.isSet then
      loadWasm

      var errored = false
      given Raise =
        case d @ ErrorReport(source = Source.Compilation) =>
          errored = true
          reportedMessages += d.mainMsg
          outerRaise(d)
        case d => outerRaise(d)
      val low = ltl.givenIn:
        codegen.Lowering()
      val le = low.program(trm)
      val (modWat, mainFnNme) = ltl.givenIn:
        baseScp.nest.givenIn:
          WatBuilder().program(le, N, wd)

      if wat.isSet then
        output("Wat:")
        output(modWat.mkString())

      // A program with errors may have a WAT that is worth inspecting, but anything that involves
      // using Binaryen requires a valid WAT
      if errored then return

      if fwat.isSet then
        output("Formatted Wat (Folded):")
        s"JSON.stringify(await wasm.binaryenFmtWat(`${modWat.mkString()}`, true));"
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return
      if swat.isSet then
        output("Formatted Wat (Stack):")
        s"JSON.stringify(await wasm.binaryenFmtWat(`${modWat.mkString()}`, false));"
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return

      output("Wasm result:")
      s"""await wasm.binaryenRunFunc(`${modWat.mkString()}`, {"system": {"mem": new WebAssembly.Memory({initial: 100})}}, exports => exports.${mainFnNme}(), true);"""
        .replace('\n', ' ') |> host.execute match
        case ReplHost.Result(content) =>
          output(s"= $content")
        case err =>
          output(s"Error while executing Wasm: $err")
          return
    end if
  end processTerm
end WasmDiffMaker
