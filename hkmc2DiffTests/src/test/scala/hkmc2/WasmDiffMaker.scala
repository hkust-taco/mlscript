package hkmc2

import mlscript.utils.*, shorthands.*

import codegen.wasm.*
import document.*
import semantics.Elaborator
import semantics.Term.Blk
import text.WatBuilder
import Diagnostic.Source
import Message.MessageContext

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
        doc"JSON.stringify(wasm.binaryenFmtWat(`$modWat`, true));"
          .stripBreaks
          .mkString(100)
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return
      if swat.isSet then
        output("Formatted Wat (Stack):")
        doc"JSON.stringify(wasm.binaryenFmtWat(`$modWat`, false));"
          .stripBreaks
          .mkString(100)
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return

      def mkQuery(preStr: Str, jsStr: Str)(k: Str => Unit) =
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) = host.query(
          preStr,
          queryStr,
          !expectRuntimeOrCodeGenErrors && fixme.isUnset && todo.isUnset
        )
        reply match
          case ReplHost.Result(content) => k(content)
          case ReplHost.Empty =>
          case ReplHost.Unexecuted(message) => ???
          case ReplHost.Error(isSyntaxError, message, otherOutputs) =>
            if otherOutputs.nonEmpty then
              otherOutputs.splitSane('\n').foreach: line =>
                output(s"> ${line}")
            if isSyntaxError then
              // If there is a syntax error in the generated code,
              // it should be a code generation error.
              raise(ErrorReport(
                msg"[Uncaught SyntaxError] ${message}" -> N :: Nil,
                source = Diagnostic.Source.Compilation
              ))
            else
              // Otherwise, it is considered a simple runtime error.
              raise(ErrorReport(
                msg"${message}" -> N :: Nil,
                source = Diagnostic.Source.Runtime
              ))
        if stderr.nonEmpty then output(s"// Standard Error:\n${stderr}")
      end mkQuery

      val importObj =
        doc"""{ #{  # "system": { #{  # "mem": new WebAssembly.Memory({initial: 100}) #}  # } #}  # }"""
      val jsStr =
        doc"""await wasm.binaryenPrintFuncRes( #  #{ `$modWat # `, # $importObj, # exports => exports.${mainFnNme}(), #}  # );"""
          .stripBreaks
          .mkString(100)
      output("Wasm result:")
      mkQuery("", jsStr): out =>
        // Omit the last line which is always "undefined" or the unit.
        val result = out.lastIndexOf('\n') match
          case n if n >= 0 => out.substring(0, n)
          case _ => ""
        output(s"= $result")
    end if
  end processTerm
end WasmDiffMaker
