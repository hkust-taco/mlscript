package hkmc2
package utils

import hkmc2.utils.*, shorthands.*


type TL = TraceLogger
def tl(using TL): TL = summon


abstract class TraceLogger(
  final val debug: DebugContext,
  indentWhenDisabled: Bool,
)(using printer: DebugPrinter):
  protected def phaseEnabled(config: Config.Debug): Bool
  protected def forceTrace(scope: Opt[Str]): Bool
  protected def output(out: Config.DebugOutput, line: Str): Unit

  final def debugPrinter: DebugPrinter = printer.withUids(debug.showUids)

  final def isTracing: Bool = phaseEnabled(debug.config) || forceTrace(scope)

  /** Commands can force a trace without enabling the phase in source settings.
    * Only source settings that enable the phase select a destination other than StdIO. */
  private def debugOutput: Config.DebugOutput =
    if phaseEnabled(debug.config) then debug.config.out else Config.DebugOutput.StdIO
  
  private val noPostTrace: Any => DebugPrinter ?=> Str = _ => ""
  
  private var indent = 0
  final def trace[T](pre: DebugPrinter ?=> Str, post: T => DebugPrinter ?=> Str = noPostTrace)(thunk: => T): T =
    log(pre)
    val indentTrace = indentWhenDisabled || isTracing
    if indentTrace then enter()
    val res = try thunk finally if indentTrace then exit()
    if post isnt noPostTrace then log(post(res))
    res
  inline def traceNot[T](pre: DebugPrinter ?=> Str, post: T => DebugPrinter ?=> Str = noPostTrace)(thunk: => T): T =
    thunk
  
  inline def enter() = indent += 1
  inline def exit() = indent -= 1
  
  private[hkmc2] final def emitDbg(str: Str): Unit = output(Config.DebugOutput.StdIO, str)
  
  final def logs(msgs: (DebugPrinter ?=> Any)*): Unit =
    if isTracing then msgs.foreach(msg => log(msg))
  
  final def log(msg: DebugPrinter ?=> Any, noIndent: Bool = false): Unit =
    if isTracing then
      val printer = debugPrinter
      val rendered = printer.printPlain(msg(using printer))
      output(debugOutput,
        if noIndent then rendered
        else "| " * indent + rendered.indentNewLines("| " * indent + ">  "),
      )

  final def traceDefinition[T](annotations: Ls[semantics.Annot], base: Config)(body: => T): T =
    traceDefinitionThen[T, T](annotations, base)(k => k(body))(identity)

  final def traceDefinitionThen[R, T](annotations: Ls[semantics.Annot], base: Config)
      (process: (R => T) => T)(k: R => T): T =
    DebugOutputHandler.definitionConfig(annotations, base.copy(debug = debug.config)) match
      case S(localConfig) =>
        debug.scopedThen(localConfig.debug, phaseEnabled(localConfig.debug))(process)(k)
      case N => process(k)

  private var scope: Opt[Str] = N

  final def scoped[T](flag: Str)(thunk: => T): T =
    val oldScope = scope
    scope = S(flag)
    try thunk finally scope = oldScope


object TraceLogger:
  def silent(using printer: DebugPrinter): TraceLogger =
    new TraceLogger(new DebugContext(() => printer.showUids), indentWhenDisabled = true):
      protected def phaseEnabled(config: Config.Debug): Bool = false
      protected def forceTrace(scope: Opt[Str]): Bool = false
      // FlowAnalysis.mkTraceLogger uses emitDbg to print traces enabled by its own flags,
      // so disabling this logger's traces must not discard that forwarded output.
      protected def output(out: Config.DebugOutput, line: Str): Unit = scala.Predef.println(line)
