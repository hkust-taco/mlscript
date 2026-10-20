package hkmc2
package utils

import hkmc2.utils.*, shorthands.*


type TL = TraceLogger
def tl(using TL): TL = summon


final class TraceLogger(
  val debug: DebugContext,
  phase: Config.Debug => Bool,
  force: Opt[Str] => Bool,
  output: (Config.DebugOutput, Str) => Unit,
  indentWhenDisabled: Bool,
)(using printer: DebugPrinter):
  def debugPrinter: DebugPrinter = printer.withUids(debug.showUids)

  def isTracing: Bool = phase(debug.config) || force(scope)

  /** Commands can force a trace without enabling the phase in source settings.
    * Only source settings that enable the phase select a destination other than StdIO. */
  private def debugOutput: Config.DebugOutput =
    if phase(debug.config) then debug.config.out else Config.DebugOutput.StdIO
  
  private val noPostTrace: Any => DebugPrinter ?=> Str = _ => ""
  
  private var indent = 0
  def trace[T](pre: DebugPrinter ?=> Str, post: T => DebugPrinter ?=> Str = noPostTrace)(thunk: => T): T =
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
  
  private[hkmc2] def emitDbg(str: Str): Unit = output(Config.DebugOutput.StdIO, str)
  
  def logs(msgs: (DebugPrinter ?=> Any)*): Unit =
    if isTracing then msgs.foreach(msg => log(msg))
  
  def log(msg: DebugPrinter ?=> Any, noIndent: Bool = false): Unit =
    if isTracing then
      val printer = debugPrinter
      val rendered = printer.printPlain(msg(using printer))
      output(debugOutput,
        if noIndent then rendered
        else "| " * indent + rendered.indentNewLines("| " * indent + ">  "),
      )

  def traceDefinition[T](annotations: Ls[semantics.Annot], base: Config)(body: => T): T =
    debug.traceDefinition(annotations, base, phase)(body)

  def traceDefinitionThen[R, T](annotations: Ls[semantics.Annot], base: Config)
      (process: (R => T) => T)(k: R => T): T =
    debug.traceDefinitionThen(annotations, base, phase)(process)(k)

  private var scope: Opt[Str] = N

  def scoped[T](flag: Str)(thunk: => T): T =
    val oldScope = scope
    scope = S(flag)
    try thunk finally scope = oldScope


object TraceLogger:
  /** A logger controlled independently of source directives, such as a diff-test command or a pass flag. */
  def apply(enabled: Opt[Str] => Bool, output: Str => Unit)(using printer: DebugPrinter): TraceLogger =
    new TraceLogger(new DebugContext(() => printer.showUids), _ => false, enabled, (_, line) => output(line), indentWhenDisabled = true)

  def silent(using DebugPrinter): TraceLogger = apply(_ => false, line => scala.Predef.println(line))
