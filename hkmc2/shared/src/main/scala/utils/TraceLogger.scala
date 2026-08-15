package hkmc2
package utils

import hkmc2.utils.*, shorthands.*


type TL = TraceLogger
def tl(using TL): TL = summon


abstract class TraceLogger(using val debugPrinter: DebugPrinter):
  def doTrace: Bool = true
  protected def defaultDebugOutput: Config.DebugOutput = Config.DebugOutput.StdIO

  private var debugOverrides: Ls[(Bool, Config.DebugOutput)] = Nil

  /** Whether tracing is enabled after applying the innermost definition-local override. */
  final def isTracing: Bool = debugOverrides.headOption.fold(doTrace)(_._1)
  
  protected val noPostTrace: Any => Str = _ => ""
  
  protected var indent = 0
  def trace[T](pre: => Str, post: T => Str = noPostTrace)(thunk: => T): T =
    log(pre)
    enter()
    val res = try thunk finally exit()
    if post isnt noPostTrace then log(post(res))
    res
  inline def traceNot[T](pre: => Str, post: T => Str = noPostTrace)(thunk: => T): T =
    thunk
  
  inline def enter() = indent += 1
  inline def exit() = indent -= 1
  
  protected[hkmc2] def emitDbg(str: Str): Unit = scala.Predef.println(str)
  protected[hkmc2] def emitDbg(str: Str, out: Config.DebugOutput): Unit = emitDbg(str)
  
  inline def log(msg: => Any): Unit = log(msg, noIndent = false)

  def logs(msgs: => Any*): Unit =
    if isTracing then msgs.foreach(log(_))
  
  def log(msg: => Any, noIndent: Bool = false): Unit =
    if isTracing then emitDbg(
      if noIndent then msg.toString
      else "| " * indent + msg.toString.indentNewLines("| " * indent + ">  "),
      debugOverrides.headOption.fold(defaultDebugOutput)(_._2),
    )

  /** Temporarily select both tracing enablement and its destination.
    * Definition annotations use this to avoid leaking debug settings to sibling definitions. */
  def scopedDebug[T](enabled: Bool, out: Config.DebugOutput)(thunk: => T): T =
    debugOverrides ::= enabled -> out
    try thunk finally debugOverrides = debugOverrides.tail

  /** Run a continuation under the debug scope that surrounded the current local scope. */
  def inOuterDebugScope[T](thunk: => T): T = debugOverrides match
    case _ :: outer =>
      val current = debugOverrides
      debugOverrides = outer
      try thunk finally debugOverrides = current
    case Nil => thunk

  protected var scope: Opt[Str] = N

  def scoped[T](flag: Str)(thunk: => T): T =
    var oldScope = scope
    scope = S(flag)
    try thunk finally scope = oldScope

