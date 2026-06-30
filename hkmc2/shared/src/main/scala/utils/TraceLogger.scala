package hkmc2
package utils

import hkmc2.utils.*, shorthands.*


type TL = TraceLogger
def tl(using TL): TL = summon


abstract class TraceLogger(using val debugPrinter: DebugPrinter):
  def doTrace: Bool = true
  
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
  
  inline def log(msg: => Any): Unit = log(msg, noIndent = false)

  def logs(msgs: => Any*): Unit =
    if doTrace then msgs.foreach(log(_))
  
  def log(msg: => Any, noIndent: Bool = false): Unit =
    if doTrace then emitDbg(if noIndent then msg.toString
      else "| " * indent + msg.toString.indentNewLines("| " * indent + ">  "))

  protected var scope: Opt[Str] = N

  def scoped[T](flag: Str)(thunk: => T): T =
    var oldScope = scope
    scope = S(flag)
    try thunk finally scope = oldScope


