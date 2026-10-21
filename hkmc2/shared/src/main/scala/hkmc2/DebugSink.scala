package hkmc2

import hkmc2.utils.*, shorthands.*


/** Sharing a sink shares output delivery; each logger decides which messages to emit and how to format them. */
trait DebugSink:
  def emit(out: Config.DebugOutput, line: Str): Unit

object DebugSink:
  object discard extends DebugSink:
    def emit(out: Config.DebugOutput, line: Str): Unit = ()
