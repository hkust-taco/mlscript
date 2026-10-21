package hkmc2

import hkmc2.utils.*, shorthands.*


/** Source debug settings shared by a compilation unit's phase loggers.
  * Imported units have their own context; only their output handler is shared.
  * Compilation is synchronous within a unit, so scoped changes are restored on the call stack. */
class DebugContext:
  protected def forceUids: Bool = false

  private case class Settings(debug: Config.Debug, uidDebug: Bool)
  private var current = Settings(Config.Debug.default, false)

  final def config: Config.Debug = current.debug
  final def showUids: Bool = (current.uidDebug || forceUids) && config.showUids

  /** File directives are discovered after parsing; diff-test blocks also replace their base settings. */
  final def configure(debug: Config.Debug): Unit =
    current = Settings(debug, debug.elaboration || debug.lowering || debug.optimizations)

  private def within[T](settings: Settings)(body: => T): T =
    val saved = current
    current = settings
    try body finally current = saved

  /** A lowering continuation processes following statements in the enclosing settings.
    * Capture those settings at entry, independently of scopes entered while processing the definition. */
  final def scopedThen[R, T](config: Config.Debug, uidDebug: Bool)
      (process: (R => T) => T)(k: R => T): T =
    val outer = current
    within(Settings(config, uidDebug)):
      process(r => within(outer)(k(r)))

end DebugContext
