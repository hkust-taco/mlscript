package hkmc2

import hkmc2.utils.*, shorthands.*


/** Source debug settings shared by a compilation unit's phase loggers.
  * Imported units have their own context; only their output handler is shared.
  * Compilation is synchronous within a unit, so scoped changes are restored on the call stack. */
final class DebugContext(forceUids: () => Bool):
  def this() = this(() => false)

  private case class Settings(debug: Config.Debug, uidDebug: Bool)
  private var current = Settings(Config.Debug.default, false)

  def config: Config.Debug = current.debug
  def showUids: Bool = (current.uidDebug || forceUids()) && config.showUids

  /** File directives are discovered after parsing; diff-test blocks also replace their base settings. */
  def configure(debug: Config.Debug): Unit =
    current = Settings(debug, debug.elaboration || debug.lowering || debug.optimizations)

  private def within[T](settings: Settings)(body: => T): T =
    val saved = current
    current = settings
    try body finally current = saved

  def traceDefinition[T](annotations: Ls[semantics.Annot], base: Config, enabled: Config.Debug => Bool)
      (body: => T): T =
    traceDefinitionThen[T, T](annotations, base, enabled)(k => k(body))(identity)

  /** A lowering continuation processes following statements in the enclosing settings.
    * Capture those settings at entry, independently of scopes entered while processing the definition. */
  def traceDefinitionThen[R, T](annotations: Ls[semantics.Annot], base: Config, enabled: Config.Debug => Bool)
      (process: (R => T) => T)(k: R => T): T =
    DebugOutputHandler.definitionConfig(annotations, base.copy(debug = config)) match
      case S(localConfig) =>
        val outer = current
        within(Settings(localConfig.debug, enabled(localConfig.debug))):
          process(r => within(outer)(k(r)))
      case N => process(k)

end DebugContext
