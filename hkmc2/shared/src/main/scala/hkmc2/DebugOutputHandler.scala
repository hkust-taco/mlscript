package hkmc2

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*


/** Routes compiler debugging output without putting callbacks or mutable streams in [[Config]].
  *
  * File output is accumulated per handler and rewritten through the compiler file-system
  * abstraction. This gives every compilation session truncate-on-first-use semantics and also
  * works for the Scala.js in-memory file system, which has no append operation. */
final class DebugOutputHandler(fs: io.FileSystem, baseDir: io.Path, stdIO: Str => Unit):
  private val fileContents = mutable.Map.empty[io.Path, StringBuilder]

  def emit(out: Config.DebugOutput, line: Str): Unit = out match
    case Config.DebugOutput.StdIO => stdIO(line)
    case Config.DebugOutput.File(path) =>
      val file = baseDir / io.RelPath(path)
      val contents = fileContents.getOrElseUpdate(file, new StringBuilder)
      contents.append(line).append('\n')
      fs.write(file, contents.result())

object DebugOutputHandler:

  /** Inspect the elaborated tree directly: new resolution runs during elaboration and does not
    * traverse the legacy resolver, but annotated definitions still need their tree displayed. */
  def showElaboratedDefinitions(block: semantics.Term.Blk, config: Config)
      (display: (semantics.Definition, Config.DebugOutput) => Unit): Unit =
    def visit(statement: semantics.Statement): Unit =
      statement match
        case defn: semantics.Definition =>
          val modifiers = defn.annotations.collect:
            case semantics.Annot.Debug(modify) => modify
          if modifiers.nonEmpty then
            val localConfig = modifiers.foldLeft(config)((cfg, modify) => modify(cfg))
            if localConfig.debug.showElaboratedTree then display(defn, localConfig.debug.out)
        case _ => ()
      statement.subStatements.foreach(visit)
    visit(block)
