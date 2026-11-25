package hkmc2

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*


/** A compilation session shares one handler across units: each output file is overwritten on first
  * use, then appended to. Concurrent debug writes are not synchronized. */
final class DebugOutputHandler(fs: io.FileSystem, stdIO: Str => Unit) extends DebugSink:
  private val writtenFiles = mutable.Set.empty[io.Path]

  def emit(out: Config.DebugOutput, line: Str): Unit = out match
    case Config.DebugOutput.StdIO => stdIO(line)
    case Config.DebugOutput.File(file) =>
      if writtenFiles(file) then fs.append(file, line + '\n')
      else
        fs.write(file, line + '\n')
        writtenFiles += file

object DebugOutputHandler:

  def definitionConfig(annotations: Ls[semantics.Annot], base: Config): Opt[Config] =
    val modifiers = annotations.collect:
      case semantics.Annot.Debug(modify) => modify
    if modifiers.isEmpty then N
    else S(modifiers.foldLeft(base)((cfg, modify) => modify(cfg)))

  def showParsedDefinitions(trees: Ls[syntax.Tree], config: Config, sourceDir: io.Path)
      (display: (syntax.Tree, Config.DebugOutput) => Unit): Unit =
    def visit(tree: syntax.Tree): Unit = tree match
      case syntax.PossiblyAnnotated(annotations, target) =>
        ConfigParser.discoverDebugFromAnnotations(annotations, config, sourceDir).foreach: localConfig =>
          if localConfig.debug.showParsedTree then display(tree, localConfig.debug.out)
        target.children.foreach:
          case child: syntax.Tree => visit(child)
          case _ => ()
      case _ => ()
    trees.foreach(visit)

  def showElaboratedTree(block: semantics.Term.Blk, config: Config)
      (display: (Str, Str, Config.DebugOutput) => Unit)(using DebugPrinter): Unit =
    showElaborated(block, config, _.showElaboratedTree, "Elaborated tree", _.showAsTree, _.showAsTree)(display)

  def showElaboratedTerm(block: semantics.Term.Blk, config: Config, width: Int)
      (display: (Str, Str, Config.DebugOutput) => Unit)(using utils.Scope, Raise): Unit =
    given semantics.ShowCfg = semantics.ShowCfg(
      showErasedTypes = false,
      showExpansionMappings = true,
      showFlowSymbols = true, // Also disambiguates symbols that share a name.
      debug = false,
    )
    showElaborated(block, config, _.showElaboratedTerm, "Elaborated term",
      _.showTopLevel.mkString(width), _.show.mkString(width))(display)

  /** Display the whole block if the file's settings select it, and otherwise each annotated
    * definition that selects it, including definitions nested in other definitions. */
  private def showElaborated(block: semantics.Term.Blk, config: Config, isEnabled: Config.Debug => Bool, title: Str,
      showBlock: semantics.Term.Blk => Str, showDefinition: semantics.Definition => Str)
      (display: (Str, Str, Config.DebugOutput) => Unit): Unit =
    def visit(statement: semantics.Statement): Unit =
      statement match
        case defn: semantics.Definition =>
          definitionConfig(defn.annotations, config).foreach: localConfig =>
            if isEnabled(localConfig.debug) then display(title, showDefinition(defn), localConfig.debug.out)
        case _ => ()
      statement.subStatements.foreach(visit)
    if isEnabled(config.debug) then display(title, showBlock(block), config.debug.out)
    else visit(block)

  def showIR(program: codegen.Program, optimized: Bool, printer: codegen.Printer, width: Int)
      (display: (Str, Str, Config.DebugOutput) => Unit)(using Config, utils.Scope): Unit =
    val title = if optimized then "Optimized IR" else "Lowered IR"
    val isEnabled: Config.Debug => Bool = if optimized then _.showOptimizedIR else _.showIR
    if isEnabled(config.debug) then
      display(title, printer.worksheet(program).mkString(width), config.debug.out)
    else forEachIRDefinition(program, isEnabled): (defn, out) =>
      display(title, printer.printDefinition(defn).mkString(width), out)

  def showLoweredTree(program: codegen.Program)(display: (Str, Str, Config.DebugOutput) => Unit)
      (using Config, DebugPrinter): Unit =
    if config.debug.showLoweredTree then
      display("Lowered IR Tree", program.showAsTree, config.debug.out)
    else forEachIRDefinition(program, _.showLoweredTree): (defn, out) =>
      val tree = defn match
        case product: Product => product.showAsTree
      display("Lowered IR Tree", tree, out)

  /** Methods are visited directly by BlockTraverser, without passing through applyDefn. */
  private def forEachIRDefinition(program: codegen.Program, isEnabled: Config.Debug => Bool)
      (display: (codegen.Defn, Config.DebugOutput) => Unit): Unit =
    def visit(defn: codegen.Defn): Unit =
      defn.configOverride.foreach: localConfig =>
        if isEnabled(localConfig.debug) then display(defn, localConfig.debug.out)
    new codegen.BlockTraverser:
      override def applyFunDefn(fun: codegen.FunDefn): Unit =
        visit(fun)
        super.applyFunDefn(fun)
      override def applyValDefn(defn: codegen.ValDefn): Unit =
        visit(defn)
        super.applyValDefn(defn)
      override def applyClsLikeDefn(defn: codegen.ClsLikeDefn): Unit =
        visit(defn)
        super.applyClsLikeDefn(defn)
    .applyProgram(program)
