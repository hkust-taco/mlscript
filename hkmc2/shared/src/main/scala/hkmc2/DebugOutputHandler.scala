package hkmc2

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*


/** Routes compiler debugging output without putting callbacks or mutable streams in [[Config]].
  *
  * A session shares one handler across compilation units: each destination is cleared on first
  * use, then appended to without retaining or rewriting previous output. Concurrent debug writes
  * are best effort; this handler does not synchronize them. */
final class DebugOutputHandler(fs: io.FileSystem, baseDir: io.Path, stdIO: Str => Unit):
  private val writtenFiles = mutable.Set.empty[io.Path]

  def emit(out: Config.DebugOutput, line: Str): Unit = out match
    case Config.DebugOutput.StdIO => stdIO(line)
    case Config.DebugOutput.File(path) =>
      val file = baseDir / io.RelPath(path)
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

  /** Keep trace routing and symbol printing in the same definition-local scope. */
  def traceDefinition[T](annotations: Ls[semantics.Annot], base: Config, enabled: Config.Debug => Bool)
      (thunk: => T)(using semantics.Elaborator.State, utils.TL): T =
    traceDefinitionThen[T, T](annotations, base, enabled)(k => k(thunk))(identity)

  /** Like [[traceDefinition]], for a definition processed in continuation-passing style, where the
    * continuation `k` processes the statements that follow the definition: `process` runs in the
    * definition's debug scope, but `k` runs back in the enclosing one, so that the definition's
    * settings do not leak to its siblings. */
  def traceDefinitionThen[R, T](annotations: Ls[semantics.Annot], base: Config, enabled: Config.Debug => Bool)
      (process: (R => T) => T)(k: R => T)(using state: semantics.Elaborator.State, tl: utils.TL): T =
    definitionConfig(annotations, tl.debugConfig(base)) match
      case S(localConfig) =>
        val debug = localConfig.debug
        state.scopedDebug(enabled(debug), debug.showUids):
          tl.scopedDebug(enabled(debug), debug):
            process: r =>
              state.inOuterDebugScope:
                tl.inOuterDebugScope(k(r))
      case N => process(k)

  /** Discover directives without committing diagnostics from a parse that may be repeated.
    * A traced parse reports its own diagnostics, in trace order; otherwise replay discovery's
    * diagnostics exactly once. Both compiler entry points use this path. */
  def parse(origin: Origin, forceDebug: Bool, showTokens: Bool, output: (Config.DebugOutput, Str) => Unit)
      (using semantics.Elaborator.State, Config, Raise): (Ls[syntax.Tree], Config) =
    def run(dbg: Bool, out: Config.DebugOutput)(using Raise): Ls[syntax.Tree] =
      val lexer = new syntax.Lexer(origin, dbg):
        override protected def doPrintDbg(msg: => Str): Unit = output(out, msg)
      val tokens = lexer.bracketedTokens
      if dbg then output(out, syntax.Lexer.printTokens(tokens))
      val parser = new syntax.Parser(origin, tokens, syntax.ParseRules(), summon[Raise], dbg):
        def doPrintDbg(msg: => Str): Unit = if this.dbg then output(out, msg)
      parser.parseAll(parser.block(allowNewlines = true))

    val diagnostics = mutable.ListBuffer.empty[Diagnostic]
    val discovery = run(false, Config.DebugOutput.StdIO)(using diagnostics += _)
    val effectiveConfig = Config.elaborationConfig(discovery)
    val result =
      // As for `TraceLogger.doForceTrace`, a parse traced only because of `forceDebug` uses `StdIO`.
      if effectiveConfig.debug.parsing then run(true, effectiveConfig.debug.out)
      else if forceDebug then run(true, Config.DebugOutput.StdIO)
      else
        diagnostics.foreach(summon[Raise])
        // Token display is a legacy diff-test option. Re-lexing does not report diagnostics twice.
        if showTokens then
          val lexer = new syntax.Lexer(origin, false)(using _ => ())
          output(Config.DebugOutput.StdIO, syntax.Lexer.printTokens(lexer.bracketedTokens))
        discovery
    result -> effectiveConfig

  def showParsedDefinitions(trees: Ls[syntax.Tree], config: Config)
      (display: (syntax.Tree, Config.DebugOutput) => Unit): Unit =
    def visit(tree: syntax.Tree): Unit = tree match
      case syntax.PossiblyAnnotated(annotations, target) =>
        ConfigParser.discoverDebugFromAnnotations(annotations, config).foreach: localConfig =>
          if localConfig.debug.showParsedTree then display(tree, localConfig.debug.out)
        target.children.foreach:
          case child: syntax.Tree => visit(child)
          case _ => ()
      case _ => ()
    trees.foreach(visit)

  /** Inspect the elaborated tree directly: new resolution runs during elaboration and does not
    * traverse the legacy resolver, but annotated definitions still need their tree displayed. */
  def showElaboratedDefinitions(block: semantics.Term.Blk, config: Config)
      (display: (semantics.Definition, Config.DebugOutput) => Unit): Unit =
    def visit(statement: semantics.Statement): Unit =
      statement match
        case defn: semantics.Definition =>
          definitionConfig(defn.annotations, config).foreach: localConfig =>
            if localConfig.debug.showElaboratedTree then display(defn, localConfig.debug.out)
        case _ => ()
      statement.subStatements.foreach(visit)
    visit(block)

  /** Methods are visited directly by BlockTraverser, without passing through applyDefn. */
  def forEachIRDefinition(program: codegen.Program, isEnabled: Config.Debug => Bool)
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
