package hkmc2

import hkmc2.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.semantics.*


class ParserSetup(file: io.Path, forceDebugParsing: Bool, outputHandler: DebugOutputHandler)
(using state: Elaborator.State, raise: Raise, cctx: CompilerCtx, config: Config, debugPrinter: DebugPrinter):
  
  val block = CompilerCtx.get.fs.read(file)
  val fph = new FastParseHelpers(block)
  val origin = Origin(file, 0, fph)
  
  private def parse(dbg: Bool, out: Config.DebugOutput): Ls[syntax.Tree] =
    val lexer = new syntax.Lexer(origin, dbg = dbg):
      override protected def doPrintDbg(msg: => Str): Unit = outputHandler.emit(out, msg)
    val tokens = lexer.bracketedTokens
    if dbg then outputHandler.emit(out, syntax.Lexer.printTokens(tokens))
    val rules = syntax.ParseRules()
    val parser = new syntax.Parser(origin, tokens, rules, raise, dbg = dbg):
      def doPrintDbg(msg: => Str): Unit = if this.dbg then outputHandler.emit(out, msg)
    parser.parseAll(parser.block(allowNewlines = true))

  private val discoveryResult = parse(dbg = false, Config.DebugOutput.StdIO)
  val effectiveConfig = ConfigParser.discoverDebugFromTrees(discoveryResult)
  val result =
    if forceDebugParsing || effectiveConfig.debug.parsing then
      parse(dbg = true, effectiveConfig.debug.out)
    else discoveryResult

  private def showSelectedParsedTrees(trees: Ls[syntax.Tree]): Unit =
    def visit(tree: syntax.Tree): Unit = tree match
      case syntax.PossiblyAnnotated(annotations, target) =>
        ConfigParser.discoverDebugFromAnnotations(annotations, effectiveConfig).foreach: localConfig =>
          if localConfig.debug.showParsedTree then
            outputHandler.emit(localConfig.debug.out, s"Parsed tree\n${tree.showAsTree}")
        target.children.foreach:
          case child: syntax.Tree => visit(child)
          case _ => ()
      case _ => ()
    trees.foreach(visit)

  if effectiveConfig.debug.showParsedTree then
    outputHandler.emit(
      effectiveConfig.debug.out,
      s"Parsed tree\n${result.map(_.showAsTree).mkString("\n")}",
    )
  else showSelectedParsedTrees(result)
  
  val resultBlk = new syntax.Tree.Block(result)

object MLsCompiler:
  /** The class contains the necessary paths to files for the MLscript compiler. */
  trait Paths:
    def preludeFile: io.Path
    def runtimeFile: io.Path
    def runtimeSourceFile: io.Path
    def termFile: io.Path

/**
  * The compiler that compiles MLscript code into JavaScript modules.
  *
  * @param mkRaise generates a separate `Raise` function for each file.
  */
class MLsCompiler
    (mkRaise: io.Path => Raise)
    (using cctx: CompilerCtx):
  
  // * The paths and the configuration are properties of the compilation session,
  // * carried by the context so that nothing can disagree with what is cached in it.
  private given Config = cctx.rootConfig
  import cctx.paths.*
  
  
  def compileModule(file: io.Path): Unit =
    
    given Raise = mkRaise(file)
    given DebugPrinter = new DebugPrinter
    
    val compilerTL = new TraceLogger:
      override def doTrace: Bool = false
    
    val preludeCtx = cctx.getPrelude(preludeFile)(using compilerTL, summon[Raise]).ctx
    val artifact = cctx.getElaboratedBlock(file, preludeCtx)(using compilerTL)
    val exportedSymbol = artifact.compilationUnit.defaultExport
    
    given Elaborator.State = artifact.state
    given Config = artifact.config
    given Elaborator.Ctx = artifact.ctx
    val jsb = compilerTL.givenIn:
      codegen.js.JSBuilder()
    val baseScp: utils.Scope =
      utils.Scope.empty(utils.Scope.Cfg.default)
    // * This line serves for `import.meta.url`, which retrieves directory and file names of mjs files.
    // * Having `module id"import" with ...` in `prelude.mls` will generate `globalThis.import` that is undefined.
    baseScp.addToBindings(Elaborator.State.importSymbol, "import", shadow = false)
    val nestedScp = baseScp.nest
    val out = file.up / io.RelPath(file.baseName + ".mjs")
    val je = nestedScp.givenIn:
      jsb.program(artifact.ir, exportedSymbol, out)
    val jsStr = je.stripBreaks.mkString(100)
    cctx.fs.write(out, jsStr)
  
  
end MLsCompiler
