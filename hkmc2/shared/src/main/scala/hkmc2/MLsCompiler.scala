package hkmc2

import hkmc2.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.semantics.*


class ParserSetup(file: io.Path)(using Elaborator.State, Raise, CompilerCtx):
  
  val block = CompilerCtx.get.fs.read(file)
  val fph = new FastParseHelpers(block)
  val origin = Origin(file, 0, fph)
  
  val lexer = new syntax.Lexer(origin, dbg = false)
  val tokens = lexer.bracketedTokens
  
  val rules = syntax.ParseRules()
  val parser = new syntax.Parser(origin, tokens, rules, raise, dbg = false):
    def doPrintDbg(msg: => Str): Unit = ()
  
  val result = parser.parseAll(parser.block(allowNewlines = true))
  
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
