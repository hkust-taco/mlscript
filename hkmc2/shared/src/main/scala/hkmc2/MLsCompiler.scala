package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.semantics.*
import hkmc2.syntax.Keyword.`override`
import semantics.Elaborator.{Ctx, State}


class ParserSetup(file: io.Path, dbgParsing: Bool)(using state: Elaborator.State, raise: Raise, cctx: CompilerCtx):
  
  val block = cctx.fs.read(file)
  val fph = new FastParseHelpers(block)
  val origin = Origin(file, 0, fph)
  
  val lexer = new syntax.Lexer(origin, dbg = dbgParsing)
  val tokens = lexer.bracketedTokens
  
  // if showParse.isSet || dbgParsing.isSet then
  //   output(syntax.Lexer.printTokens(tokens))
  
  val rules = syntax.ParseRules()
  val parser = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing):
    def doPrintDbg(msg: => Str): Unit =
      // if dbg then output(msg)
      if dbg then println(msg)
  
  val result = parser.parseAll(parser.block(allowNewlines = true))
  
  val resultBlk = new syntax.Tree.Block(result)

object MLsCompiler:
  /** The class contains the necessary paths to files for the MLscript compiler. */
  trait Paths:
    def preludeFile: io.Path
    def runtimeFile: io.Path
    def termFile: io.Path

/**
  * The compiler that compiles MLscript code into JavaScript modules.
  *
  * @param paths required paths needed by the compiler
  * @param mkRaise generates a separate `Raise` function for each file.
  * @param config the compiler's configuration object
  * @param fs the file system interface
  */
class MLsCompiler
    (paths: MLsCompiler.Paths, mkRaise: io.Path => Raise)
    (using cctx: CompilerCtx, config: Config):
  import paths.*
  
  
  
  // TODO adapt logic
  given DebugPrinter = new DebugPrinter
  val etl = new TraceLogger{override def doTrace: Bool = false}
  val ltl = new TraceLogger{override def doTrace: Bool = false}
  // val ltl = new TraceLogger{override def doTrace: Bool = true}
  val rtl = new TraceLogger{override def doTrace: Bool = false}
  
  
  var dbgParsing = false
  var dbgElab = false
  
  
  def compileModule(file: io.Path): Unit =
    
    val wd = file.up
    
    given Raise = mkRaise(file)
    
    given Elaborator.State = new Elaborator.State:
      override def dbg: Bool = dbgElab
    
    val preludeParse = ParserSetup(preludeFile, dbgParsing)
    val mainParse = ParserSetup(file, dbgParsing)
    
    val elab = Elaborator(etl, wd, Ctx.empty)
    
    val initState = State.init.nestLocal("prelude")
    
    val (pblk, newCtx) = elab.importFrom(preludeParse.resultBlk)(using initState)
    
    newCtx.nestLocal("file:"+file.baseName).givenIn:
      given CompilerCtx = cctx.derive(file)
      val elab = Elaborator(etl, wd, newCtx)
      val parsed = mainParse.resultBlk
      val (blk0, _) = elab.importFrom(parsed)
      val resolver = Resolver(rtl)
      resolver.traverseBlock(blk0)(using Resolver.ICtx.empty)
      def findQuote(t: semantics.Statement): Bool = t match
        case Term.Quoted(_) | Term.Unquoted(_) => true
        case Term.Ref(sym) => sym === State.termSymbol
        case _ => t.subTerms.exists(findQuote)
      val hasQuote = findQuote(blk0)
      val blk = new Term.Blk(
        Import(State.runtimeSymbol, runtimeFile.toString, runtimeFile) ::
          // Only import `Term.mls` when necessary.
          (if hasQuote then
            Import(State.termSymbol, termFile.toString, termFile) :: blk0.stats
          else
            blk0.stats),
        blk0.res
      )
      val low = ltl.givenIn:
        new codegen.Lowering()
          with codegen.LoweringSelSanityChecks
      val jsb = ltl.givenIn:
        codegen.js.JSBuilder()
      val le_0 = low.program(blk)
      val nme = file.baseName
      val exportedSymbol = parsed.definedSymbols.find(_._1 === nme).map(_._2)
      val le_1 = ltl.givenIn:
        codegen.BlockSimplifier(exportedSymbol.toSet)(le_0)
      val le_2 = ltl.givenIn:
        codegen.DeadParamElim(le_1)
      val baseScp: utils.Scope =
        utils.Scope.empty(utils.Scope.Cfg.default)
      // * This line serves for `import.meta.url`, which retrieves directory and file names of mjs files.
      // * Having `module id"import" with ...` in `prelude.mls` will generate `globalThis.import` that is undefined.
      baseScp.addToBindings(Elaborator.State.importSymbol, "import", shadow = false)
      val nestedScp = baseScp.nest
      val je = nestedScp.givenIn:
        jsb.program(le_2, exportedSymbol, wd)
      val jsStr = je.stripBreaks.mkString(100)
      val out = file.up / io.RelPath(file.baseName + ".mjs")
      cctx.fs.write(out, jsStr)
  
  
end MLsCompiler


