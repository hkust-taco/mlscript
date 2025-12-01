package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.io
import utils.*

import hkmc2.semantics.MemberSymbol
import hkmc2.semantics.Elaborator
import hkmc2.semantics.Resolver
import hkmc2.syntax.Keyword.`override`
import semantics.Elaborator.{Ctx, State}


class ParserSetup(file: io.Path, dbgParsing: Bool)(using state: Elaborator.State, raise: Raise, fs: io.FileSystem):

  val block = fs.read(file)
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
  


// * The weird type of `mkOutput` is to allow wrapping the reporting of diagnostics in synchronized blocks
class MLsCompiler(preludeFile: io.Path, mkOutput: ((Str => Unit) => Unit) => Unit)(using cfg: Config, fs: io.FileSystem):

  val runtimeFile: io.Path = preludeFile.up.up.up / io.RelPath("mlscript-compile/Runtime.mjs")
  val termFile: io.Path = preludeFile.up.up.up / io.RelPath("mlscript-compile/Term.mjs")
  
  
  val report = ReportFormatter: outputConsumer =>
    mkOutput: output =>
      outputConsumer: str =>
        output(fansi.Color.Red(str).toString)
  
  
  // TODO adapt logic
  val etl = new TraceLogger{override def doTrace: Bool = false}
  val ltl = new TraceLogger{override def doTrace: Bool = false}
  val rtl = new TraceLogger{override def doTrace: Bool = false}
  
  
  var dbgParsing = false
  
  
  def compileModule(file: io.Path): Unit =

    val wd = file.up

    given raise: Raise = d =>
      mkOutput:
        val relPath = file.relativeTo(wd.up).map(_.toString).getOrElse(file.toString)
        _(fansi.Color.LightRed(s"/!!!\\ Error in $relPath /!!!\\").toString)
      report(0, d :: Nil, showRelativeLineNums = false)
    
    given Elaborator.State = new Elaborator.State
    
    val preludeParse = ParserSetup(preludeFile, dbgParsing)
    val mainParse = ParserSetup(file, dbgParsing)
    
    val elab = Elaborator(etl, wd, Ctx.empty)
    
    val initState = State.init.nestLocal("prelude")
    
    val (pblk, newCtx) = elab.importFrom(preludeParse.resultBlk)(using initState)
    
    newCtx.nestLocal("file:"+file.baseName).givenIn:
      val elab = Elaborator(etl, wd, newCtx)
      val parsed = mainParse.resultBlk
      val (blk0, _) = elab.importFrom(parsed)
      val resolver = Resolver(rtl)
      resolver.traverseBlock(blk0)(using Resolver.ICtx.empty)
      val blk = new semantics.Term.Blk(
        semantics.Import(State.runtimeSymbol, runtimeFile.toString, runtimeFile)
        :: semantics.Import(State.termSymbol, termFile.toString, termFile)
        :: blk0.stats,
        blk0.res
      )
      val low = ltl.givenIn:
        new codegen.Lowering()
          with codegen.LoweringSelSanityChecks
      val jsb = ltl.givenIn:
        codegen.js.JSBuilder()
      val le = low.program(blk)
      val baseScp: utils.Scope =
        utils.Scope.empty
      // * This line serves for `import.meta.url`, which retrieves directory and file names of mjs files.
      // * Having `module id"import" with ...` in `prelude.mls` will generate `globalThis.import` that is undefined.
      baseScp.addToBindings(Elaborator.State.importSymbol, "import", shadow = false)
      val nestedScp = baseScp.nest
      val nme = file.baseName
      val exportedSymbol = parsed.definedSymbols.find(_._1 === nme).map(_._2)
      val je = nestedScp.givenIn:
        jsb.program(le, exportedSymbol, wd)
      val jsStr = je.stripBreaks.mkString(100)
      val out = file.up / io.RelPath(file.baseName + ".mjs")
      fs.write(out, jsStr)
  
  
end MLsCompiler


