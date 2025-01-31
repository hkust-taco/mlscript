package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.MemberSymbol
import hkmc2.semantics.Elaborator
import hkmc2.syntax.Keyword.`override`
import semantics.Elaborator.State


class ParserSetup(file: os.Path, dbgParsing: Bool)(using Elaborator.State, Raise):
  
  val block = os.read(file)
  val fph = new FastParseHelpers(block)
  val origin = Origin(file.toString, 0, fph)
  
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
  


class MLsCompiler(preludeFile: os.Path):
  
  
  val report = ReportFormatter: str =>
    System.out.println(fansi.Color.Red(str))
  
  
  // TODO adapt logic
  val etl = new TraceLogger{override def doTrace: Bool = false}
  val ltl = new TraceLogger{override def doTrace: Bool = false}
  
  
  var dbgParsing = false
  
  
  def compileModule(file: os.Path): Unit =
    
    val wd = file / os.up
    
    given raise: Raise = d =>
      System.out.println(fansi.Color.LightRed(s"/!!!\\ Error in ${file.relativeTo(wd/os.up)} /!!!\\"))
      report(0, d :: Nil, showRelativeLineNums = false)
    
    given Elaborator.State = new Elaborator.State
    
    val preludeParse = ParserSetup(preludeFile, dbgParsing)
    val mainParse = ParserSetup(file, dbgParsing)
    
    val elab = Elaborator(etl, wd)
    
    val initState = State.init.nest(N)
    
    val (pblk, newCtx) = elab.importFrom(preludeParse.resultBlk)(using initState)
    
    newCtx.nest(N).givenIn:
      
      val parsed = mainParse.resultBlk
      val (blk, newCtx) = elab.importFrom(parsed)
      val low = ltl.givenIn:
        codegen.Lowering(lowerHandlers = false, stackLimit = None) // TODO: properly hook up stack limit
      val jsb = ltl.givenIn:
        codegen.js.JSBuilder()
      val le = low.program(blk)
      val baseScp: utils.Scope =
        utils.Scope.empty
      val nestedScp = baseScp.nest
      val nme = file.baseName
      val exportedSymbol = parsed.definedSymbols.find(_._1 === nme).map(_._2)
      val je = nestedScp.givenIn:
        jsb.program(le, exportedSymbol, wd)
      val jsStr = je.stripBreaks.mkString(100)
      val out = file / os.up / (file.baseName + ".mjs")
      os.write.over(out, jsStr)
  
  
end MLsCompiler


