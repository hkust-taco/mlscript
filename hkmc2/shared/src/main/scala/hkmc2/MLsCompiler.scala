package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.MemberSymbol
import hkmc2.semantics.Elaborator
import hkmc2.syntax.Keyword.`override`
import semantics.Elaborator.State


class MLsCompiler(preludeFile: os.Path):
  
  
  given raise: Raise = d =>
    System.err.println(s"Error: $d")
    ()
  
  
  // TODO adapt logic
  val etl = new TraceLogger{override def doTrace: Bool = false}
  val ltl = new TraceLogger{override def doTrace: Bool = false}
  
  
  var dbgParsing = false
  
  
  def compileModule(file: os.Path): Unit =
    
    val block = os.read(file)
    val fph = new FastParseHelpers(block)
    val origin = Origin(file.toString, 0, fph)
    
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing)
    val tokens = lexer.bracketedTokens
    
    // if showParse.isSet || dbgParsing.isSet then
    //   output(syntax.Lexer.printTokens(tokens))
    
    given Elaborator.State = new Elaborator.State
    val rules = syntax.ParseRules()
    val p = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing):
      def doPrintDbg(msg: => Str): Unit =
        // if dbg then output(msg)
        if dbg then println(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    given Elaborator.Ctx = State.init.nest(N)
    val wd = file / os.up
    val elab = Elaborator(etl, wd)
    val resBlk = new syntax.Tree.Block(res)
    val (blk, newCtx) = elab.importFrom(resBlk)
    val low = ltl.givenIn:
      codegen.Lowering()
    val jsb = codegen.js.JSBuilder()
    val le = low.program(blk)
    val baseScp: codegen.js.Scope =
      codegen.js.Scope.empty
    val nestedScp = baseScp.nest
    val je = nestedScp.givenIn:
      jsb.program(le, S(file.baseName), wd)
    val jsStr = je.stripBreaks.mkString(100)
    val out = file / os.up / (file.baseName + ".mjs")
    os.write.over(out, jsStr)
  
  
end MLsCompiler


