package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.MemberSymbol
import hkmc2.semantics.Elaborator
import hkmc2.syntax.Keyword.`override`


class MLsCompiler(predefFile: os.Path):
  
  
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
    
    val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing):
      def doPrintDbg(msg: => Str): Unit =
        // if dbg then output(msg)
        if dbg then println(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    given Elaborator.State = new Elaborator.State
    given Elaborator.Ctx = Elaborator.Ctx.init.nest(N)
    val elab = Elaborator(etl, file / os.up)
    val (blk, newCtx) = elab.importFrom(res)
    val low = ltl.givenIn:
      codegen.Lowering()
    val jsb = codegen.js.JSBuilder()
    val le = low.program(blk)
    val baseScp: codegen.js.Scope =
      codegen.js.Scope.empty
    val nestedScp = baseScp.nest
    val je = nestedScp.givenIn:
      jsb.program(le, S(file.baseName))
    val jsStr = je.stripBreaks.mkString(100)
    val out = file / os.up / (file.baseName + ".mjs")
    os.write.over(out, jsStr)
  
  
end MLsCompiler


