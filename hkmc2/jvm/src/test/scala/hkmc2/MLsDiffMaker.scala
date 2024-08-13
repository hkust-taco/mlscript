package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.semantics.Elaborator
import hkmc2.syntax.Keyword.all
import utils.TraceLogger


abstract class MLsDiffMaker extends DiffMaker:
  
  val predefFile: os.Path
  
  val dbgElab = NullaryCommand("de")
  val dbgParsing = NullaryCommand("dp")
  
  val showParse = NullaryCommand("p")
  val showElab = NullaryCommand("el")
  val parseOnly = NullaryCommand("parseOnly")
  
  val importCmd = Command("import"): ln =>
    importFile(file / os.up / os.RelPath(ln.trim), verbose = true)
  
  
  given Elaborator.State = new Elaborator.State
  
  val etl = new TraceLogger:
    override def doTrace = dbgElab.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  var curCtx = Elaborator.Ctx.empty
  
  if file =/= predefFile then importFile(predefFile, verbose = false)
  
  def importFile(fileName: Str, verbose: Bool): Unit =
    importFile(file / os.up / os.RelPath(fileName), verbose)
  
  def importFile(file: os.Path, verbose: Bool): Unit =
    
    // val raise: Raise = throw _
    given raise: Raise = d =>
      output(s"Error: $d")
      ()
    
    val block = os.read(file)
    val fph = new FastParseHelpers(block)
    val origin = Origin(file.toString, 0, fph)
    
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    given Elaborator.Ctx = curCtx
    val elab = Elaborator(etl)
    try
      val imports = elab.importFrom(res)
      if verbose then
        output(s"Imported ${imports.members.size} members")
      curCtx = curCtx.copy(members = curCtx.members ++ imports.members)
    catch
      case err: Throwable =>
        output("/!!!\\ Uncaught error during Predef import: " + err)
  
  val tl = new TraceLogger:
    override def doTrace = debug.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  
  def processOrigin(origin: Origin)(using Raise): Unit =
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    
    if parseOnly.isSet || showParse.isSet then
      output(s"Parsed:${res.map("\n\t"+_.showDbg).mkString}")
    
    // if showParse.isSet then
    //   output(s"AST: $res")
    
    if parseOnly.isUnset then
      processTrees(res)(using raise)
  
  
  def processTrees(trees: Ls[syntax.Tree])(using Raise): Unit =
    val elab = Elaborator(etl)
    given Elaborator.Ctx = curCtx
    val (e, newCtx) = elab.topLevel(trees)
    curCtx = newCtx
    if showElab.isSet || debug.isSet then
      output(s"Elab: ${e.showDbg}")
    processTerm(e)
  
  
  def processTerm(trm: semantics.Term)(using Raise): Unit =
    val typer = typing.TypeChecker()
    val ty = typer.typeProd(trm)
    output(s"Type: ${ty}")
  

