package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.semantics.Elaborator
import hkmc2.syntax.Keyword.all
import utils.*


abstract class MLsDiffMaker extends DiffMaker:
  
  val predefFile: os.Path
  
  val dbgElab = NullaryCommand("de")
  val dbgParsing = NullaryCommand("dp")
  
  val showParse = NullaryCommand("p")
  val showParsedTree = NullaryCommand("pt")
  val showElab = NullaryCommand("el")
  val showElaboratedTree = NullaryCommand("elt")
  val showContext = NullaryCommand("ctx")
  val parseOnly = NullaryCommand("parseOnly")
  val noTypeCheck = NullaryCommand("noTypeCheck")
  
  val importCmd = Command("import"): ln =>
    importFile(file / os.up / os.RelPath(ln.trim), verbose = true)
  
  val showUCS = Command("ucs"): ln =>
    ln.split(" ").iterator.map(x => "ucs:" + x.trim).toSet
  
  given Elaborator.State = new Elaborator.State
  
  val etl = new TraceLogger:
    override def doTrace = dbgElab.isSet || scope.exists:
      showUCS.get.getOrElse(Set.empty).contains
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
  
  given tl: TraceLogger with
    override def doTrace = debug.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  
  def processOrigin(origin: Origin)(using Raise): Unit =
    val oldCtx = curCtx
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    
    // If parsed tree is displayed, don't show the string serialization.
    if (parseOnly.isSet || showParse.isSet) && !showParsedTree.isSet then
      output(s"Parsed:${res.map("\n\t"+_.showDbg).mkString}")

    if showParsedTree.isSet then
      output(s"Parsed tree:")
      res.foreach(t => output(t.showAsTree))
    
    // if showParse.isSet then
    //   output(s"AST: $res")
    
    if parseOnly.isUnset then
      processTrees(res)(using raise)

    if showContext.isSet then
      output("Members:")
      curCtx.members.foreach: (k, v) =>
        if !(oldCtx.members contains k) then
          output(s"  $k -> $v")
      output("Locals:")
      curCtx.locals.foreach: (k, v) =>
        if !(oldCtx.locals contains k) then
          output(s"  $k -> $v")
  
  
  def processTrees(trees: Ls[syntax.Tree])(using Raise): Unit =
    val elab = Elaborator(etl)
    given Elaborator.Ctx = curCtx
    val (e, newCtx) = elab.topLevel(trees)
    curCtx = newCtx
    // If elaborated tree is displayed, don't show the string serialization.
    if (showElab.isSet || debug.isSet) && !showElaboratedTree.isSet then
      output(s"Elab: ${e.showDbg}")
    if showElaboratedTree.isSet then
      output(s"Elaborated tree:")
      output(e.showAsTree)
    if noTypeCheck.isUnset then
      processTerm(e)
  
  
  def processTerm(trm: semantics.Term)(using Raise): Unit =
    val typer = typing.TypeChecker()
    val ty = typer.typeProd(trm)
    output(s"Type: ${ty}")
  

