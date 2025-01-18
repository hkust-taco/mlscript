package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.Elaborator


abstract class MLsDiffMaker extends DiffMaker:
  
  val bbmlOpt: Command[?]
  
  val rootPath: Str // * Absolute path to the root of the project
  val preludeFile: os.Path // * Contains declarations of JS builtins
  val predefFile: os.Path // * Contains MLscript standard library definitions
  
  val wd = file / os.up
  
  class DebugTreeCommand(name: Str) extends Command[Product => Str](name)(
    line => if line.contains("loc") then
      (t: Product) => t match
        case t: Located => t.toLoc.fold("(no loc)"): loc =>
          val (sl, _, sc) = loc.origin.fph.getLineColAt(loc.spanStart)
          val (el, _, ec) = loc.origin.fph.getLineColAt(loc.spanEnd)
          s"$sl:$sc-$el:$ec"
        case _ => ""
    else 
      Function.const("")
  ):
    def post: Product => Str = get.getOrElse(Function.const(""))
  
  val silent = NullaryCommand("silent")
  val dbgElab = NullaryCommand("de")
  val dbgParsing = NullaryCommand("dp")
  
  val showParse = NullaryCommand("p")
  val showParsedTree = DebugTreeCommand("pt")
  val showElab = NullaryCommand("el")
  val showElaboratedTree = DebugTreeCommand("elt")
  val showLoweredTree = NullaryCommand("lot")
  val ppLoweredTree = NullaryCommand("slot")
  val showContext = NullaryCommand("ctx")
  val parseOnly = NullaryCommand("parseOnly")
  
  val typeCheck = FlagCommand(false, "typeCheck")
  
  val importCmd = Command("import"): ln =>
    importFile(file / os.up / os.RelPath(ln.trim), verbose = silent.isUnset)
  
  val showUCS = Command("ucs"): ln =>
    ln.split(" ").iterator.map(x => "ucs:" + x.trim).toSet
  
  given Elaborator.State = new Elaborator.State:
    override def dbg: Bool =
      dbgParsing.isSet
      || dbgElab.isSet
      || debug.isSet
  
  val etl = new TraceLogger:
    override def doTrace = dbgElab.isSet || scope.exists:
      showUCS.get.getOrElse(Set.empty).contains
    override def emitDbg(str: String): Unit = output(str)
    override def trace[T](pre: => Str, post: T => Str = noPostTrace)(thunk: => T): T =
      // * This override is for avoiding to increase the indentation when tracing if doTrace is false,
      // * so that selectively-enabled tracing doesn't get strange indentation.
      // * Perhaps this should be the default behavior of TraceLogger.
      if doTrace then super.trace(pre, post)(thunk)
      else thunk
  
  var curCtx = Elaborator.State.init
  
  
  override def run(): Unit =
    if file =/= preludeFile then importFile(preludeFile, verbose = false)
    curCtx = curCtx.nest(N)
    super.run()
  
  
  override def init(): Unit =
    import syntax.*
    import Tree.*
    import Keyword.*
    given raise: Raise = d =>
      output(s"Error: $d")
      ()
    processTrees(
      Modified(`import`, N, StrLit(predefFile.toString))
      :: Open(Ident("Predef"))
      :: Nil)
    super.init()
  
  
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
    
    val rules = syntax.ParseRules()
    val p = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    val imprtSymbol =
      semantics.TopLevelSymbol("import#"+file.baseName)
    given Elaborator.Ctx = curCtx.nest(S(imprtSymbol))
    val elab = Elaborator(etl, wd)
    try
      val resBlk = new syntax.Tree.Block(res)
      val (e, newCtx) = elab.importFrom(resBlk)
      val ctxWithImports = newCtx.withMembers(resBlk.definedSymbols)
      if verbose then
        output(s"Imported ${resBlk.definedSymbols.size} member(s)")
      curCtx = ctxWithImports
      processTerm(e, inImport = true)
    catch
      case err: Throwable =>
        uncaught(err)
  
  given tl: TraceLogger with
    override def doTrace = debug.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  
  def processOrigin(origin: Origin)(using Raise): Unit =
    val oldCtx = curCtx
    
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val rules = syntax.ParseRules()
    val p = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    
    // If parsed tree is displayed, don't show the string serialization.
    if (parseOnly.isSet || showParse.isSet) && !showParsedTree.isSet then
      output(s"Parsed:${res.map("\n\t"+_.showDbg).mkString}")

    showParsedTree.get.foreach: post =>
      output(s"Parsed tree:")
      res.foreach(t => output(t.showAsTree(using post)))  
    
    // if showParse.isSet then
    //   output(s"AST: $res")
    
    if parseOnly.isUnset then
      processTrees(res)(using raise)
    
    if showContext.isSet then
      output("Env:")
      curCtx.env.foreach: (k, v) =>
        if !(oldCtx.env contains k) then
          output(s"  $k -> $v")
  
  
  private var blockNum = 0
  
  def processTrees(trees: Ls[syntax.Tree])(using Raise): Unit =
    val elab = Elaborator(etl, file / os.up)
    val blockSymbol =
      semantics.TopLevelSymbol("block#"+blockNum)
    blockNum += 1
    given Elaborator.Ctx = curCtx.nest(S(blockSymbol))
    val blk = new syntax.Tree.Block(trees)
    val (e, newCtx) = elab.topLevel(blk)
    curCtx = newCtx
    // If elaborated tree is displayed, don't show the string serialization.
    if (showElab.isSet || debug.isSet) && !showElaboratedTree.isSet then
      output(s"Elab: ${e.showDbg}")
    showElaboratedTree.get.foreach: post =>
      output(s"Elaborated tree:")
      output(e.showAsTree(using post))
    processTerm(e, inImport = false)
      
  
  
  def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    if typeCheck.isSet then
      val typer = typing.TypeChecker()
      val ty = typer.typeProd(trm)
      output(s"Type: ${ty}")
  

