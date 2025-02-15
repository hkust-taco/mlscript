package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.Elaborator
import hkmc2.semantics.ImplicitResolver

import semantics.Elaborator.Ctx

abstract class MLsDiffMaker extends DiffMaker:
  
  val bbmlOpt: Command[?]
  
  val rootPath: Str // * Absolute path to the root of the project
  val preludeFile: os.Path // * Contains declarations of JS builtins
  val predefFile: os.Path // * Contains MLscript standard library definitions
  val runtimeFile: os.Path = predefFile/os.up/"Runtime.mjs" // * Contains MLscript runtime definitions
  
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
  val dbgResolving = NullaryCommand("dr")
  
  val showParse = NullaryCommand("p")
  val showParsedTree = DebugTreeCommand("pt")
  val showElab = NullaryCommand("el")
  val showElaboratedTree = DebugTreeCommand("elt")
  val showResolve = NullaryCommand("r")
  val showResolvedTree = DebugTreeCommand("rt")
  val showLoweredTree = NullaryCommand("lot")
  val ppLoweredTree = NullaryCommand("slot")
  val showContext = NullaryCommand("ctx")
  val parseOnly = NullaryCommand("parseOnly")
  
  val typeCheck = FlagCommand(false, "typeCheck")
  
  
  // * Compiler configuration
  
  val noSanityCheck = NullaryCommand("noSanityCheck")
  val effectHandlers = NullaryCommand("effectHandlers")
  val stackSafe = Command("stackSafe")(_.trim)
  
  def mkConfig: Config =
    import Config.*
    if stackSafe.isSet && effectHandlers.isUnset then
      output(s"$errMarker Option ':stackSafe' requires ':effectHandlers' to be set")
    Config(
      sanityChecks = Opt.when(noSanityCheck.isUnset)(SanityChecks(light = true)),
      effectHandlers = Opt.when(effectHandlers.isSet)(EffectHandlers(
        stackSafety = stackSafe.get.flatMap:
          case "off" => N
          case value => value.toIntOption match
            case N => S(StackSafety.default)
            case S(value) =>
              if value < 0 then
                failures += 1
                output("/!\\ Stack limit must be positive, but the stack limit here is set to " + value)
                S(StackSafety.default)
              else
                S(StackSafety(stackLimit = value))
        ,
      )),
    )
  
  
  val importCmd = Command("import"): ln =>
    given Config = mkConfig
    importFile(file / os.up / os.RelPath(ln.trim), verbose = silent.isUnset)
  
  val showUCS = Command("ucs"): ln =>
    ln.split(" ").iterator.map(x => "ucs:" + x.trim).toSet
  
  given Elaborator.State = new Elaborator.State:
    override def dbg: Bool =
      dbgParsing.isSet
      || dbgElab.isSet
      || dbgResolving.isSet
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
      
  val rtl = new TraceLogger:
    override def doTrace = dbgResolving.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  var curCtx = Elaborator.State.init
  var curICtx = ImplicitResolver.ICtx.empty
  
  var prelude = Elaborator.Ctx.empty
  
  override def run(): Unit =
    if file =/= preludeFile then 
      given Config = mkConfig
      importFile(preludeFile, verbose = false)
      prelude = curCtx
    curCtx = curCtx.nest(N)
    super.run()
  
  
  override def init(): Unit =
    import syntax.*
    import Tree.*
    import Keyword.*
    given raise: Raise = d =>
      output(s"Error: $d")
      ()
    if file != preludeFile then
      given Config = mkConfig
      processTrees(
        Modified(`import`, N, StrLit(predefFile.toString))
        :: Open(Ident("Predef"))
        :: Nil)
    super.init()
  
  
  def importFile(file: os.Path, verbose: Bool)(using Config): Unit =
    
    // val raise: Raise = throw _
    given raise: Raise = d =>
      output(s"Error: $d")
      ()
    
    val block = os.read(file)
    val fph = new FastParseHelpers(block)
    val origin = Origin(file, 0, fph)
    
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
    given Elaborator.Ctx = curCtx.nest(N)
    val elab = Elaborator(etl, wd, Ctx.empty)
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
    
    given Config = mkConfig
    
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
      processTrees(res)(using summon, raise)
    
    if showContext.isSet then
      output("Env:")
      curCtx.env.foreach: (k, v) =>
        if !(oldCtx.env contains k) then
          output(s"  $k -> $v")
  
  
  private var blockNum = 0
  
  def processTrees(trees: Ls[syntax.Tree])(using Config, Raise): Unit =
    val elab = Elaborator(etl, file / os.up, prelude)
    // val blockSymbol =
    //   semantics.TopLevelSymbol("block#"+blockNum)
    blockNum += 1
    // given Elaborator.Ctx = curCtx.nest(S(blockSymbol))
    given Elaborator.Ctx = curCtx.nest(N)
    val blk = new syntax.Tree.Block(trees)
    val (e, newCtx) = elab.topLevel(blk)
    curCtx = newCtx
    // If elaborated tree is displayed, don't show the string serialization.
    if (showElab.isSet || debug.isSet) && !showElaboratedTree.isSet then
      output(s"Elab: ${e.showDbg}")
    showElaboratedTree.get.foreach: post =>
      output(s"Elaborated tree:")
      output(e.showAsTree(using post))
      
    val resolver = ImplicitResolver(rtl)
    curICtx = resolver.resolveBlk(e)(using curICtx)
    
    if showResolve.isSet then
      output(s"Resolved: ${e.showDbg}")
    showResolvedTree.get.foreach: post =>
      output(s"Resolved tree:")
      output(e.showAsTree(using post))
    
    processTerm(e, inImport = false)
      
  
  
  def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    if typeCheck.isSet then
      val typer = typing.TypeChecker()
      val ty = typer.typeProd(trm)
      output(s"Type: ${ty}")
  

