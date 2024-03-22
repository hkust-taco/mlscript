package hkmc2

// import ammonite.ops.*
// import os.Path
import scala.collection.mutable
import mlscript.utils.*, shorthands.*

case class Mode(
  global: Bool,
  expectTypeErrors: Bool, expectWarnings: Bool, expectParseErrors: Bool,
  fixme: Bool, showParse: Bool, verbose: Bool, noSimplification: Bool,
  explainErrors: Bool, dbg: Bool, dbg_err: Bool, fullExceptionStack: Bool,
  dbgParsing: Bool = false,
)
object Mode:
  val init = Mode(
    false, false, false, false, false, false, false, false, false, false, false, false)
end Mode

class Outputter(val out: java.io.PrintWriter):
  val outputMarker = "//│ "
  // val oldOutputMarker = "/// "
  def apply(str: String) = out.println(outputMarker + str)

abstract class DiffMaker:
  
  def doFail(msg: String): Unit
  
  val outputMarker = "//│ "
  // val oldOutputMarker = "/// "
  
  val diffBegMarker = "<<<<<<<"
  val diffMidMarker = "======="
  val diff3MidMarker = "|||||||" // * Appears under `git config merge.conflictstyle diff3` (https://stackoverflow.com/a/18131595/1518588)
  val diffEndMarker = ">>>>>>>"
  
  val exitMarker = "=" * 100
  
  
  private val commands: mutable.Map[Str, Command[?]] = mutable.Map.empty
  
  def resetCommands: Unit =
    commands.valuesIterator.foreach(cmd =>
      if !cmd.isGlobal then cmd.currentValue = N)
  
  class Command[A](val name: Str, val process: Str => A, var isGlobal: Bool = false):
    require(name.nonEmpty)
    require(name.forall(_.isLetterOrDigit))
    if commands.contains(name) then
      throw new IllegalArgumentException(s"Option '$name' already exists")
    commands += name -> this
    private[DiffMaker] var currentValue: Opt[A] = N
    def get: Opt[A] = currentValue
    def isSet: Bool = currentValue.isDefined
  
  class NullaryCommand(name: Str) extends Command[Unit](name,
    line => assert(line.isEmpty))
  
  
  val global = NullaryCommand("global")
  
  val debug = NullaryCommand("d")
  val showParse = NullaryCommand("p")
  
  
  def apply(file: os.Path): Unit =
    val fileName = file.toString
    
    val fileContents = os.read(file)
    val allLines = fileContents.splitSane('\n').toList
    val strw = new java.io.StringWriter
    val out = new java.io.PrintWriter(strw)
    // def output(str: String) = out.println(outputMarker + str)
    val output = Outputter(out)
    
    // val typer = new Typer {
    //   dbg = false
    //   verbose = false
    //   explainErrors = false
    //   override def emitDbg(str: String): Unit = output(str)
    // }
    // var ctx: typer.Ctx = typer.Ctx.init
    val failures = mutable.Buffer.empty[Int]
    
    var _onlyParse = false
    var _allowTypeErrors = false
    var _showRelativeLineNums = false
    
    var defaultMode = Mode.init
    
    def showMode(m: Mode): Str =
      m.productElementNames.zip:
        Iterator.tabulate(m.productArity)(m.productElement)
      .map(_.toString + "=" + _) mkString ", "
    
    def rec(lines: List[String], mode: Mode): Unit = lines match {
      case "" :: Nil =>
      case line :: ls if line.startsWith(":") =>
        out.println(line)
        
        /* 
        // def updateMode(m: Mode): Mode = 
        val newMode = line.tail.takeWhile(!_.isWhitespace) match {
          case "global" => mode.copy(global = true)
          case "e" => mode.copy(expectTypeErrors = true)
          case "w" => mode.copy(expectWarnings = true)
          case "pe" => mode.copy(expectParseErrors = true)
          case "p" => mode.copy(showParse = true)
          // case "q" => ls.foreach(out.println); return
          case "q" =>
            val msg = "====== TEST ABORTED – THE REST OF THIS FILE IS NOT PROCESSED ======"
            output(msg)
            // out.print(ls.mkString("\n")); return
            out.print(ls.dropWhile(_.endsWith(msg)).mkString("\n")); return
          case "d" => mode.copy(dbg = true)
          case "de" => mode.copy(dbg_err = true)
          case "s" => mode.copy(fullExceptionStack = true)
          case "v" | "verbose" => mode.copy(verbose = true)
          case "ex" | "explain" => mode.copy(expectTypeErrors = true, explainErrors = true)
          case "ns" | "no-simpl" => mode.copy(noSimplification = true)
          // case "InferPreciseTypes" => typer.mergeFunctionTypes = false; mode
          case "OnlyParse" => _onlyParse = true; mode
          case "AllowTypeErrors" => _allowTypeErrors = true; mode
          case "ShowRelativeLineNums" => _showRelativeLineNums = true; mode
          // case "import" =>
          //   val arg = line.tail.dropWhile(!_.isWhitespace).dropWhile(_.isWhitespace)
          //   val file = pwd/"src"/"test"/"supertype"/"diff"/(arg + ".sup")
          //   if mode.dbg then output(s"Importing '${file}'...")
          //   val ans = ModuleTyper(file, typer, ctx, mode, failures, output)
          //   if mode.dbg then if ans.nonEmpty then out.println(ans)
          //   mode
          case _ =>
            failures += allLines.size - lines.size
            output("/!\\ Unrecognized option " + line)
            mode
        }
        if mode.global then defaultMode = newMode.copy(global = false)
        rec(ls, newMode)
        */
        
        val cmd = line.tail.takeWhile(!_.isWhitespace)
        val rest = line.drop(cmd.length + 1)
        
        commands.get(cmd) match
          case S(cmd) =>
            cmd.currentValue = S(cmd.process(rest))
            if global.isSet then cmd.isGlobal = true
          case N =>
            failures += allLines.size - lines.size
            output("/!\\ Unrecognized command: " + cmd)
        
        rec(ls, mode)
      case line :: ls if line.startsWith("// FIXME") /* || line.startsWith("// TODO") */ =>
        out.println(line)
        rec(ls, mode.copy(fixme = true))
      case line :: ls if line.startsWith(output.outputMarker) //|| line.startsWith(oldOutputMarker)
        => rec(ls, defaultMode)
      case line :: ls if line.startsWith("//") =>
        out.println(line)
        rec(ls, mode)
      case line :: ls if line.isEmpty =>
        out.println(line)
        rec(ls, defaultMode)
      case l :: ls =>
        // val block = (l :: ls.takeWhile(l => l.nonEmpty && !(
        //   l.startsWith(output.outputMarker)
        //   // || l.startsWith(oldOutputMarker)
        // ))).toIndexedSeq
        // block.foreach(out.println)
        // // output(showMode(mode))
        
        val blockLineNum = (allLines.size - lines.size) + 1
        
        val block = (l :: ls.takeWhile(l => l.nonEmpty && !(
          l.startsWith(outputMarker)
          || l.startsWith(diffBegMarker)
          // || l.startsWith(oldOutputMarker)
        ))).toIndexedSeq
        block.foreach(out.println)
        val processedBlock = block
        val processedBlockStr = processedBlock.mkString
        val fph = new FastParseHelpers(block)
        val globalStartLineNum = allLines.size - lines.size + 1
        
        val origin = Origin(fileName, globalStartLineNum, fph)
        // type Raise = Diagnostic => Unit
        val raise: Raise = throw _ // TODO
        val lexer = new Lexer(origin, raise, dbg = mode.dbgParsing)
        val tokens = lexer.bracketedTokens
        
        if showParse.isSet || mode.showParse || mode.dbgParsing then
          output(Lexer.printTokens(tokens))
        
        //
        // output(showMode(mode))
        // 
        /* 
        val fph = FastParseHelpers(block)
        val _globalStartLineNum = allLines.size - lines.size + 1
        // val parser = new Parser(Origin(fileName, _globalStartLineNum, fph))
        // val parser = Parser(fph.blockStr.toArray)
        val origin = Origin(fileName, _globalStartLineNum, fph)
        val parser = Parser(origin)
        // val ppDiags = mutable.Buffer.empty[Diagnostic[Not]]
        // val preparser = PreParser(origin, ppDiags.+=)
        /* 
        val toks = preparser.tokens()
        println("LX: " + preparser.printTokens(toks))
        println("PP: " + preparser.parse(toks))
        */
        // ppDiags
        // val globalLineNum = (allLines.size - lines.size) + lineNum
        val lineOffset = allLines.size - lines.size
        val mt = new ModuleTyper(typer, ctx, output, lineOffset, failures):
          override val globalStartLineNum = _globalStartLineNum
          override def onlyParse = _onlyParse
          override def allowTypeErrors = _allowTypeErrors
          override def showRelativeLineNums = _showRelativeLineNums
          override def doSimplify = !mode.noSimplification
        val ans = mt.ans(parser, fph, origin, mode)
        // val ans = mt.ans(preparser, parser, fph, origin, mode)
        if (ans.nonEmpty) out.println(ans)
        */
        
        rec(lines.drop(block.size), mode)
        if mode.dbg then
          println("=== DONE ===")
      case Nil =>
    }
    try rec(allLines, defaultMode) finally {
      out.close()
    }
    val result = strw.toString
    if result =/= fileContents then {
      println(s"Updating $file...")
      os.write.over(file, result)
    }
    if failures.nonEmpty then
      // fail(s"Unexpected diagnostics (or lack thereof) at: " + failures.map("l."+_).mkString(", "))(dummyPos)
      doFail(s"Unexpected diagnostics (or lack thereof) at: " + failures.map("l."+_).mkString(", "))
    
end DiffMaker

