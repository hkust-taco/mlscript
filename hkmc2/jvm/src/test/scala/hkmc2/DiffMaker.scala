package hkmc2

import scala.collection.mutable
import mlscript.utils.*, shorthands.*
import hkmc2.semantics.Elaborator
import hkmc2.bbml.*


class Outputter(val out: java.io.PrintWriter):
  val outputMarker = "//│ "
  // val oldOutputMarker = "/// "
  def apply(str: String) =
    // out.println(outputMarker + str)
    str.splitSane('\n').foreach(l => out.println(outputMarker + l))


class DiffMaker(file: os.Path, predefFile: os.Path, relativeName: Str):
  
  def doFail(blockLineNum: Int, msg: String): Unit =
    System.err.println(fansi.Color.Red("FAILURE: ").toString + msg)
  def unhandled(blockLineNum: Int, exc: Throwable): Unit =
    unexpected("exception", blockLineNum)
  
  final def unexpected(what: Str, blockLineNum: Int): Unit =
    doFail(blockLineNum, s"unexpected $what at $relativeName.${file.ext}:" + blockLineNum)
  
  
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
      if !cmd.isGlobal then cmd.unset)
  
  class Command[A](val name: Str, var isGlobal: Bool = false)(val process: Str => A):
    require(name.nonEmpty)
    require(name.forall(_.isLetterOrDigit))
    if commands.contains(name) then
      throw new IllegalArgumentException(s"Option '$name' already exists")
    commands += name -> this
    private[DiffMaker] var currentValue: Opt[A] = N
    def get: Opt[A] = currentValue
    def isSet: Bool = currentValue.isDefined
    def isUnset: Bool = !isSet
    def unset: Unit = currentValue = N
    override def toString: Str = s"${if isGlobal then "global " else ""}$name: $currentValue"
  
  class NullaryCommand(name: Str) extends Command[Unit](name)(
    line => assert(line.isEmpty))
  
  
  val global = NullaryCommand("global")
  
  val fixme = NullaryCommand("fixme")
  val fullExceptionStack = NullaryCommand("s")
  
  val debug = NullaryCommand("d")
  val dbgParsing = NullaryCommand("dp")
  
  val expectParseError = NullaryCommand("pe") // TODO handle lack of errors
  val expectTypeErrors = NullaryCommand("e") // TODO handle lack of errors
  val expectWarnings = NullaryCommand("w")
  val showRelativeLineNums = NullaryCommand("showRelativeLineNums")
  
  val showParse = NullaryCommand("p")
  val parseOnly = NullaryCommand("parseOnly")
  
  val bbml = NullaryCommand("bbml")
  
  
  val tests = Command("tests"){ case "" =>
    new DiffTests(new DiffTests.State).execute()
  }
  
  
  val fileName = file.last
  
  val fileContents = os.read(file)
  val allLines = fileContents.splitSane('\n').toList
  val strw = new java.io.StringWriter
  val out = new java.io.PrintWriter(strw)
  val output = Outputter(out)
  val report = ReportFormatter(output.apply)
  
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
  
  
  var curCtx = if file == predefFile then Elaborator.Ctx.empty else
    val raise: Raise = throw _
    
    val block = os.read(predefFile)
    val fph = new FastParseHelpers(block)
    val origin = Origin(predefFile.toString, 0, fph)
    
    val lexer = new syntax.Lexer(origin, raise, dbg = dbgParsing.isSet)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block)
    given Elaborator.Ctx = Elaborator.Ctx.empty
    val elab = Elaborator(raise)
    elab.importFrom(res)
      
  
  var bbmlTyper: Opt[BBTyper] = None
  
  @annotation.tailrec
  final def rec(lines: List[String]): Unit = lines match
    case "" :: Nil => // To prevent adding an extra newline at the end
    case (line @ "") :: ls =>
      out.println(line)
      resetCommands
      rec(ls)
    case ":exit" :: ls =>
      out.println(":exit")
      out.println(exitMarker)
      ls.dropWhile(_ =:= exitMarker).tails.foreach {
        case Nil =>
        case lastLine :: Nil => out.print(lastLine)
        case l :: _ => out.println(l)
      }
    case line :: ls if line.startsWith(":") =>
      out.println(line)
      
      val cmd = line.tail.takeWhile(!_.isWhitespace)
      val rest = line.drop(cmd.length + 1)
      
      commands.get(cmd) match
        case S(cmd) =>
          if global.isSet then cmd.isGlobal = true
          cmd.currentValue = S(cmd.process(rest))
        case N =>
          failures += allLines.size - lines.size + 1
          output("/!\\ Unrecognized command: " + cmd)
      
      rec(ls)
    case line :: ls if line.startsWith(output.outputMarker) //|| line.startsWith(oldOutputMarker)
      => rec(ls)
    case line :: ls if line.startsWith("//") =>
      out.println(line)
      rec(ls)
    case l :: ls =>
    
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
        
      try
        
        val origin = Origin(fileName, globalStartLineNum, fph)
        val raise: Raise = d =>
          d.kind match
          case Diagnostic.Kind.Error =>
            d.source match
            case Diagnostic.Source.Lexing =>
              TODO(d.source)
            case Diagnostic.Source.Parsing =>
              if expectParseError.isUnset && fixme.isUnset then
                failures += allLines.size - lines.size + 1
                // doFail(fileName, blockLineNum, "unexpected parse error at ")
                unexpected("parse error", blockLineNum)
                // report(blockLineNum, d :: Nil, showRelativeLineNums.isSet)
            case Diagnostic.Source.Typing =>
              if expectTypeErrors.isUnset && fixme.isUnset then
                failures += allLines.size - lines.size + 1
                unexpected("type error", blockLineNum)
            case Diagnostic.Source.Compilation =>
              TODO(d.source)
            case Diagnostic.Source.Runtime =>
              TODO(d.source)
          case Diagnostic.Kind.Warning =>
            TODO(d.kind)
          report(blockLineNum, d :: Nil, showRelativeLineNums.isSet)
        val lexer = new syntax.Lexer(origin, raise, dbg = dbgParsing.isSet)
        val tokens = lexer.bracketedTokens
        
        if showParse.isSet || showParse.isSet || dbgParsing.isSet then
          output(syntax.Lexer.printTokens(tokens))
        
        val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing.isSet):
          def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
        val res = p.parseAll(p.block)
        
        if parseOnly.isSet || showParse.isSet then
          output(s"Parsed:${res.map("\n\t"+_.showDbg).mkString}")
        
        // if showParse.isSet then
        //   output(s"AST: $res")
        
        if parseOnly.isUnset then
          val elab = Elaborator(raise)
          given Elaborator.Ctx = curCtx
          val (e, newCtx) = elab.topLevel(res)
          curCtx = newCtx
          output(s"Elab: ${e.showDbg}")
          if bbml.isSet then
            if bbmlTyper.isEmpty then
              bbmlTyper = S(BBTyper(raise, Ctx.init(curCtx.members)))
            val typer = bbmlTyper.get // ???
            val ty = typer.typeCheck(e)(using typer.initCtx)
            val printer = PrettyPrinter((msg: String) => output(msg))
            printer.print(ty)
          else
            val typer = typing.TypeChecker(raise)
            val ty = typer.typeProd(e)
            output(s"Type: ${ty}")
        
      catch
        case oh_noes: ThreadDeath => throw oh_noes
        case err: Throwable =>
          if fixme.isUnset then
            failures += allLines.size - lines.size + 1
            unhandled(blockLineNum, err)
          // err.printStackTrace(out)
          // println(err.getCause())
          output("/!!!\\ Uncaught error: " + err +
            err.getStackTrace().take(
              if fullExceptionStack.isSet then Int.MaxValue
              else if fixme.isSet || err.isInstanceOf[StackOverflowError] then 0
              else 10
            ).map("\n" + "\tat: " + _).mkString)
      
      rec(lines.drop(block.size))
    case Nil =>
  try rec(allLines) finally
    out.close()
  val result = strw.toString
  if result =/= fileContents then
    println(s"Updating $file...")
    os.write.over(file, result)
  
end DiffMaker

