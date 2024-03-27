package hkmc2

import scala.collection.mutable
import mlscript.utils.*, shorthands.*


class Outputter(val out: java.io.PrintWriter):
  val outputMarker = "//│ "
  // val oldOutputMarker = "/// "
  def apply(str: String) =
    // out.println(outputMarker + str)
    str.splitSane('\n').foreach(l => out.println(outputMarker + l))


class DiffMaker(file: os.Path):
  
  def doFail(fileName: Str, blockLineNum: Int, msg: String): Unit =
    System.err.println(fansi.Color.Red("FAILURE: ").toString + msg)
  def unhandled(fileName: Str, blockLineNum: Int, exc: Throwable): Unit =
    doFail(fileName, blockLineNum, s"unhandled exception at $fileName:" + blockLineNum)
  
  
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
  val fullExceptionStack = NullaryCommand("ex")
  
  val debug = NullaryCommand("d")
  val dbgParsing = NullaryCommand("dp")
  
  val expectParseError = NullaryCommand("pe") // TODO handle lack of errors
  val expectTypeErrors = NullaryCommand("e") // TODO handle lack of errors
  val expectWarnings = NullaryCommand("w")
  val showRelativeLineNums = NullaryCommand("showRelativeLineNums")
  
  val showParse = NullaryCommand("p")
  
  
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
  
  @annotation.tailrec
  final def rec(lines: List[String]): Unit = lines match {
    case "" :: Nil => // To prevent adding an extra newline at the end
    case (line @ "") :: ls =>
      out.println(line)
      resetCommands
      rec(ls)
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
        val raise: Raise = d => report(blockLineNum, d :: Nil, showRelativeLineNums.isSet)
        val lexer = new syntax.Lexer(origin, raise, dbg = dbgParsing.isSet)
        val tokens = lexer.bracketedTokens
        
        if showParse.isSet || showParse.isSet || dbgParsing.isSet then
          output(syntax.Lexer.printTokens(tokens))
        
        val p = new syntax.Parser(origin, tokens, raise, dbg = dbgParsing.isSet) {
          def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
        }
        val res = p.parseAll(p.block)
        
        // if (parseOnly)
        //   output(s"Parsed: ${res.showDbg}")
        
        if showParse.isSet then
          output(s"AST: $res")
        
        catch {
          case oh_noes: ThreadDeath => throw oh_noes
          case err: Throwable =>
            if fixme.isUnset then
              failures += allLines.size - lines.size + 1
              unhandled(fileName, blockLineNum, err)
            // err.printStackTrace(out)
            output("/!!!\\ Uncaught error: " + err +
              err.getStackTrace().take(
                if fullExceptionStack.isSet then Int.MaxValue
                else if fixme.isSet || err.isInstanceOf[StackOverflowError] then 0
                else 10
              ).map("\n" + "\tat: " + _).mkString)
        }
      
      rec(lines.drop(block.size))
    case Nil =>
  }
  try rec(allLines) finally {
    out.close()
  }
  val result = strw.toString
  if result =/= fileContents then {
    println(s"Updating $file...")
    os.write.over(file, result)
  }
  
end DiffMaker

