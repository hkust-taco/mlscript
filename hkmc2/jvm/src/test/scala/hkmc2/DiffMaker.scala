package hkmc2

import scala.collection.mutable
import mlscript.utils.*, shorthands.*



class Outputter(val out: java.io.PrintWriter):
  
  val outputMarker = "//│ "
  // val oldOutputMarker = "/// "

  val diffBegMarker = "<<<<<<<"
  val diffMidMarker = "======="
  val diff3MidMarker = "|||||||" // * Appears under `git config merge.conflictstyle diff3` (https://stackoverflow.com/a/18131595/1518588)
  val diffEndMarker = ">>>>>>>"

  val exitMarker = "=" * 100
  
  def apply(str: String) =
    // out.println(outputMarker + str)
    str.splitSane('\n').foreach(l => out.println(outputMarker + l))



abstract class DiffMaker:
  
  val file: os.Path
  val relativeName: Str
  
  def processOrigin(origin: Origin)(using Raise): Unit
  
  
  
  def doFail(blockLineNum: Int, msg: String): Unit =
    System.err.println(fansi.Color.Red("FAILURE: ").toString + msg)
  def unhandled(blockLineNum: Int, exc: Throwable): Unit =
    unexpected("exception", blockLineNum)
  
  final def unexpected(what: Str, blockLineNum: Int): Unit =
    output(s"FAILURE: Unexpected $what")
    doFail(blockLineNum, s"unexpected $what at $relativeName.${file.ext}:" + blockLineNum)
  
  
  
  private val commands: mutable.Map[Str, Command[?]] = mutable.Map.empty
  
  def resetCommands: Unit =
    commands.valuesIterator.foreach(cmd =>
      if !cmd.isGlobal then cmd.unset)
  
  class Command[A](val name: Str, var isGlobal: Bool = false)(val process: Str => A):
    require(name.nonEmpty)
    require(name.forall(l => l.isLetterOrDigit || l === '!'))
    if commands.contains(name) then
      throw new IllegalArgumentException(s"Option '$name' already exists")
    commands += name -> this
    private var currentValue: Opt[A] = N
    private[hkmc2] def setCurrentValue(a: A): Unit =
      currentValue = S(a)
      onSet()
    def get: Opt[A] = currentValue
    def isSet: Bool = currentValue.isDefined
    def isUnset: Bool = !isSet
    def unset: Unit = currentValue = N
    def onSet(): Unit = ()
    override def toString: Str = s"${if isGlobal then "global " else ""}$name: $currentValue"
  
  class NullaryCommand(name: Str) extends Command[Unit](name)(
    line =>
      val commentIndex = line.indexOf("//")
      val body = if commentIndex == -1 then line else line.take(commentIndex)
      assert(body.forall(_.isWhitespace)))
  
  class FlagCommand(init: Bool, name: Str) extends NullaryCommand(name):
    self =>
    val disable = new NullaryCommand("!" + name):
      override def onSet(): Unit =
        if isSet then self.unset
        else self.setCurrentValue(())
    if init then setCurrentValue(()) else disable.setCurrentValue(())
  
  val global = NullaryCommand("global")
  global.setCurrentValue(()) // * Starts enabled at the top of the file
  
  val fixme = Command("fixme")(_ => ())
  val todo = Command("todo")(_ => ())
  def tolerateErrors = fixme.isSet || todo.isSet
  
  val fullExceptionStack = NullaryCommand("s")
  
  val debug = NullaryCommand("d")
  
  val expectParseErrors = NullaryCommand("pe")
  val expectTypeErrors = NullaryCommand("e")
  val expectRuntimeErrors = NullaryCommand("re")
  val expectCodeGenErrors = NullaryCommand("ge")
  val allowRuntimeErrors = NullaryCommand("allowRuntimeErrors")
  val expectWarnings = NullaryCommand("w")
  val showRelativeLineNums = NullaryCommand("showRelativeLineNums")
  
  
  val tests = Command("tests"):
    case "" =>
      new DiffTestRunner(new DiffTestRunner.State).execute()
  
  
  val fileName = file.last
  
  val fileContents = os.read(file)
  val allLines = fileContents.splitSane('\n').toList
  val strw = new java.io.StringWriter
  val out = new java.io.PrintWriter(strw)
  val output = Outputter(out)
  val report = ReportFormatter(output.apply)
  
  val failures = mutable.Buffer.empty[Int]
  val unmergedChanges = mutable.Buffer.empty[Int]
  
  var _onlyParse = false
  var _allowTypeErrors = false
  var _showRelativeLineNums = false
  
  
  
  def processBlock(origin: Origin): Unit =
    val globalStartLineNum = origin.startLineNum
    val blockLineNum = origin.startLineNum
    // * ^ In previous DiffTest versions, these two could be different due to relative line numbers
    
    var parseErrors, typeErrors, compilationErrors, runtimeErrors, warnings = 0
    
    val raise: Raise = d =>
      d.kind match
      case Diagnostic.Kind.Error =>
        d.source match
        case Diagnostic.Source.Lexing =>
          parseErrors += 1
          if expectParseErrors.isUnset && !tolerateErrors then
            failures += globalStartLineNum
            unexpected("lexing error", blockLineNum)
        case Diagnostic.Source.Parsing =>
          parseErrors += 1
          if expectParseErrors.isUnset && !tolerateErrors then
            failures += globalStartLineNum
            // doFail(fileName, blockLineNum, "unexpected parse error at ")
            unexpected("parse error", blockLineNum)
            // report(blockLineNum, d :: Nil, showRelativeLineNums.isSet)
        case Diagnostic.Source.Typing =>
          typeErrors += 1
          if expectTypeErrors.isUnset && !tolerateErrors then
            failures += globalStartLineNum
            unexpected("type error", blockLineNum)
        case Diagnostic.Source.Compilation =>
          compilationErrors += 1
          if expectCodeGenErrors.isUnset && !tolerateErrors then
            failures += globalStartLineNum
            unexpected("runtime error", blockLineNum)
        case Diagnostic.Source.Runtime =>
          runtimeErrors += 1
          if expectRuntimeErrors.isUnset && !tolerateErrors then
            failures += globalStartLineNum
            unexpected("runtime error", blockLineNum)
      case Diagnostic.Kind.Warning =>
        warnings += 1
        if expectWarnings.isUnset && !tolerateErrors then
          failures += globalStartLineNum
          unexpected("warning", blockLineNum)
      case Diagnostic.Kind.Internal =>
        failures += globalStartLineNum
        unexpected("internal error", blockLineNum)
      report(blockLineNum, d :: Nil, showRelativeLineNums.isSet)
    
    processOrigin(origin)(using raise)
    
    // Note: when `todo` is set, we allow the lack of errors.
    // Use `todo` when the errors are expected but not yet implemented.
    if expectParseErrors.isSet && parseErrors == 0 && todo.isUnset then
      failures += globalStartLineNum
      unexpected("lack of parse error", blockLineNum)
    if expectTypeErrors.isSet && typeErrors == 0 && todo.isUnset then
      failures += globalStartLineNum
      unexpected("lack of type error", blockLineNum)
    if expectRuntimeErrors.isSet && runtimeErrors == 0 && todo.isUnset then
      failures += globalStartLineNum
      unexpected("lack of runtime error", blockLineNum)
    if expectWarnings.isSet && warnings == 0 && todo.isUnset then
      failures += globalStartLineNum
      unexpected("lack of warnings", blockLineNum)
    
    if fixme.isSet && (parseErrors + typeErrors + compilationErrors + runtimeErrors) == 0 then
      failures += globalStartLineNum
      unexpected("lack of error to fix", blockLineNum)
  
  
  
  @annotation.tailrec
  final def rec(lines: List[String]): Unit = lines match
    case "" :: Nil => // To prevent adding an extra newline at the end
    case (line @ "") :: ls =>
      out.println(line)
      resetCommands
      rec(ls)
    case ":exit" :: ls =>
      out.println(":exit")
      out.println(output.exitMarker)
      ls.dropWhile(_ =:= output.exitMarker).tails.foreach {
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
          cmd.setCurrentValue(cmd.process(rest))
        case N =>
          failures += allLines.size - lines.size + 1
          output("/!\\ Unrecognized command: " + cmd)
      
      rec(ls)
    case line :: ls if line.startsWith(output.outputMarker) //|| line.startsWith(oldOutputMarker)
      => rec(ls)
    case line :: ls if line.startsWith("//") =>
      out.println(line)
      rec(ls)
    case line :: ls if line.startsWith(output.diffBegMarker) => // Check if there are unmerged git conflicts
      val diff = ls.takeWhile(l => !l.startsWith(output.diffEndMarker))
      assert(diff.exists(_.startsWith(output.diffMidMarker)), diff)
      val rest = ls.drop(diff.length)
      val hdo = rest.headOption
      assert(hdo.exists(_.startsWith(output.diffEndMarker)), hdo)
      val blankLines = diff.count(_.isEmpty)
      val hasBlankLines = diff.exists(_.isEmpty)
      if diff.forall(l => l.startsWith(output.outputMarker) || l.startsWith(output.diffMidMarker) || l.startsWith(output.diff3MidMarker) || l.isEmpty) then {
        for _ <- 1 to blankLines do out.println()
      } else {
        unmergedChanges += allLines.size - lines.size + 1
        out.println(output.diffBegMarker)
        diff.foreach(out.println)
        out.println(output.diffEndMarker)
      }
      if hasBlankLines then resetCommands
      rec(rest.tail)
    case l :: ls =>
      
      val blockLineNum = allLines.size - lines.size + 1
      
      val block = (l :: ls.takeWhile(l => l.nonEmpty && !(
        l.startsWith(output.outputMarker)
        || l.startsWith(output.diffBegMarker)
        // || l.startsWith(oldOutputMarker)
      ))).toIndexedSeq
      block.foreach(out.println)
      val processedBlock = block
      val processedBlockStr = processedBlock.mkString
      val fph = new FastParseHelpers(block)
      
      val origin = Origin(fileName, blockLineNum, fph)
      
      try
        
        processBlock(origin)
        
      catch
        case oh_noes: ThreadDeath => throw oh_noes
        case err: Throwable =>
          if !tolerateErrors then
            failures += allLines.size - lines.size + 1
            unhandled(blockLineNum, err)
          // err.printStackTrace(out)
          // println(err.getCause())
          output("/!!!\\ Uncaught error: " + err +
            err.getStackTrace().take(
              if fullExceptionStack.isSet || debug.isSet then Int.MaxValue
              else if tolerateErrors || err.isInstanceOf[StackOverflowError] then 0
              else 10
            ).map("\n" + "\tat: " + _).mkString)
      
      rec(lines.drop(block.size))
      
    case Nil =>
  
  
  
  def run(): Unit =
    try rec(allLines) finally out.close()
    val result = strw.toString
    if result =/= fileContents then
      println(s"Updating $file...")
      os.write.over(file, result)
  
  
  
end DiffMaker


