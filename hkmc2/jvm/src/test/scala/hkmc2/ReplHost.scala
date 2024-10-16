package hkmc2

import mlscript.utils.*, shorthands.*

/**
 * A helper class to manipulate an interactive Node.js process.
 */
final case class ReplHost() {
  import java.io.{BufferedWriter, BufferedReader, InputStreamReader, OutputStreamWriter}
  private val builder = new java.lang.ProcessBuilder()
  // `--interactive` always enters the REPL even if stdin is not a terminal
  builder.command("node", "--interactive")
  private val proc = builder.start()

  private val stdin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream))
  private val stdout = new BufferedReader(new InputStreamReader(proc.getInputStream))
  private val stderr = new BufferedReader(new InputStreamReader(proc.getErrorStream))

  // Skip the welcome message.
  collectUntilPrompt()
  execute("console.info = console.error")

  /**
   * This function simply collects output from Node.js until meeting `"\n> "`.
   * It is useful to skip the welcome message and collect REPL reply from
   * interactive Node.js. It also filters out syntax errors.
   * 
   * @return when there are syntax errors, returns `Error` where `syntax` is 
   *         `true`; otherwise, returns the result
   */
  private def collectUntilPrompt(): ReplHost.Error | Str = {
    val buffer = new StringBuilder()
    while !buffer.endsWith("\n> ") do {
      val c = stdout.read()
      if c === -1 then lastWords(s"ReplHost could not read more from NodeJS stdout.")
      buffer.append(c.toChar)
    }
    // Remove the trailing `"\n> "`
    buffer.delete(buffer.length - 3, buffer.length)
    val reply = buffer.toString()
    reply.linesIterator.find(_.startsWith(ReplHost.syntaxErrorHead)) match {
      case None => reply.linesIterator.find(_.startsWith(ReplHost.uncaughtErrorHead)) match {
        case None => reply
        case Some(uncaughtErrorLine) => {
          val message = uncaughtErrorLine.substring(ReplHost.uncaughtErrorHead.length)
          ReplHost.Error(false, message)
        }
      }
      case Some(syntaxErrorLine) =>
        val message = syntaxErrorLine.substring(ReplHost.syntaxErrorHead.length)
        ReplHost.Error(true, message)
    }
  }

  private def consumeStderr(): String = {
    val buffer = new StringBuilder()
    while stderr.ready() do
      buffer.append(stderr.read().toChar)
    buffer.toString()
  }

  /**
   * Parse query results from collected output from Node.js.
   * 
   * - If there is a line begining with `"Uncaught SyntaxError: "`,
   *    return the syntax error indicated in that line.
   * - If character `0x200B` presents in the output,
   *    return the trimmed error message.
   * - Otherwise, returns the result string.
   */
  private def parseQueryResult(): ReplHost.Error | Str =
    collectUntilPrompt() match
    case reply: Str =>
      // Find error boundaries.
      val begin = reply.indexOf(0x200b)
      val end = reply.lastIndexOf(0x200b)
      // If there is an error, returns `ReplHost.Error`.
      if begin >= 0 && end >= 0 then
        // `console.log` inserts a space between every two arguments,
        // so + 1 and - 1 is necessary to get correct length.
        ReplHost.Error(false, reply.substring(begin + 1, end))
      else reply
    case error: ReplHost.Error => error
  
  /**
    * Send code to Node.js process.
    *
    * @param code the code to execute
    */
  private def send(code: Str): Unit = {
    stdin.write(if code.endsWith("\n") then code else code + "\n")
    stdin.flush()
  }

  /**
    * Send code to the Node.js process.
    *
    * @param prelude the prelude code
    * @param code the main code
    * @param res the result identifier name
    * @return reply string and stderr string
    */
  def query(prelude: Str, code: Str, res: Str): (ReplHost.Reply, Str) =
    // For empty queries, returns empty.
    if prelude.isEmpty && code.isEmpty then
      (ReplHost.Empty, "")
    else
      // Wrap the code with `try`-`catch` block.
      val wrapped =
        s"$prelude try { $code } catch (e) { console.log('\\u200B' + e + '\\u200B'); }"
      // Send the code
      send(wrapped)
      (parseQueryResult() match
        case intermediate: Str =>
          // Since the result might not be the result of the expression, we need
          // to retrieve the value again.
          send(s"globalThis[\"${res}\"]")
          parseQueryResult() match
          case result: Str =>
            // Add the intermediate result to the reply.
            ReplHost.Result(result, Some(intermediate))
          case error: ReplHost.Error => error
        case error: ReplHost.Error => error
      , consumeStderr())
  
  /**
    * Execute class and function declarations.
    *
    * @param code the code to execute
    * @return
    */
  def execute(code: Str): ReplHost.Reply = {
    send(code)
    collectUntilPrompt() match
    case res: Str => ReplHost.Result(res, None)
    case error: ReplHost.Error => error
  }

  /**
    * Kills the Node.js process.
    */
  def terminate(): Unit = proc.destroy()
}

object ReplHost {

  /**
    * The syntax error beginning text from Node.js.
    */
  private val syntaxErrorHead = "Uncaught SyntaxError: "
  private val uncaughtErrorHead = "Uncaught "

  /**
    * The base class of all kinds of REPL replies.
    */
  sealed abstract class Reply {

    /**
      * Maps the successful part. Like `Option[T].map`.
      *
      * @param f the function over
      * @return
      */
    def map(f: Str => Reply): Reply
  }

  /**
    * Represents a successful reply from Node.js.
    *
    * @param content the reply content, i.e. the final result
    * @param intermediate the intermediate evaluation results
    */
  final case class Result(content: Str, intermediate: Opt[Str]) extends Reply {
    override def map(f: Str => Reply): Reply = f(content)
    override def toString(): Str = s"[success] $content${
      intermediate match
        case None | Some("") => s""
        case Some(str) => s" (with output)"
    }"
  }

  /**
    * If the query is `Empty`, we will receive this.
    */
  object Empty extends Reply {
    override def map(f: Str => Reply): Reply = this
    override def toString(): Str = "[empty]"
  }

  /**
    * If the query is `Unexecuted`, we will receive this.
    * @param message the error message
    */
  final case class Unexecuted(message: Str) extends Reply {
    override def map(f: Str => Reply): Reply = this
    override def toString(): Str = s"[unexecuted] $message"
  }

  /**
    * If the `ReplHost` captured errors, it will response with `Error`.
    * @param syntax if `true`, this is a syntax error; otherwise, this is a
    *               runtime error
    * @param message the error message
    */
  final case class Error(syntax: Bool, message: Str) extends Reply {
    override def map(f: Str => Reply): Reply = this
    override def toString(): Str =
      if syntax then
        s"[syntax error] $message"
      else
        s"[runtime error] $message"
  }
}
