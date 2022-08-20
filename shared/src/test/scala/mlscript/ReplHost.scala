package mlscript

import mlscript.utils.shorthands._

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

  /**
   * This function simply collect output from Node.js until meet `"\n> "`.
   * It is useful to skip the welcome message and collect REPL reply from
   * interactive Node.js. It also filters out syntax errors.
   * 
   * @return when there are syntax errors, returns `Error` where `syntax` is 
   *         `true`; otherwise, returns `Result`
   */
  private def collectUntilPrompt(): ReplHost.Reply = {
    val buffer = new StringBuilder()
    while (!buffer.endsWith("\n> ")) {
      buffer.append(stdout.read().toChar)
    }
    // Remove the trailing `"\n> "`
    buffer.delete(buffer.length - 3, buffer.length)
    val reply = buffer.toString()
    reply.linesIterator.find(_.startsWith(ReplHost.syntaxErrorHead)) match {
      case None => ReplHost.Result(reply, None)
      case Some(syntaxErrorLine) =>
        val message = syntaxErrorLine.substring(ReplHost.syntaxErrorHead.length)
        ReplHost.Error(true, message)
    }
  }

  /**
   * Parse query results from collected output from Node.js.
   * 
   * - If there is line begins with `"Uncaught SyntaxError: "`, returns
   *   the syntax error indicated in that line.
   * - If character `0x200B` presents in the output, returns the trimmed
   *   error message.
   * - Otherwise, returns the result as a successfully reply.
   */
  private def parseQueryResult(): ReplHost.Reply = {
    collectUntilPrompt().map { reply =>
      // Find error boundaries.
      val begin = reply.indexOf(0x200b)
      val end = reply.lastIndexOf(0x200b)
      // If there is an error, returns `ReplHost.Error`.
      if (begin >= 0 && end >= 0)
        // `console.log` inserts a space between every two arguments,
        // so + 1 and - 1 is necessary to get correct length.
        ReplHost.Error(false, reply.substring(begin + 1, end))
      else
        ReplHost.Result(reply, None)
    }
  }

  /**
    * Send code to Node.js process.
    *
    * @param code the code to execute
    */
  private def send(code: Str): Unit = {
    stdin.write(if (code endsWith "\n") code else code + "\n")
    stdin.flush()
  }

  /**
    * Send code to the Node.js process.
    *
    * @param prelude the prelude code
    * @param code the main code
    * @param res the result identifier name
    * @return
    */
  def query(prelude: Str, code: Str, res: Str): ReplHost.Reply = {
    // For empty queries, returns empty.
    if (prelude.isEmpty && code.isEmpty)
      ReplHost.Empty
    else {
      // Warp the code with `try`-`catch` block.
      val wrapped = s"$prelude try { $code } catch (e) { console.log('\\u200B' + e + '\\u200B'); }"
      // Send the code
      send(wrapped)
      // If succeed, retrieve the result.
      parseQueryResult().map { intermediate =>
        // Since the result might not be the result of the expression, we need
        // to retrieve the value again.
        send(res match {
          case "res" => res
          case _     => s"globalThis[\"${res}\"]"
        })
        parseQueryResult().map { result =>
          // Add the intermediate result to the reply.
          ReplHost.Result(result, Some(intermediate))
        }
      }
    }
  }

  /**
    * Execute class and function declarations.
    *
    * @param code the code to execute
    * @return
    */
  def execute(code: Str): ReplHost.Reply = {
    send(code)
    collectUntilPrompt()
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
    override def toString(): Str = s"[success] $content"
  }

  /**
    * If the query is `Empty`, we will receive this.
    */
  final object Empty extends Reply {
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
      if (syntax)
        s"[syntax error] $message"
      else
        s"[runtime error] $message"
  }
}
