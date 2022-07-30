package mlscript

import mlscript.utils.shorthands._

/**
 * Helper to run NodeJS on test input.
 */
final case class ReplHost() {
  import java.io.{BufferedWriter, BufferedReader, InputStreamReader, OutputStreamWriter}
  private val builder = new java.lang.ProcessBuilder()
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
    * @param code
    * @param useEval whether warp
    */
  private def send(code: Str, useEval: Bool = false): Unit = {
    stdin.write(
      if (useEval) "eval(" + JSLit.makeStringLiteral(code) + ")\n"
      else if (code endsWith "\n") code
      else code + "\n"
    )
    stdin.flush()
  }

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
        send(if (res == "res") res else s"globalThis[\"${res}\"]")
        parseQueryResult().map { result =>
          ReplHost.Result(result, Some(intermediate))
        }
      }
    }
  }

  def execute(code: Str): ReplHost.Reply = {
    send(code)
    collectUntilPrompt()
  }

  def terminate(): Unit = proc.destroy()
}

object ReplHost {

  /**
    * The syntax error beginning text.
    */
  private val syntaxErrorHead = "Uncaught SyntaxError: "

  /**
    * The base class of all kinds of REPL replies.
    */
  sealed abstract class Reply {

    /**
      * Maps the successfuly part.
      *
      * @param f the function over
      * @return
      */
    def map(f: Str => Reply): Reply
  }

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
    */
  final case class Unexecuted(message: Str) extends Reply {
    override def map(f: Str => Reply): Reply = this
    override def toString(): Str = s"[unexecuted] $message"
  }

  /**
    * If the `ReplHost` captured errors, it will response with `Error`.
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
