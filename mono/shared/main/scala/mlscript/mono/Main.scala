package mlscript.mono

import mlscript.Pgrm
import mlscript.TypingUnit
import mlscript.Term
import mlscript.TypeDef
import mlscript.Def
import mlscript.{NuDecl, NuFunDef, NuTypeDef}
import fastparse.parse
import fastparse.Parsed.{Failure, Success}
import mlscript.NewLexer
import mlscript.NewParser
import mlscript.Origin
import mlscript.PolyType
import mlscript.{Lam, Tup, Var}
import collection.mutable.Map as MutMap
import mlscript.Cls
import mlscript.New
import mlscript.Trt
import mlscript.{Diagnostic, Warning, CompilationError}
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.mono.debug.RainbowDebug

@main
def main(): Unit =
  val source = """
    |class Node() {}
    |class Literal(#value): Node {
    |  fun compute() = value
    |}
    |class Add(#x, y): Node {
    |  fun compute() = x.compute() + y.compute()
    |}
    |class Sub(#x, y): Node {
    |  fun compute() = x.compute() - y.compute()
    |}
    |let add = Add(1, 2)
    |add.compute()""".stripMargin
  val fastParseHelpers = mlscript.FastParseHelpers(source)
  val origin = mlscript.Origin("test.mls", 1, fastParseHelpers)
  val raise = (t: Diagnostic) => t match
    case Warning(mainMsg, _) =>
      println(Console.YELLOW + "[parser]" + Console.RESET + " " + mainMsg)
    case CompilationError(mainMsg, _) =>
      println(Console.RED + "[parser]" + Console.RESET + " " + mainMsg)
  val lexer = new NewLexer(origin, raise, false)
  val tokens = lexer.tokens
  val parser = new NewParser(origin, tokens, raise, false) {
    def printDbg(msg: => Any): Unit =
      println(Console.GREEN + "[parser]" + Console.RESET + " " + msg)
  }
  val typingUnit = parser.parseAll(parser.typingUnit)
  println(showStructure(typingUnit))
  val monomorph = new Monomorph(RainbowDebug())
  val monomorphized = monomorph.monomorphize(typingUnit)
  println("Successfully monomorphized the program.")
