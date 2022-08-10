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

@main
def main(): Unit =
  val source = """
    |class Option {
    |  fun map(f: int): int
    |}
    |class Some(#value): Option {
    |  fun map(f) = f(value)
    |}
    |class None: Option {
    |  fun map(f) = ()
    |}
    |fun process(maybeInt) =
    |  maybeInt.map(fun (x) => x + 2)
    |process(None)
    |process(Some(0))""".stripMargin
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
  val monomorph = new Monomorph(true)
  val monomorphized = monomorph.monomorphize(typingUnit)
  println("Successfully monomorphized the program.")
