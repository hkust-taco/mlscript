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
import mlscript.New.apply
import mlscript.Trt

@main
def main(): Unit =
  val source = """
def inc x = x + 1
def dbl x = x * 2
def app f x = f x

class Box[T]: { inner: T }
  method Map: (T -> 'a) -> Box['a]
  method Map f = Box { inner = f this.inner }
  method Get = this.inner

class Stop: {}

Box { inner = 4 * 5 }

def box0 = Box { inner = 0 }
def box1 = box0.Map inc
def box2 = box1.Map dbl
  """
  val fastParseHelpers = mlscript.FastParseHelpers(source)
  val origin = mlscript.Origin("test.mls", 1, fastParseHelpers)
  val raise = (t: Any) => ()
  val lexer = new NewLexer(origin, raise, false)
  val tokens = lexer.tokens
  val parser = new NewParser(origin, tokens, raise, false) {
    def printDbg(msg: => Any): Unit = ()
  }
  val typingUnit = parser.parseAll(parser.typingUnit)
  val monomorphized = Monomorph.monomprphize(typingUnit)
  println("Successfully monomorphized the program.")
  println("Specialized type definitions:")
  Monomorph.specializedTypeDefs.foreach { case tyDef =>
    println(PrettyPrinter.show(tyDef))
  }
