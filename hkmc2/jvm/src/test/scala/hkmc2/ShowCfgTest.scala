package hkmc2
package semantics

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*, shorthands.*
import syntax.Tree


/** Diff tests check printed output, but cannot observe whether debug rendering retains
  * symbols and their owner states from unrelated compilations.
  */
class ShowCfgTest extends AnyFunSuite:
  test("independent internal displays keep symbol tracking isolated and bounded"):
    val unusedDisplay = ShowCfg.internal
    for index <- 0 until 64 do
      given Elaborator.State = new Elaborator.State
      given Scope = Scope.empty(Scope.Cfg.default)
      given Raise = diagnostic => fail(diagnostic.theMsg)
      val display = ShowCfg.internal
      val symbol = VarSymbol(Tree.Ident(s"item$index"), mut = false)

      symbol.showName(using summon[Scope], display)
      assert(display.shownSymbols.size == 1)
      assert(display.shownSymbols.contains(symbol))
      assert(unusedDisplay.shownSymbols.isEmpty)
