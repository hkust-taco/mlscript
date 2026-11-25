package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import semantics.{ClassSymbol, TopLevelSymbol}
import semantics.Elaborator.State
import syntax.Tree
import utils.*, shorthands.*


/** Valid source programs cannot request an unbound IR receiver. Exercise this backend
  * boundary directly so optimizer checks cannot hide a fallback to the global object.
  */
class ReceiverScopeTest extends AnyFunSuite:
  test("unbound class receivers are rejected in global and nested scopes"):
    given State = new State
    given Raise = diagnostic => throw diagnostic
    val missing = ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident("Owner"))
    val other = ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident("Owner"))
    val root = Scope.empty(Scope.Cfg.default)
    for scope <- List(root, root.nest) do
      intercept[InternalError](scope.findThis_!(missing))
    root.nestRebindThis(N):
      intercept[InternalError](summon[Scope].findThis_!(missing))
    root.nestRebindThis(S(other)):
      intercept[InternalError](summon[Scope].findThis_!(missing))

  test("top-level receivers denote the global object even inside classes and functions"):
    given State = new State
    given Raise = diagnostic => throw diagnostic
    val owner = ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident("Owner"))
    val root = Scope.empty(Scope.Cfg.default)
    for global <- List(State.globalThisSymbol, TopLevelSymbol("another compilation unit")) do
      assert(root.findThis_!(global) == "globalThis")
      root.nestRebindThis(S(owner)):
        assert(summon[Scope].findThis_!(global) == "globalThis")
        summon[Scope].nestRebindThis(N):
          assert(summon[Scope].findThis_!(global) == "globalThis")

  test("bound receivers retain their identity across scopes that rebind JavaScript this"):
    given State = new State
    given Raise = diagnostic => throw diagnostic
    val owner = ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident("Owner"))
    val root = Scope.empty(Scope.Cfg.default)
    root.nestRebindThis(S(owner)):
      val ownScope = summon[Scope]
      assert(ownScope.findThis_!(owner) == "this")
      assert(ownScope.nest.findThis_!(owner) == "this")
      ownScope.nestRebindThis(N):
        val captured = summon[Scope].findThis_!(owner)
        assert(captured != "this" && captured != "globalThis")
        assert(summon[Scope].nest.findThis_!(owner) == captured)
