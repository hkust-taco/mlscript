package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.codegen.ErasedType
import hkmc2.semantics.{Elaborator, TermSymbol, VarSymbol}
import hkmc2.syntax.{Fun, Tree}
import hkmc2.utils.*, shorthands.*


class ErasureTest extends AnyFunSuite:
  test("parameter type reads fail before erasure without caching an unknown representation"):
    given Elaborator.State = new Elaborator.State
    val parameter = VarSymbol(Tree.Ident("parameter"))
    intercept[AssertionError](parameter.erasedType)
    intercept[AssertionError](parameter.erasedValueType)
    intercept[AssertionError](parameter.erasedValueType_!)
    intercept[AssertionError](parameter.erasedType_!)
    parameter.erasedType = S(ErasedType.Primitive(codegen.PrimitiveType.Int32))
    assert(parameter.erasedValueType == parameter.erasedType)
    assert(parameter.erasedValueType_! == ErasedType.Primitive(codegen.PrimitiveType.Int32))
    assert(parameter.erasedType_! == parameter.erasedValueType_!)
    intercept[AssertionError](parameter.erasedType = N)

  test("an unknown representation is initialized and cannot be initialized twice"):
    given Elaborator.State = new Elaborator.State
    val parameter = VarSymbol(Tree.Ident("unannotated"))
    parameter.erasedType = N
    assert(parameter.isErased)
    assert(parameter.erasedValueType.isEmpty)
    assert(parameter.erasedValueType_! == ErasedType.Unknown)
    intercept[AssertionError](parameter.erasedType = S(ErasedType.Unknown))

  test("definition result types cannot be read before erasure"):
    given Elaborator.State = new Elaborator.State
    val definition = TermSymbol(Fun, N, Tree.Ident("function"))
    intercept[AssertionError](definition.declaredResultType)
    definition.erasedType = S(ErasedType.FuncRef(S(false), Nil :: Nil, S(ErasedType.Unknown)))
    assert(definition.declaredResultType.contains(ErasedType.Unknown))
