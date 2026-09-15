package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import codegen.*
import semantics.{NoSymbol, PlainParamList}
import syntax.Tree.IntLit


class BlockReturnTypeTest extends AnyFunSuite:
  test("a block without returns differs from one returning an untyped value"):
    val lambda = Lambda(PlainParamList(Nil), Return(Value.Lit(IntLit(1))))(Nil)
    assert(new Assign(NoSymbol, lambda, End()).returnType.isEmpty)
    assert(Return(lambda).returnType.contains(ErasedType.Unknown))

  test("returns in lambda bodies do not contribute to the enclosing block"):
    val value = Value.Lit(IntLit(1))
    val lambda = Lambda(PlainParamList(Nil), Return(Tuple(false, Nil)))(Nil)
    val block = new Assign(NoSymbol, lambda, Return(value))
    assert(block.returnType.contains(value.erasedValueType_!))

  test("returns in finalizers and unreachable continuations still contribute"):
    val first = Value.Lit(IntLit(1))
    val second = Tuple(false, Nil)
    val block = TryBlock(Return(first), Return(second), End())
    assert(block.returnType.contains(ErasedType.Union(List(first.erasedValueType_!, second.erasedValueType_!))))
    // Bypass Begin's simplifying constructor so the unreachable continuation remains in the IR.
    assert(new Begin(Return(first), Return(second)).returnType == block.returnType)
