package simplesub

import org.scalatest._
import fastparse._
import Parser.pgrm
import fastparse.Parsed.Failure
import fastparse.Parsed.Success

class ProgramTests extends FunSuite {
  
  def doTest(str: String)(expected: String*): Unit = {
    val Success(p, index) = parse(str, pgrm(_), verboseFailures = true)
    val typing = new Typing
    val tys = typing.inferTypes(p)
    (p.defs lazyZip tys lazyZip expected).foreach { (str, ty, exp) =>
      if (exp.isEmpty) println(s">>> $str")
      val res = typing.expandPosType(ty.instantiate(0), true).show
      if (exp.nonEmpty) { assert(res =:= exp); () }
      else {
        println(res)
        println("---")
      }
    }
    assert(tys.size =:= expected.size)
    ()
  }
  
  test("mlsub") { // from https://www.cl.cam.ac.uk/~sd601/mlsub/
    doTest("""
      let id = fun x -> x
      let twice = fun f -> fun x -> f (f x)
      let object1 = { x = 42; y = id }
      let object2 = { x = 17; y = false }
      let pick_an_object = fun b ->
        if b then object1 else object2
      let rec recursive_monster = fun x ->
        { thing = x;
          self = recursive_monster x }
    """)(
      "'a -> 'a",
      "('a ∨ 'b -> 'a ∧ 'c) -> 'b -> 'c",
      "{x: Int, y: 'a -> 'a}",
      "{x: Int, y: Bool}",
      "Bool -> {x: Int, y: Bool ∨ 'a -> 'a}",
      "'a -> {self: {self: b, thing: 'a} as b, thing: 'a}",
    )
  }
  
  test("top-level-polymorphism") {
    doTest("""
      let id = fun x -> x
      let ab = {u = id 0; v = id true}
    """)(
      "'a -> 'a",
      "{u: Int, v: Bool}",
    )
  }
  
}
