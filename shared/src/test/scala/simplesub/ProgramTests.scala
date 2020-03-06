package simplesub

import org.scalatest._
import fastparse._
import Parser.pgrm
import fastparse.Parsed.Failure
import fastparse.Parsed.Success
import sourcecode.Line

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class ProgramTests extends FunSuite {
  
  implicit class ExpectedStr(val str: String)(implicit val line: Line)
  
  def doTest(str: String)(expected: ExpectedStr*): Unit = {
    val Success(p, index) = parse(str, pgrm(_), verboseFailures = true)
    val typing = new Typer
    val tys = typing.inferTypes(p)
    (p.defs lazyZip tys lazyZip expected).foreach { (str, ty, exp) =>
      if (exp.str.isEmpty) println(s">>> $str")
      val tyv = ty.instantiate(0)
      val res = typing.expandPosType(tyv, true).simplify.show
      if (exp.str.nonEmpty) { assert(res == exp.str, "at line " + exp.line.value); () }
      else {
        println("inferred: " + tyv)
        println(" where " + tyv.showBounds)
        println(res)
        println("---")
      }
    }
    assert(tys.size == expected.size)
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
      "('a -> 'a ∧ 'b) -> 'a -> 'b",
      "{x: Int, y: 'a -> 'a}",
      "{x: Int, y: Bool}",
      "Bool -> {x: Int, y: Bool ∨ ('a -> 'a)}",
      "'a -> {self: 'b, thing: 'a} as 'b",
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
  
  test("rec-producer-consumer") {
    doTest("""
      let rec produce = fun arg -> { head = arg; tail = produce (succ arg) }
      let rec consume = fun strm -> add strm.head (consume strm.tail)
      
      let codata = produce 42
      let res = consume codata
      
      let rec codata2 = { head = 0; tail = { head = 1; tail = codata2 } }
      let res = consume codata2
      
      let rec produce3 = fun b -> { head = 123; tail = if b then codata else codata2 }
      let res = fun x -> consume (produce3 x)
      
      let consume2 =
        let rec go = fun strm -> add strm.head (add strm.tail.head (go strm.tail.tail))
        in fun strm -> add strm.head (go strm.tail)
        // in go
      // let rec consume2 = fun strm -> add strm.head (add strm.tail.head (consume2 strm.tail.tail))
      let res = consume2 codata2
    """)(
      "Int -> {head: Int, tail: 'a} as 'a",
      "{head: Int, tail: 'a} as 'a -> Int",
      "{head: Int, tail: 'a} as 'a",
      "Int",
      "{head: Int, tail: {head: Int, tail: 'a}} as 'a",
      "Int",
      "Bool -> {head: Int, tail: {head: Int, tail: {head: Int, tail: 'a} ∨ 'a} as 'a}",
      "Bool -> Int",
      "{head: Int, tail: {head: Int, tail: {head: Int, tail: 'a}} as 'a} -> Int",
      "Int",
    )
  }
  
}
