package simplesub

import fastparse._
import Parser.expr
import fastparse.Parsed.Failure
import fastparse.Parsed.Success

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class TypingTests extends TypingTester {
  
  // In the tests, leave the expected string empty so the inferred type is printed in the console
  // and you can copy and paste it after making sure it is correct.
  
  test("basic") {
    doTest("42", "Int")
    doTest("fun x -> 42", "⊤ -> Int")
    doTest("fun x -> x", "'a -> 'a")
    doTest("fun x -> x 42", "(Int -> 'a) -> 'a")
    doTest("(fun x -> x) 42", "Int")
    doTest("fun f -> fun x -> f (f x)  // twice", "('a -> 'a ∧ 'b) -> 'a -> 'b")
  }
  
  test("booleans") {
    doTest("true", "Bool")
    doTest("not true", "Bool")
    doTest("fun x -> not x", "Bool -> Bool")
    doTest("(fun x -> not x) true", "Bool")
    doTest("fun x -> fun y -> fun z -> if x then y else z",
      "Bool -> 'a -> 'a -> 'a")
    doTest("fun x -> fun y -> if x then y else x",
      "'a ∧ Bool -> 'a -> 'a")
    
    error("succ true",
      "cannot constrain Bool <: Int")
    error("fun x -> succ (not x)",
      "cannot constrain Bool <: Int")
    error("(fun x -> not x.f) { f = 123 }",
      "cannot constrain Int <: Bool")
    error("(fun f -> fun x -> not (f x.u)) false",
      "cannot constrain Bool <: 'a -> 'b")
  }
  
  test("records") {
    doTest("fun x -> x.f", "{f: 'a} -> 'a")
    doTest("{}", "⊤")
    doTest("{ f = 42 }", "{f: Int}")
    doTest("{ f = 42 }.f", "Int")
    doTest("(fun x -> x.f) { f = 42 }", "Int")
    doTest("fun f -> { x = f 42 }.x", "(Int -> 'a) -> 'a")
    doTest("fun f -> { x = f 42; y = 123 }.y", "(Int -> ⊤) -> Int")
    doTest("if true then { a = 1; b = true } else { b = false; c = 42 }", "{b: Bool}")
    
    error("{ a = 123; b = true }.c",
      "missing field: c in {a: Int, b: Bool}")
    error("fun x -> { a = x }.b",
      "missing field: b in {a: 'a}")
  }
  
  test("self-app") {
    doTest("fun x -> x x", "('a -> 'b) as 'a -> 'b")
    // ^ see the note in the App case: with an intermediate variable we get ('a ∧ ('a -> 'b)) -> 'b
    
    doTest("fun x -> x x x", "('a -> 'a -> 'b) as 'a -> 'b")
    doTest("fun x -> fun y -> x y x", "('b -> 'a -> 'c) as 'a -> 'b -> 'c")
    doTest("fun x -> fun y -> x x y", "('a -> 'b -> 'c) as 'a -> 'b -> 'c")
    doTest("(fun x -> x x) (fun x -> x x)", "⊥")
    
    doTest("fun x -> {l = x x; r = x }",
      "('a -> 'b) as 'a -> {l: 'b, r: 'a}")
    // ^ notice this case of a recursive alias that is mentioned later in the type
    
    // From https://github.com/stedolan/mlsub
    // Y combinator:
    doTest("(fun f -> (fun x -> f (x x)) (fun x -> f (x x)))",
      "('a -> 'a) -> 'a")
    // Z combinator:
    doTest("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)))",
      "(('a -> 'b) -> 'c ∧ ('a -> 'b)) -> 'c")
    // Function that takes arbitrarily many arguments:
    doTest("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v))) (fun f -> fun x -> f)",
      "⊤ -> ⊤ -> (⊤ -> ('a ∨ (⊤ -> 'a ∨ 'b)) as 'b) as 'a")
  }
  
  test("let-poly") {
    doTest("let f = fun x -> x in {a = f 0; b = f true}", "{a: Int, b: Bool}")
    doTest("fun y -> let f = fun x -> x in {a = f y; b = f true}",
      "'a -> {a: 'a, b: Bool}")
    doTest("fun y -> let f = fun x -> y x in {a = f 0; b = f true}",
      "(Int ∨ Bool -> 'a) -> {a: 'a, b: 'a}")
    doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> true)}",
      "'a -> {a: 'a, b: Bool}")
    doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> succ z)}",
      "'a ∧ Int -> {a: 'a, b: Int}")
  }
  
  test("recursion") {
    doTest("let rec f = fun x -> f x.u in f",
      "{u: 'a} as 'a -> ⊥")
    
    // from https://www.cl.cam.ac.uk/~sd601/mlsub/
    doTest("let rec recursive_monster = fun x -> { thing = x; self = recursive_monster x } in recursive_monster",
      "'a -> {self: {self: 'b, thing: 'a} as 'b, thing: 'a}")
    // ^ Note: with an intermediate variable in the App case, we get this weird (but seemingly correct) type:
    //      "⊤ as 'a -> {self: {self: 'b, thing: 'a} as 'b, thing: 'a}";
    //    This happens because we have ?a <: ?c and ?c <: ?a (where ?c does not appear anywhere else),
    //    and the expansion algorithm does not detect that ?a is only spuriously recursive.
  }
  
}
