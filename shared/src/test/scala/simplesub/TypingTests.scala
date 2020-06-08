package simplesub

import fastparse._
import Parser.expr
import fastparse.Parsed.Failure
import fastparse.Parsed.Success

@SuppressWarnings(Array("org.wartremover.warts.Equals"))
class TypingTests extends TypingTestHelpers {
  
  // In the tests, leave the expected string empty so the inferred type is printed in the console
  // and you can copy and paste it after making sure it is correct.
  
  test("basic") {
    doTest("42", "int")
    doTest("fun x -> 42", "⊤ -> int")
    doTest("fun x -> x", "'a -> 'a")
    doTest("fun x -> x 42", "(int -> 'a) -> 'a")
    doTest("(fun x -> x) 42", "int")
    doTest("fun f -> fun x -> f (f x)  // twice", "('a ∨ 'b -> 'a) -> 'b -> 'a")
    doTest("let twice = fun f -> fun x -> f (f x) in twice", "('a ∨ 'b -> 'a) -> 'b -> 'a")
  }
  
  test("booleans") {
    doTest("true", "bool")
    doTest("not true", "bool")
    doTest("fun x -> not x", "bool -> bool")
    doTest("(fun x -> not x) true", "bool")
    doTest("fun x -> fun y -> fun z -> if x then y else z",
      "bool -> 'a -> 'a -> 'a")
    doTest("fun x -> fun y -> if x then y else x",
      "'a ∧ bool -> 'a -> 'a")
    
    error("succ true",
      "cannot constrain bool <: int")
    error("fun x -> succ (not x)",
      "cannot constrain bool <: int")
    error("(fun x -> not x.f) { f = 123 }",
      "cannot constrain int <: bool")
    error("(fun f -> fun x -> not (f x.u)) false",
      "cannot constrain bool <: 'a -> 'b")
  }
  
  test("records") {
    doTest("fun x -> x.f", "{f: 'a} -> 'a")
    doTest("{}", "{}") // note: MLsub returns "⊤" (equivalent)
    doTest("{ f = 42 }", "{f: int}")
    doTest("{ f = 42 }.f", "int")
    doTest("(fun x -> x.f) { f = 42 }", "int")
    doTest("fun f -> { x = f 42 }.x", "(int -> 'a) -> 'a")
    doTest("fun f -> { x = f 42; y = 123 }.y", "(int -> ⊤) -> int")
    doTest("if true then { a = 1; b = true } else { b = false; c = 42 }", "{b: bool}")
    
    error("{ a = 123; b = true }.c",
      "missing field: c in {a: int, b: bool}")
    error("fun x -> { a = x }.b",
      "missing field: b in {a: 'a}")
  }
  
  test("self-app") {
    doTest("fun x -> x x", "'a ∧ ('a -> 'b) -> 'b")
    
    doTest("fun x -> x x x", "'a ∧ ('a -> 'a -> 'b) -> 'b")
    doTest("fun x -> fun y -> x y x", "'a ∧ ('b -> 'a -> 'c) -> 'b -> 'c")
    doTest("fun x -> fun y -> x x y", "'a ∧ ('a -> 'b -> 'c) -> 'b -> 'c")
    doTest("(fun x -> x x) (fun x -> x x)", "⊥")
    
    doTest("fun x -> {l = x x; r = x }",
      "'a ∧ ('a -> 'b) -> {l: 'b, r: 'a}")
    
    // From https://github.com/stedolan/mlsub
    // Y combinator:
    doTest("(fun f -> (fun x -> f (x x)) (fun x -> f (x x)))",
      "('a -> 'a) -> 'a")
    // Z combinator:
    doTest("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)))",
      "(('a -> 'b) -> 'c ∧ ('a -> 'b)) -> 'c")
    // Function that takes arbitrarily many arguments:
    doTest("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v))) (fun f -> fun x -> f)",
      "⊤ -> (⊤ -> 'a) as 'a")
    
    doTest("let rec trutru = fun g -> trutru (g true) in trutru",
      "(bool -> 'a) as 'a -> ⊥")
    doTest("fun i -> if ((i i) true) then true else true",
      "'a ∧ ('a -> bool -> bool) -> bool")
    // ^ for: λi. if ((i i) true) then true else true,
    //    Dolan's thesis says MLsub infers: (α → ((bool → bool) ⊓ α)) → bool
    //    which does seem equivalent, despite being quite syntactically different
  }
  
  test("let-poly") {
    doTest("let f = fun x -> x in {a = f 0; b = f true}", "{a: int, b: bool}")
    doTest("fun y -> let f = fun x -> x in {a = f y; b = f true}",
      "'a -> {a: 'a, b: bool}")
    doTest("fun y -> let f = fun x -> y x in {a = f 0; b = f true}",
      "(bool ∨ int -> 'a) -> {a: 'a, b: 'a}")
    doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> true)}",
      "'a -> {a: 'a, b: bool}")
    doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> succ z)}",
      "'a ∧ int -> {a: 'a, b: int}")
  }
  
  test("recursion") {
    doTest("let rec f = fun x -> f x.u in f",
      "{u: 'a} as 'a -> ⊥")
    
    // from https://www.cl.cam.ac.uk/~sd601/mlsub/
    doTest("let rec recursive_monster = fun x -> { thing = x; self = recursive_monster x } in recursive_monster",
      "'a -> {self: 'b, thing: 'a} as 'b")
  }
  
  test("random") {
    doTest("(let rec x = {a = x; b = x} in x)",                           "{a: 'a, b: 'a} as 'a")
    doTest("(let rec x = fun v -> {a = x v; b = x v} in x)",              "⊤ -> {a: 'a, b: 'a} as 'a")
    error("let rec x = (let rec y = {u = y; v = (x y)} in 0) in 0",       "cannot constrain int <: 'a -> 'b")
    doTest("(fun x -> (let y = (x x) in 0))",                             "'a ∧ ('a -> ⊤) -> int")
    doTest("(let rec x = (fun y -> (y (x x))) in x)",                     "('b -> 'b ∧ 'a) as 'a -> 'b")
    doTest("fun next -> 0",                                               "⊤ -> int")
    doTest("((fun x -> (x x)) (fun x -> x))",                             "('b ∨ ('b -> 'a)) as 'a")
    doTest("(let rec x = (fun y -> (x (y y))) in x)",                     "('b ∧ ('b -> 'a)) as 'a -> ⊥")
    doTest("fun x -> (fun y -> (x (y y)))",                               "('a -> 'b) -> 'c ∧ ('c -> 'a) -> 'b")
    doTest("(let rec x = (let y = (x x) in (fun z -> z)) in x)",          "'a -> ('a ∨ ('a -> 'b)) as 'b")
    doTest("(let rec x = (fun y -> (let z = (x x) in y)) in x)",          "'a -> ('a ∨ ('a -> 'b)) as 'b")
    doTest("(let rec x = (fun y -> {u = y; v = (x x)}) in x)",
      "'a -> {u: 'a ∨ ('a -> 'b), v: 'b} as 'b")
    doTest("(let rec x = (fun y -> {u = (x x); v = y}) in x)",
      "'a -> {u: 'b, v: 'a ∨ ('a -> 'b)} as 'b")
    doTest("(let rec x = (fun y -> (let z = (y x) in y)) in x)",          "('b ∧ ('a -> ⊤) -> 'b) as 'a")
    doTest("(fun x -> (let y = (x x.v) in 0))",                           "{v: 'a} ∧ ('a -> ⊤) -> int")
    doTest("let rec x = (let y = (x x) in (fun z -> z)) in (x (fun y -> y.u))", // [test:T1]
      "('b ∨ ('b ∧ {u: 'c} -> 'a ∨ 'c)) as 'a")
  }
  
  
}
