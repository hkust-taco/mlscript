
:p
data Test a b
//│ Parsed: data ((Test a) b);
//│ Desugared: class Test[a, b]: {a: a, b: b}
//│ Desugared: def Test: [a, b] -> a -> b -> Test[a, b]
//│ Defined class Test
//│ Test: 'a -> 'b -> (test & {Test#b: 'b, a: 'a, b: 'b, Test#a: 'a})

:p
data Person(name: string, age: int)
//│ Parsed: data (Person ((name: string, age: int,);));
//│ Desugared: class Person: {age: int, name: string}
//│ Desugared: def Person: [] -> (name: string, age: int,) -> Person[]
//│ Defined class Person
//│ Person: (name: string, age: int,) -> (person & {name: string, age: int})

let p = Person("Bob", 42)
//│ p: person & {name: string, age: int}

let foo q = q.age
foo p
//│ foo: {age: 'a} -> 'a
//│ res: int

// TODO properly check pattern types!
let bar (q: Person _) = q.age
//│ bar: (q: {age: 'a},) -> 'a

bar p
//│ res: int

:e
bar {}
bar {name: "Bob"}
bar {age: 1} // TODO B/E
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.34: 	bar {}
//│ ║        	^^^^^^
//│ ╟── expression of type `anything` does not have field 'age'
//│ ║  l.34: 	bar {}
//│ ║        	    ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ║        	                         ^^^^
//│ ╟── from parameter type:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.35: 	bar {name: "Bob"}
//│ ║        	^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `{name: "Bob"}` does not have field 'age'
//│ ║  l.35: 	bar {name: "Bob"}
//│ ║        	    ^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ║        	                         ^^^^
//│ ╟── from parameter type:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^^^
//│ res: error
//│ res: 1

let fake-p = { name: "Bob", age: 42 }
//│ fake-p: {name: "Bob", age: 42}

// :e // TODO B/E
bar fake-p
//│ res: 42

data Wine(name: string, age: int)
let w = Wine("Côtes du Rhône", 3)
//│ Defined class Wine
//│ Wine: (name: string, age: int,) -> (wine & {name: string, age: int})
//│ w: wine & {name: string, age: int}

// :e
bar w
bar (q: w)
//│ res: int
//│ res: int

// TODO simplify: `{age: int}` is included in `Person _`!
// TODO in fact, maybe we shouldn't infer more than user annotations in parameter types...
let bar2 (q: Person _) = succ q.age
//│ bar2: (q: {age: int},) -> int


:e
let nested x =
  data Foo a // Note: we get one error for the synthetic class, and one for the synthetic def...
  Foo x
//│ ╔══[ERROR] Illegal position for this type declaration statement.
//│ ║  l.92: 	  data Foo a // Note: we get one error for the synthetic class, and one for the synthetic def...
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] Illegal position for this definition statement.
//│ ║  l.92: 	  data Foo a // Note: we get one error for the synthetic class, and one for the synthetic def...
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] identifier not found: Foo
//│ ║  l.93: 	  Foo x
//│ ╙──      	  ^^^
//│ nested: error -> error

