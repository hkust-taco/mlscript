
:p
data Test a b
//│ Parsed: data Test a b;
//│ Desugared: class Test[a, b]: {a: a, b: b}
//│ Desugared: def Test: [a, b] -> a -> b -> Test[a, b]
//│ Defined class Test[+a, +b]
//│ Test: 'a -> 'b -> Test['a, 'b]

:p
data Person(name: string, age: int)
//│ Parsed: data Person '(' {name: string, age: int,} ')';
//│ Desugared: class Person: {age: int, name: string}
//│ Desugared: def Person: [] -> (name: string, age: int,) -> Person[]
//│ Defined class Person
//│ Person: (name: string, age: int,) -> Person

let p = Person("Bob", 42)
//│ p: Person

let foo q = q.age
foo p
//│ foo: {age: 'age} -> 'age
//│ res: int

// TODO properly check pattern types!
let bar (q: Person _) = q.age
//│ bar: (q: {age: 'age},) -> 'age

bar p
//│ res: int

:e
bar {}
bar {name: "Bob"}
bar {age: 1} // TODO B/E
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.34: 	bar {}
//│ ║        	^^^^^^
//│ ╟── tuple of type `anything` does not have field 'age'
//│ ║  l.34: 	bar {}
//│ ║        	    ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ║        	                         ^^^^
//│ ╟── from binding:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ╙──      	         ^^^^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.35: 	bar {name: "Bob"}
//│ ║        	^^^^^^^^^^^^^^^^^
//│ ╟── record of type `{name: "Bob"}` does not have field 'age'
//│ ║  l.35: 	bar {name: "Bob"}
//│ ║        	    ^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ║        	                         ^^^^
//│ ╟── from binding:
//│ ║  l.27: 	let bar (q: Person _) = q.age
//│ ╙──      	         ^^^^^^^^^^^
//│ res: error
//│ res: 1

let fake-p = { name: "Bob", age: 42 }
//│ fake-p: {age: 42, name: "Bob"}

// :e // TODO B/E
bar fake-p
//│ res: 42

data Wine(name: string, age: int)
let w = Wine("Côtes du Rhône", 3)
//│ Defined class Wine
//│ Wine: (name: string, age: int,) -> Wine
//│ w: Wine

// :e
bar w
bar (q: w)
//│ res: int
//│ res: int

let bar2 (q: Person _) = succ q.age
//│ bar2: (q: {age: int},) -> int


:e
let nested x =
  data Foo a // Note: we get one error for the synthetic class, and one for the synthetic def...
  Foo x
//│ ╔══[ERROR] Illegal position for this type declaration statement.
//│ ║  l.90: 	  data Foo a // Note: we get one error for the synthetic class, and one for the synthetic def...
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] Illegal position for this definition statement.
//│ ║  l.90: 	  data Foo a // Note: we get one error for the synthetic class, and one for the synthetic def...
//│ ╙──      	       ^^^^^
//│ ╔══[ERROR] identifier not found: Foo
//│ ║  l.91: 	  Foo x
//│ ╙──      	  ^^^
//│ nested: error -> error

