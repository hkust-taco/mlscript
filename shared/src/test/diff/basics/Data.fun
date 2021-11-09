
data Test a b
//│ Test: 'a -> 'b -> {a: 'a, b: 'b}

data Person(name: string, age: int)
//│ Person: (name: string & 'a, age: int & 'b,) -> {age: 'b, name: 'a}

let p = Person("Bob", 42)
//│ p: Person ("Bob", 42,)

let foo q = q.age
foo p
//│ foo: {age: 'a} -> 'a
//│ res: 42

// TODO why not simplified?
let bar (q: Person _) = q.age
//│ bar: (q: Person (name: string & 'a, age: int & 'b,) & {age: 'c},) -> 'c

bar p
//│ res: 42

:e
bar {}
bar {name: "Bob"}
bar {age: 1} // TODO B/E
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.24: 	bar {}
//│ ║        	^^^^^^
//│ ╟── expression of type `anything` does not have field 'age'
//│ ║  l.24: 	bar {}
//│ ║        	    ^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ║        	                         ^^^^
//│ ╟── from parameter type:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.25: 	bar {name: "Bob"}
//│ ║        	^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `{name: "Bob"}` does not have field 'age'
//│ ║  l.25: 	bar {name: "Bob"}
//│ ║        	    ^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from field selection:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ║        	                         ^^^^
//│ ╟── from parameter type:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^^^
//│ res: error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.26: 	bar {age: 1} // TODO B/E
//│ ║        	^^^^^^^^^^^^
//│ ╟── expression of type `(name: string & ?a, age: int & ?b,) & ?c -> {age: 1}` does not match type `Person`
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ║        	            ^^^^^^
//│ ╟── Note: constraint arises from data symbol:
//│ ║  l.5: 	data Person(name: string, age: int)
//│ ║       	     ^^^^^^
//│ ╟── from reference:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^
//│ res: 1 | error

let fake-p = { name: "Bob", age: 42 }
//│ fake-p: {name: "Bob", age: 42}

:e // TODO B/E
bar fake-p
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.71: 	bar fake-p
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `(name: string & ?a, age: int & ?b,) & ?c -> {name: "Bob", age: 42}` does not match type `Person`
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ║        	            ^^^^^^
//│ ╟── Note: constraint arises from data symbol:
//│ ║  l.5: 	data Person(name: string, age: int)
//│ ║       	     ^^^^^^
//│ ╟── from reference:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^
//│ res: 42 | error

data Wine(name: string, age: int)
let w = Wine("Côtes du Rhône", 3)
//│ Wine: (name: string & 'a, age: int & 'b,) -> {age: 'b, name: 'a}
//│ w: Wine ("Côtes du Rhône", 3,)

:e
bar w
bar (q: w)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.92: 	bar w
//│ ║        	^^^^^
//│ ╟── expression of type `(name: string & ?a, age: int & ?b & ?b,) -> {age: ?b | 3, name: ?a | "Côtes du Rhône"}` does not match type `Person`
//│ ║  l.86: 	data Wine(name: string, age: int)
//│ ║        	     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── but it flows into reference with expected type `(q: Person ((name: string & ?c, age: int & ?d,) & ?e) & {age: ?f} & ?g,)`
//│ ║  l.92: 	bar w
//│ ║        	    ^
//│ ╟── Note: constraint arises from data symbol:
//│ ║  l.5: 	data Person(name: string, age: int)
//│ ║       	     ^^^^^^
//│ ╟── from reference:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^
//│ res: 3 | error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.93: 	bar (q: w)
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `(name: string & ?a, age: int & ?b & ?b,) -> {age: ?b | 3, name: ?a | "Côtes du Rhône"}` does not match type `Person`
//│ ║  l.86: 	data Wine(name: string, age: int)
//│ ║        	     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `(q: Person ((name: string & ?c, age: int & ?d,) & ?e) & {age: ?f} & ?g,)`
//│ ║  l.93: 	bar (q: w)
//│ ║        	    ^^^^^^
//│ ╟── Note: constraint arises from data symbol:
//│ ║  l.5: 	data Person(name: string, age: int)
//│ ║       	     ^^^^^^
//│ ╟── from reference:
//│ ║  l.17: 	let bar (q: Person _) = q.age
//│ ╙──      	            ^^^^^^
//│ res: 3 | error

// TODO simplify: `{age: int}` is included in `Person _`!
// TODO in fact, maybe we shouldn't infer more than user annotations in parameter types...
let bar2 (q: Person _) = succ q.age
//│ bar2: (q: Person (name: string & 'a, age: int & 'b,) & {age: int},) -> int

