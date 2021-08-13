
// FIXME
class Test1: { x: Int }
//│ Defined class Test1

:e
type Test1 = { x: Int }
//│ ╔══[ERROR] Type 'Test1' is already defined.
//│ ║  l.7: 	type Test1 = { x: Int }
//│ ╙──     	     ^^^^^
//│ Defined type Test1

// FIXME
type Test2 = { x: Int }
//│ Defined type Test2

:pe
class Test = { x: Int }
//│ /!\ Parse error: Expected ":":1:12, found "= { x: Int" at l.18:12: class Test = { x: Int }

:pe
type Test: { x: Int }
//│ /!\ Parse error: Expected "=":1:10, found ": { x: Int" at l.22:10: type Test: { x: Int }

// FIXME
type Test3 = Int -> Int
//│ Defined type Test3

// FIXME
type Test4 = Int -> Int -> Int
//│ Defined type Test4

// FIXME
type Test5 = (Int -> Int) -> Int
//│ Defined type Test5


type T = Int
//│ Defined type T

:e
type T = Int
type T = Int
//│ ╔══[ERROR] Type 'T' is already defined.
//│ ║  l.42: 	type T = Int
//│ ╙──      	     ^
//│ ╔══[ERROR] Type 'T' is already defined.
//│ ║  l.43: 	type T = Int
//│ ╙──      	     ^
//│ Defined type T
//│ Defined type T

:e
type TypeA = Int
foo 42
def foo = 1
foo 42
//│ Defined type TypeA
//│ ╔══[ERROR] identifier not found: foo
//│ ║  l.55: 	foo 42
//│ ╙──      	^^^
//│ res: error
//│ foo: 1
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.57: 	foo 42
//│ ║        	^^^^^^
//│ ╟── expression of type `1` is not a function
//│ ║  l.56: 	def foo = 1
//│ ║        	          ^
//│ ╟── but it flows into reference with expected type `42 -> ?a`
//│ ║  l.57: 	foo 42
//│ ╙──      	^^^
//│ res: error

type TypeB = TypeB
def test = fun x -> x
type TypeC = TypeA
//│ Defined type TypeB
//│ Defined type TypeC
//│ test: 'a -> 'a

