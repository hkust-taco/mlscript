
// FIXME
class Test1: { x: Int }
//│ class Test1

:e
type Test1 = { x: Int }
//│ ╔══[ERROR] Type 'Test1' is already defined.
//│ ║  l.7: 	type Test1 = { x: Int }
//│ ╙──     	     ^^^^^
//│ type Test1

// FIXME
type Test2 = { x: Int }
//│ type Test2

:pe
class Test = { x: Int }
//│ /!\ Parse error: Expected ":":1:12, found "= { x: Int" at l.18:12: class Test = { x: Int }

:pe
type Test: { x: Int }
//│ /!\ Parse error: Expected "=":1:10, found ": { x: Int" at l.22:10: type Test: { x: Int }

// FIXME
type Test3 = Int -> Int
//│ type Test3

// FIXME
type Test4 = Int -> Int -> Int
//│ type Test4

// FIXME
type Test5 = (Int -> Int) -> Int
//│ type Test5


type T = Int
//│ type T

:e
type T = Int
type T = Int
//│ ╔══[ERROR] Type 'T' is already defined.
//│ ║  l.42: 	type T = Int
//│ ╙──      	     ^
//│ ╔══[ERROR] Type 'T' is already defined.
//│ ║  l.43: 	type T = Int
//│ ╙──      	     ^
//│ type T
//│ type T

// FIXME error is not shown
:d
type TypeA = TypeB
foo 42
//│ 0. Typing term (foo 42)
//│  0. Typing term foo
//│  0. : [error]
//│  0. Typing term 42
//│  0. : 42
//│  CONSTRAIN [[error]] <! ([42] -> α0)
//│    where 
//│  C [[error]] <! ([42] -> α0)
//│   C [error] <! ([42] -> α0)
//│    C error <! ([42] -> α0)
//│     C [42] <! error
//│      C 42 <! error
//│     C error <! α0
//│ 0. : α0
//│ type TypeA

type TypeB = TypeB
def foo = 1
foo 42
type TypeC = Int
//│ type TypeB
//│ type TypeC
//│ foo: 1

