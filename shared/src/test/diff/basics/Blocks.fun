
// let foo x = // TODO
let foo = x =>
  let a = x + 1
  a
//│ foo: int -> int

let foo = x =>
  log x
  let u = x + 1
  log true
  u + 1
//│ foo: int -> int

let foo = x =>
  log x;
  let u = x + 1;
  log true;
  u + 1
//│ foo: int -> int

foo 1
foo / 1
foo / foo / 1
//│ res: int
//│ res: int
//│ res: int
foo
  foo
    1
//│ res: int
foo
  discard / foo
    1
  foo
    1
//│ res: int
foo / foo /
  foo 1
//│ res: int

:p
discard / foo
    1
//│ Parsed: discard (foo {1});
//│ Desugared: discard (foo {1})

:e
discard foo
  1
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.49: 	discard foo
//│ ║        	^^^^^^^^^^^
//│ ║  l.50: 	  1
//│ ║        	^^^
//│ ╟── application of type `unit` is not a function
//│ ║  l.49: 	discard foo
//│ ╙──      	^^^^^^^^^^^
//│ res: error

:w
foo
  foo 1
  foo 2
//│ ╔══[WARNING] Expression in statement position should have type `unit`.
//│ ╟── Use the `discard` function to discard non-unit values, making the intent clearer.
//│ ╟── Type mismatch in application:
//│ ║  l.63: 	  foo 1
//│ ║        	  ^^^^^
//│ ╟── operator application of type `int` is not an instance of type `unit`
//│ ║  l.19: 	  u + 1
//│ ║        	  ^^^^^
//│ ╟── but it flows into application with expected type `unit`
//│ ║  l.63: 	  foo 1
//│ ╙──      	  ^^^^^
//│ res: int

:p
id id
  id
//│ Parsed: id id {id};
//│ Desugared: id id {id}
//│ res: 'a -> 'a

:p
id id id
  id id id
    id id id
      id id id
//│ Parsed: id id id {id id id {id id id {id id id}}};
//│ Desugared: id id id {id id id {id id id {id id id}}}
//│ res: 'a -> 'a

:p
id id /
  id id /
    id id
//│ Parsed: id id {id id {id id}};
//│ Desugared: id id {id id {id id}}
//│ res: 'a -> 'a

:p
id id
    id id
  id id
//│ Parsed: id id {id id} {id id};
//│ Desugared: id id {id id} {id id}
//│ res: 'a -> 'a

let foo =
  log 1
  log 2
//│ foo: unit

let foo =
  log 1
  
  log 2
//│ foo: unit

let foo =
 
  log 1
   
  log 2
  
//│ foo: unit

succ (
  log 1
  1
)
succ (
  log 1
  1)
succ (succ
  1)
succ (succ
  1
)
succ (succ
  succ 1)
succ (succ
    let x = 1; x)
//│ res: int
//│ res: int
//│ res: int
//│ res: int
//│ res: int
//│ res: int

:w
succ (
  succ
  1
)
//│ ╔══[WARNING] Pure expression does nothing in statement position.
//│ ║  l.154: 	  succ
//│ ╙──       	  ^^^^
//│ res: int

:pe
succ (succ
1)
//│ /!\ Parse error: Expected end-of-input:1:6, found "(succ\n1)\n" at l.163:6: succ (succ

:pe
succ (succ
succ 1)
//│ /!\ Parse error: Expected end-of-input:1:6, found "(succ\nsucc" at l.168:6: succ (succ

:pe
succ (succ
succ
  1)
//│ /!\ Parse error: Expected end-of-input:1:6, found "(succ\nsucc" at l.173:6: succ (succ

(let x = 1)
(let x = 1; x)
(
  let x = 1
  x
)
succ(
  let x = 1
  x
)
//│ res: ()
//│ res: 1
//│ res: 1
//│ res: int

succ
  (
    let x = 1
    x
  )
//│ res: int

log 1; log 2; log 3

let a = 1; log a; let b = 2
//│ a: 1
//│ b: 2

(let a = 1; log a; let b = 2)
//│ res: ()

(let a = 1; log a; let b = 2; a + b)
//│ res: int


:e
let test =
  let aaa =
    let bbb = 42
    bbb
  bbb
//│ ╔══[ERROR] identifier not found: bbb
//│ ║  l.218: 	  bbb
//│ ╙──       	  ^^^
//│ test: error

let test =
  let aaa =
    let bbb = 42
    bbb
  aaa
//│ test: 42

:e
aaa
//│ ╔══[ERROR] identifier not found: aaa
//│ ║  l.232: 	aaa
//│ ╙──       	^^^
//│ res: error


:pe
succ
  (
    let x = 1
    x
)
//│ /!\ Parse error: Expected expression:1:1, found "succ\n  (\n " at l.240:1: succ

:pe
let a =
    succ
  1
  "?"
//│ /!\ Parse error: Expected end-of-input:3:3, found "1\n  \"?\"\n" at l.250:3:   1

:pe
  1
//│ /!\ Parse error: Expected (data type definition | data definition | let binding | expression):1:1, found "  1\n" at l.255:1:   1

