
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
//│ Parsed: (discard (foo 1;));
//│ res: unit

:e
discard foo
  1
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.49: 	discard foo
//│ ║        	^^^^^^^^^^^
//│ ║  l.50: 	  1
//│ ║        	^^^
//│ ╟── expression of type `unit` is not a function
//│ ║  l.49: 	discard foo
//│ ╙──      	^^^^^^^^^^^
//│ res: nothing

:e // TODO better error: discarded non-unit value
foo
  foo 1
  foo 2
//│ ╔══[ERROR] Type mismatch in function application:
//│ ║  l.63: 	  foo 1
//│ ║        	  ^^^^^
//│ ╙── expression of type `int` does not match type `unit`
//│ res: int

:p
id id
  id
//│ Parsed: ((id id) id;);
//│ res: 'a -> 'a

:p
id id id
  id id id
    id id id
      id id id
//│ Parsed: (((id id) id) (((id id) id) (((id id) id) ((id id) id););););
//│ res: 'a -> 'a

:p
id id /
  id id /
    id id
//│ Parsed: ((id id) ((id id) (id id);););
//│ res: 'a -> 'a

:p
id id
    id id
  id id
//│ Parsed: (((id id) (id id);) (id id););
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
//│ ║  l.143: 	  succ
//│ ╙──       	  ^^^^
//│ res: int

:pe
succ (succ
1)
//│ /!\ Parse error: Expected end-of-input:1:6, found "(succ\n1)" at l.152:6: succ (succ

:pe
succ (succ
succ 1)
//│ /!\ Parse error: Expected end-of-input:1:6, found "(succ\nsucc" at l.157:6: succ (succ

:pe
succ (succ
succ
  1)
//│ /!\ Parse error: Expected end-of-input:1:6, found "(succ\nsucc" at l.162:6: succ (succ

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
//│ res: {}
//│ res: 1
//│ res: 1
//│ res: int

succ
  (
    let x = 1
    x
  )
//│ res: int

:pe
succ
  (
    let x = 1
    x
)
//│ /!\ Parse error: Expected expression:1:1, found "succ\n  (\n " at l.190:1: succ

:pe
let a =
    succ
  1
  "?"
//│ /!\ Parse error: Expected end-of-input:3:3, found "1\n  \"?\"" at l.200:3:   1

:pe
  1
//│ /!\ Parse error: Expected (let binding | expression):1:1, found "  1" at l.205:1:   1

