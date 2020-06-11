
// let foo x = // TODO
let foo = x =>
  let a = x + 1
  a
/// foo: int -> int

let foo = x =>
  println x
  let u = x + 1
  println true
  u + 1
/// foo: int -> int

let foo = x =>
  println x;
  let u = x + 1;
  println true;
  u + 1
/// foo: int -> int

foo 1
foo / 1
foo / foo / 1
/// res: int
/// res: int
/// res: int
foo
  foo
    1
/// res: int
foo
  foo
    1
  foo
    1
/// res: int
foo / foo /
  foo 1
/// res: int

:p
id id
  id
/// Parsed: {((id id) {id})}
/// res: 'a -> 'a

:p
id id id
  id id id
    id id id
      id id id
/// Parsed: {(((id id) id) {(((id id) id) {(((id id) id) {((id id) id)})})})}
/// res: 'a -> 'a

:p
id id /
  id id /
    id id
/// Parsed: {((id id) {((id id) {(id id)})})}
/// res: 'a -> 'a

:p
id id
    id id
  id id
/// Parsed: {(((id id) {(id id)}) {(id id)})}
/// res: 'a -> 'a

let foo =
  println 1
  println 2
/// foo: unit

let foo =
  println 1
  
  println 2
/// foo: unit

let foo =
 
  println 1
   
  println 2
/// foo: unit

succ (
  println 1
  1
)
succ (
  println 1
  1)
succ (succ
  1)
succ (succ
  1
)
succ (succ
  succ 1)
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int

:e
succ (
  succ
  1
)
/// /!\ Type error: Pure expression does nothing in statement position.
/// l.110: 	  succ
///        	  ^^^^
/// res: int

:pe
succ (succ
1)
/// /!\ Parse error: Expected applied expressions:1:1, found "succ (succ" at line 119: succ (succ

:pe
succ (succ
succ 1)
/// /!\ Parse error: Expected applied expressions:1:1, found "succ (succ" at line 124: succ (succ

:pe
succ (succ
succ
  1)
/// /!\ Parse error: Expected applied expressions:1:1, found "succ (succ" at line 129: succ (succ

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
/// res: unit
/// res: int
/// res: int
/// res: int

succ
  (
    let x = 1
    x
  )
/// res: int

:pe
succ
  (
    let x = 1
    x
)
/// /!\ Parse error: Expected applied expressions:1:1, found "succ\n  (\n " at line 157: succ

:pe
let a =
    succ
  1
  "?"
/// /!\ Parse error: Expected end-of-input:2:9, found "\n  1\n  \"?\"" at line 166:     succ

:pe
  1
/// /!\ Parse error: Expected (let binding | applied expressions):1:1, found "  1" at line 172:   1

