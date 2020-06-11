
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

// TODO report pure exprs in statements pos; there are some here!
succ (
  succ
  1
)
succ (
  succ
  1)
succ (succ
  1)
succ (succ
1)
succ (succ
  1
)
succ (succ
  succ 1)
succ (succ
succ 1)
succ (succ
succ
  1)
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int
/// res: int

:pe
let a =
    succ
  1
  "?"
/// /!\ Parse error: Expected end-of-input:2:9, found "\n  1\n  \"?\"" at line 121:     succ

:pe
  1
/// /!\ Parse error: Expected (let binding | applied expressions):1:1, found "  1" at line 127:   1

