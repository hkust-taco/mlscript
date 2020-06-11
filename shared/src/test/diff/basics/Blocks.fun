
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

// FIXME last line not applied
:p
id id
    id id
  id id
/// Parsed: {((id id) {(id id)}); (id id)}
/// res: 'a -> 'a
/// res: 'a -> 'a
