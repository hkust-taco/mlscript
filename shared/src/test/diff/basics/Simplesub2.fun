// Tests ported from Simplesub



// --- mlsub --- //


let id = x => x
//│ id: 'a -> 'a

let twice = f => x => f (f x)
//│ twice: ((forall 'a, 'b, 'c. ('c
//│   where
//│     'a <: 'b -> 'c)) -> 'd & 'b -> 'a & 'a) -> 'b -> 'd

let object1 = { x: 42, y: id }
//│ object1: {x: 42, y: forall 'a. 'a -> 'a}

let object2 = { x: 17, y: false }
//│ object2: {x: 17, y: false}

let pick_an_object = b =>
  if b then object1 else object2
//│ pick_an_object: bool -> {x: 17 | 42, y: forall 'a. 'a -> 'a | false}

let rec recursive_monster = x =>
  { thing: x, self: recursive_monster x }
//│ recursive_monster: 'a -> 'b
//│   where
//│     'b :> {self: 'b, thing: 'a}



// --- top-level-polymorphism --- //


let id = x => x
//│ id: 'a -> 'a

let ab = {u: id 0, v: id true}
//│ ab: {u: 0, v: true}



// --- rec-producer-consumer --- //


let rec produce = arg => { head: arg, tail: produce (succ arg) }
let rec consume = strm => add strm.head (consume strm.tail)
//│ produce: int -> 'a
//│   where
//│     'a :> {head: int, tail: 'a}
//│ consume: 'a -> int
//│   where
//│     'a <: {head: int, tail: 'a}

let codata = produce 42
let res = consume codata
//│ codata: 'a
//│   where
//│     'a :> {head: int, tail: 'a}
//│ res: int

let rec codata2 = { head: 0, tail: { head: 1, tail: codata2 } }
let res = consume codata2
//│ codata2: 'codata2
//│   where
//│     'codata2 :> {head: 0, tail: {head: 1, tail: 'codata2}}
//│ res: int

// TODO better parser error
:pe
let rec produce3 = b => { head: 123, tail: if b then codata else codata2 }
//│ /!\ Parse error: Expected let binding:1:1, found "let rec pr" at l.73:1: let rec produce3 = b => { head: 123, tail: if b then codata else codata2 }

let rec produce3 = b => { head: 123, tail: (if b then codata else codata2) }
let res = x => consume (produce3 x)
//│ produce3: bool -> {head: 123, tail: forall 'codata2, 'a. 'codata2 | 'a}
//│   where
//│     'a :> {head: int, tail: 'a}
//│     'codata2 :> {head: 0, tail: {head: 1, tail: 'codata2}}
//│ res: bool -> int

let consume2 =
  let rec go = strm => add strm.head (add strm.tail.head (go strm.tail.tail))
  strm => add strm.head (go strm.tail)
  // go
// let rec consume2 = strm => add strm.head (add strm.tail.head (consume2 strm.tail.tail))
let res = consume2 codata2
//│ consume2: {head: int, tail: {head: int, tail: 'tail}} -> int
//│   where
//│     'tail <: {head: int, tail: 'tail}
//│ res: int

