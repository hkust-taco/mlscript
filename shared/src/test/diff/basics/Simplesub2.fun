// Tests ported from Simplesub



// --- mlsub --- //


let id = x => x
//│ id: 'a -> 'a

let twice = f => x => f (f x)
//│ twice: ('a -> 'b & 'c -> 'a) -> 'c -> 'b

let object1 = { x: 42, y: id }
//│ object1: {x: 42, y: forall 'a. 'a -> 'a}

let object2 = { x: 17, y: false }
//│ object2: {x: 17, y: false}

let pick_an_object = b =>
  if b then object1 else object2
//│ pick_an_object: bool -> {x: 17 | 42, y: forall 'a. 'a -> 'a | false}

let rec recursive_monster = x =>
  { thing: x, self: recursive_monster x }
//│ recursive_monster: 'a -> ({self: 'b, thing: 'a} as 'b)



// --- top-level-polymorphism --- //


let id = x => x
//│ id: 'a -> 'a

let ab = {u: id 0, v: id true}
//│ ab: {u: 0, v: true}



// --- rec-producer-consumer --- //


let rec produce = arg => { head: arg, tail: produce (succ arg) }
let rec consume = strm => add strm.head (consume strm.tail)
//│ produce: int -> ({head: int, tail: 'a} as 'a)
//│ consume: ({head: int, tail: 'a} as 'a) -> int

let codata = produce 42
let res = consume codata
//│ codata: {head: int, tail: 'a} as 'a
//│ res: int

let rec codata2 = { head: 0, tail: { head: 1, tail: codata2 } }
let res = consume codata2
//│ codata2: {head: 0, tail: {head: 1, tail: 'a}} as 'a
//│ res: int

// TODO better parser error
:pe
let rec produce3 = b => { head: 123, tail: if b then codata else codata2 }
//│ /!\ Parse error: Expected let binding:1:1, found "let rec pr" at l.61:1: let rec produce3 = b => { head: 123, tail: if b then codata else codata2 }

let rec produce3 = b => { head: 123, tail: (if b then codata else codata2) }
let res = x => consume (produce3 x)
//│ produce3: bool -> {head: 123, tail: {head: int, tail: {head: int, tail: 'a}} as 'a}
//│ res: bool -> int

let consume2 =
  let rec go = strm => add strm.head (add strm.tail.head (go strm.tail.tail))
  strm => add strm.head (go strm.tail)
  // go
// let rec consume2 = strm => add strm.head (add strm.tail.head (consume2 strm.tail.tail))
let res = consume2 codata2
//│ consume2: {head: int, tail: {head: int, tail: 'a} as 'a} -> int
//│ res: int

