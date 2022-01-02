
let f x =
  discard / x as { v: (y) } // TODO accept plain `y`
  log / v
  log / y + 1
//│ f: {v: int} -> unit

let f x =
  discard / x as { v: (y) } // TODO accept plain `y`
  log / v + 1
  log / y
//│ f: {v: int} -> unit


