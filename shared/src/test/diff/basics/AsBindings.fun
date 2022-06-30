
let f x =
  discard / x as { v: (y) } // TODO accept plain `y`
  log / v
  log / y + 1
//│ f: anything -> unit

let f x =
  discard / x as { v: (y) } // TODO accept plain `y`
  log / v + 1
  log / y
//│ f: anything -> unit


