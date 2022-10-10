
let a = 1
let b = 2
let c = 3
let d = 4
//│ a: 1
//│ b: 2
//│ c: 3
//│ d: 4

a + b
//│ res: int

:p
a +
  b
//│ Parsed: + a {b};
//│ Desugared: + a {b}
//│ AST: App(App(Var(+), Var(a)), Blk(...))
//│ res: int

:pe
a +
  b +
  c
//│ /!\ Parse error: Expected expression:1:1, found "a +\n  b +\n" at l.23:1: a +

:p
succ a +
  b +
    c
//│ Parsed: + (succ a) {+ b {c}};
//│ Desugared: + (succ a) {+ b {c}}
//│ AST: App(App(Var(+), App(Var(succ), Var(a))), Blk(...))
//│ res: int

:p
succ / a +
  b +
    c
//│ Parsed: succ (+ a {+ b {c}});
//│ Desugared: succ (+ a {+ b {c}})
//│ AST: App(Var(succ), App(App(Var(+), Var(a)), Blk(...)))
//│ res: int

:p
a
  + b
a
  + b
  + c
a
  + b
  + c
  + d
//│ Parsed: + a b; + (+ a b) c; + (+ (+ a b) c) d;
//│ Desugared: + a b
//│ AST: App(App(Var(+), Var(a)), Var(b))
//│ Desugared: + (+ a b) c
//│ AST: App(App(Var(+), App(App(Var(+), Var(a)), Var(b))), Var(c))
//│ Desugared: + (+ (+ a b) c) d
//│ AST: App(App(Var(+), App(App(Var(+), App(App(Var(+), Var(a)), Var(b))), Var(c))), Var(d))
//│ res: int
//│ res: int
//│ res: int

:p
a
  + b
  + c
    + 1
    + 2
      + 3
  + d
//│ Parsed: + (+ (+ a b) (+ (+ c 1) (+ 2 3))) d;
//│ Desugared: + (+ (+ a b) (+ (+ c 1) (+ 2 3))) d
//│ AST: App(App(Var(+), App(App(Var(+), App(App(Var(+), Var(a)), Var(b))), App(App(Var(+), App(App(Var(+), Var(c)), IntLit(1))), App(App(Var(+), IntLit(2)), IntLit(3))))), Var(d))
//│ res: int

:pe
a
+ b
//│ /!\ Parse error: Expected end-of-input:2:1, found "+ b\n" at l.82:1: + b

:pe
let x = 1
+ 2
//│ /!\ Parse error: Expected end-of-input:2:1, found "+ 2\n" at l.87:1: + 2

let x = 1
  + 2
//│ x: int

:pe
let x =
  1
  + 2
//│ /!\ Parse error: Expected end-of-input:3:3, found "+ 2\n" at l.97:3:   + 2

let x =
  1
    + 2
//│ x: int

succ / succ 1
  + 1
//│ res: int

:p
succ
    a + b
  + c
//│ Parsed: + (succ {+ a b}) c;
//│ Desugared: + (succ {+ a b}) c
//│ AST: App(App(Var(+), App(Var(succ), Blk(...))), Var(c))
//│ res: int

// Maybe allow this as it lets us nicely align the operands?
:pe
let test =
    a
  + b
  + c
//│ /!\ Parse error: Expected end-of-input:3:3, found "+ b\n  + c\n" at l.122:3:   + b
