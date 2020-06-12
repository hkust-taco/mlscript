
let a = 1
let b = 2
let c = 3
let d = 4
/// a: 1
/// b: 2
/// c: 3
/// d: 4

a + b
/// res: int

:p
a +
  b
/// Parsed: ((+ a) b;);
/// res: int

:pe
a +
  b +
  c
/// /!\ Parse error: Expected expression:1:1, found "a +\n  b +\n" at l.21:1: a +

:p
succ a +
  b +
    c
/// Parsed: ((+ (succ a)) ((+ b) c;););
/// res: int

:p
succ / a +
  b +
    c
/// Parsed: (succ ((+ a) ((+ b) c;);));
/// res: int

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
/// Parsed: ((+ a) b); ((+ ((+ a) b)) c); ((+ ((+ ((+ a) b)) c)) d);
/// res: int
/// res: int
/// res: int

:p
a
  + b
  + c
    + 1
    + 2
      + 3
  + d
/// Parsed: ((+ ((+ ((+ a) b)) ((+ ((+ c) 1)) ((+ 2) 3)))) d);
/// res: int

:pe
a
+ b
/// /!\ Parse error: Expected end-of-input:2:1, found "+ b" at l.68:1: + b

:pe
let x = 1
+ 2
/// /!\ Parse error: Expected end-of-input:2:1, found "+ 2" at l.73:1: + 2

let x = 1
  + 2
/// x: int

:pe
let x =
  1
  + 2
/// /!\ Parse error: Expected end-of-input:3:3, found "+ 2" at l.83:3:   + 2

let x =
  1
    + 2
/// x: int

succ / succ 1
  + 1
/// res: int

:p
succ
    a + b
  + c
/// Parsed: ((+ (succ ((+ a) b);)) c);
/// res: int

// Maybe allow this as it lets us nicely align the operands?
:pe
let test =
    a
  + b
  + c
/// /!\ Parse error: Expected end-of-input:3:3, found "+ b\n  + c" at l.106:3:   + b
