
let a = 1
let b = 2
let c = 3
let d = 4
/// a: int
/// b: int
/// c: int
/// d: int

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
/// /!\ Parse error: Expected end-of-input:1:2, found "\n+ b" at l.67:2: a

:pe
let x = 1
+ 2
/// /!\ Parse error: Expected end-of-input:1:10, found "\n+ 2" at l.72:10: let x = 1

let x = 1
  + 2
/// x: int

:pe
let x =
  1
  + 2
/// /!\ Parse error: Expected end-of-input:2:4, found "\n  + 2" at l.82:4:   1

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
/// /!\ Parse error: Expected end-of-input:2:6, found "\n  + b\n  +" at l.105:6:     a
