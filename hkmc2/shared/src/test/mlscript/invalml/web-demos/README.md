# Web-Demo 

## Syntax

Most syntax can be found in the paper.
We list the changed and non-mentioned syntax in this documentation.

### ADT Declarations

We use the following syntax to declare ADTs:
```fs
class List[T] with
  constructor
    Nil
    Cons(x: T, xs: List[out T])
```
which is equivalent to the syntax used in the paper:
```scala
enum List[T]:
  case Nil
  case Cons(x: T, xs: List[out T])
```

### Functions

Keyword `case` is used to create a function that
pattern matches on the unique parameter.
```fs
fun fact = case
  1 then 1
  n then n * fact(n - 1)
```
which is equivalent to
```fs
fun fact(x) = if x is
  1 then 1
  n then n * fact(n - 1)
```

Keyword `of` is used for function application
to avoid unnecessary parentheses.
```fs
fun add(x, y, z) = x + y + z
add of 1, 2, 3
```
which is equivalent to
```fs
fun add(x, y, z) = x + y + z
add(1, 2, 3)
```

### Type Annotations

Type annotations are written in the following syntax:
```fs
[T] -> ... // equivalent to ∀ T. ...
[T extends S] -> ... // equivalent to ∀ T {T ≤ S}. ...
[T restricts S] -> ... // equivalent to ∀ T {S ≤ T}. ...
T | S // equivalent to T ∨ S
T & S // equivalent to T ∧ S
~T // equivalent to ¬T
```
