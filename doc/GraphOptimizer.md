

## Find Splitting Targets

### Definitions with one of its parameters being destructed in its scope.

(To be split directly)

```haskell
let foo(x) = 
  ...
  case x of
    ...

...
let y = C(...)
... 
let z = foo(y)
...

-- splitting target: (foo, x)
```

### Definitions with one of its parameters being destructed in its callee's scopes.

(To be specialized on a specific input)

```haskell
let foo(x1) =
  ...
  case x1 of
    ...
  
let bar(x2) = 
  ...
  foo(x2)
  ...

...
let y = A(...)
... 
let z = bar(y)
...

-- specialization target: (bar, x2)
```

### Definitions with mixing constructors as return values and the return values are destructed

(To be split directly)

```haskell
let foo() =
  ...
  case ... of
    ... -> C1(...)
    ... -> C2(...)
  

let y = foo(...)
...
case y of
  ...

-- mixing target: foo
```

## Definition Splitting

- ```haskell
  -- (foo, x) is a splitting target 
  let foo(x) =
    ...
    case x of
      A -> ... a ...
      B -> ... b ...
  
  -- -->
  
  let foo$P(x) = 
    ...
    x, fv1, fv2, ....
  
  let foo$D1(x, fv1, fv2, ...) =
    ... a ...
  
  let foo$D2(x, fv1, fv2, ...) =
    ... b ...
  
  ```

- ```haskell
  -- (bar, x) is a specialization target
  let bar(x) =
    ...
  
  -- -->
  
  -- for every active input Ii
  let bar$C1(x) [x: I1] = 
    ...
  let bar$C2(x) [x: I2] = 
    ...
  ```

- ```haskell
  -- foo is a mixing target
  
  let foo(...) =
    ...
    case ... of
      A -> ... a ...
      B -> ... b ...
  
  -- -->
  
  let foo$P(...) = 
    ...
    fv0, fv1, ....
  
  let foo$D1(fv0, fv1, ...) =
    ... a ...
  
  let foo$D2(x, fv1, fv2, ...) =
    ... b ...
  ```

## Call Site Replacement of Splitting

(Assume there're definitions introduced by former splitting)

- ```haskell
  -- (foo, x) is a splitting target 
  
  ...
  let y = A(...)
  ... 
  let z = foo(y)
  ...
  
  -- -->
  
  ...
  let y = A(...)
  ...
  let x, fv1, fv2, ... = foo$P(y)
  let z = foo$D1(x, fv1, fv2, ...)
  ...
  
  ```

- ```haskell
  -- (bar, x2) is a specialization target
  
  ...
  let y = C(...)
  ...
  let z = bar(y)
  ...
  
  -- -->
  
  ...
  let y = C(...)
  ...
  let z = bar$D1(y) [x: ICtor(C)]
  ...
  
  ```

- ```haskell
  -- foo is a mixing target
  
  let foo() =
    ...
    case ... of
      A -> C1(...)
      B -> C2(...)
  
  let bar() =
    ...
    let y = foo(...)
    ...
    case y of
      ...
  
  -- -->
  
  let join bar$M(y) = 
    case y of
      ...
  
  let bar() =
    ...
    let f0, f1, ... = foo$P()
    ...
    case ... of
      A ->
        let m = foo$D1(f0, f1, ...)
        jump bar$M(m)
      B ->
        let n = foo$D2(f0, f1, ...)
        jump bar$M(n)
  
  ```

## Scalar Replacement

```haskell
let foo(x) =
  ...
  let x_a = x.a
  ...
  let x_b = x.b
  ...
  let x_c = x.c
  ...

let y = C(a = ..., b = ..., c = ...)
...
let z = foo(y) ...
...

-- SR target: (foo, x, {a, b, c})

-- -->

let foo$S(x_a, x_b, x_c) =
  ...
  let x_a = x.a
  ...
  let x_b = x.b
  ...
  let x_c = x.c
  ...

let y = C(a = ..., b = ..., c = ...)
...
let p = y.a
let q = y.b
let r = y.c
let z = foo$S(p, q, r)
...

```

## Trivial Call & Jump Simplification

- ```haskell
  let t(x, ...) =
    x, ...
    
  let foo() =
    ...
    let z, ... = t(y, ...)
    ...
  
  -- -->
  
  let t(x, ...) =
    x, ...
    
  let foo() =
    ...
    let z, ... = x, ...
    ...
  ```

- ```haskell
  let join j1(x, ...) = 
    ...
  
  let join j2(x, ...) =
    jump j1 (x, ...)
    
  let foo() =
    ...
    jump j2(m, n)
  
  -- -->
  
  let join j1(x, ...) = 
    ...
  
  let join j2(x, ...) =
    jump j1(x, ...)
    
  let foo() =
    ...
    jump j1(m, n, ...)
  
  ```

- ```haskell
  let trivial(x, ...) = 
    let result = ...
    result
  
  let foo() =
    ...
    let z = trivial(...)
    ...
    
  -- -->
  
  let foo() =
    ...
    let result = ...
    let z = result
    ...
  ```

- ```haskell
  let join trivial(x, ...) = 
    let result = ...
    result
  
  let foo() =
    ...
    jump trivial(...)
    
  -- -->
  
  let foo() =
    ...
    let result = ...
    result
  ```

## Selection Simplification

```haskell
let y = C(a = aaa, b = bbb, c = ccc)
...
let p = y.a
let q = y.b
let r = y.c
...

-- -->

let y = C(a = aaa, b = bbb, c = ccc)
...
let p = aaa
let q = bbb
let r = ccc
...
```

## Trivial Binding Simplification

```haskell
...
let a = ...
...
let b = a
...
let c = 1
...
... b ...
... c ...

-- -->

...
let a = ...
...
let b = a
...
let c = 1
...
... a ...
... 1 ...
```

## Dead Binding Elimination & Dead Definition Elimination
