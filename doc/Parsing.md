# Advanced MLscript Parser

## Indentation

The parsing is indentation-sensitive,
but it follows some very simple rules uniformly.

Indentation is used only for two things:
 * to form indented blocks of code
 
 * to form single expressions spanning multiple line


### Indented blocks of code

In general, you can understand an indented block of code
as a syntax for nesting a list of `;`-separated statements inside an argument expression.

An indented block of the form:

```ts
some header expression
  aaa bbb ccc
  ddd eee fff
  ggg hhh iii
```

is equivalent to the form:

```ts
some header expression / (aaa bbb ccc; ddd eee fff; ggg hhh iii)
```

where `/` is a right-associated expression separator with low precedence
(whose goal is to avoid having to nest parentheses, similar to Haskell's `$`).

So in particular,  the following:

```ts
foo x
  bar y
    baz z
```

is equivalent to:

```ts
foo x / bar y / baz z
```

which is shorthand for:

```ts
foo x (bar y (baz z))
```



### Single expressions spanning multiple line

**Rule 1:**
if a line finishes on an operator,
then the following indented block is understood as an argument to that operator:

```ts
some header expression +
  aaa bbb ccc
  ddd eee fff
  ggg hhh iii
```

is equivalent to:

```ts
some header expression + (aaa bbb ccc; ddd eee fff; ggg hhh iii)
```

**Rule 2:**
a header expression followed by a succession of indented lines all starting by an operator
is understood as the application of the corresponding operators,
in order (operator precedence is ignored),
to the header expression:

```ts
some header expression
  + aaa bbb ccc
  * ddd eee fff
  - ggg hhh iii
```

is equivalent to:

```ts
(((some header expression) + (aaa bbb ccc)) * (ddd eee fff)) - (ggg hhh iii)
```

**Note:**
In both of these rules, one can use `/` as an operator;
so one can write:

```ts
foo
  / arg 1
  / arg 2
// i.e.,
(foo / arg 1) / arg 2

foo / bar /  // this last `/` is not actually useful!
  arg 1
  arg 2
// i.e.,
foo / bar / (arg 1; arg 2)
```

[TODO actually implement]

**Note:**
field accessors are considered operators (with tightest precedence):

```ts
foo
  .bar 1
  .baz 2
// i.e.,
(foo.bar 1).baz 2
```

[TODO actually implement]

