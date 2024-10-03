# Tuple Patterns

```
b is refined D and
  let y = b.y
  ...
  // pattern with fixed length
  b is Array { length: 3 }
  b is [_, _, _]

  // let bindings single field selector and range selector
  let z = b.z
  let w = b[1..]
  let w = b[..-1]
```
