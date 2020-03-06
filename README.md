# Simple Algebraic Subtyping

This repository shows the implementation of **simple-sub**,
an alternative algorithm to MLsub for algebraic subtyping.

## Running the demo locally

To run the demo on your computer, first change the line in `index.html` from:
```html
<script type="text/javascript" src="bin/simple-algebraic-subtyping-opt.js"></script>
```
to:
```html
<script type="text/javascript" src="js/target/scala-2.13/simple-algebraic-subtyping-fastopt.js"></script>
```

And then compile the project with `sbt fastOptJS`.

Finally, open the file `index.html` in your browser.

You can make changes to the type inference code
in `shared/src/main/scala/simplesub`,
have it compile to JavaScript on file change with command
`sbt ~fastOptJS`,
and immediately see the results in your browser by refreshing the page with `F5`.
