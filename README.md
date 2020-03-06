# Simple Algebraic Subtyping

This repository shows the implementation of **simple-sub**,
an alternative algorithm to MLsub for algebraic subtyping.

## Running the demo

To run the demo, compile the project with:
`sbt fastOptJS`,
and then open the file `demo.html` in your browser.

You can make changes to the type inference code
in `shared/src/main/scala/simplesub`,
have it compile to JavaScript on file change with command
`sbt ~fastOptJS`,
and immediately see the results in your browser by refreshing the page with `F5`.
