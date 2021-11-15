# MLscript

What would TypeScript look like if it had been designed with type inference and soundness in mind?

We provide one possible answer in MLscript, an object-oriented and functional programming language with records, generic classes, mix-in traits, first-class unions and intersections, instance matching, and ML-style principal type inference.
These features can be used to implement expressive class hierarchies as well as extensible sums and products.

MLscript supports union, intersection, and complement (or negation) connectives, making sure they form a Boolean algebra, and add enough structure to derive a sound and complete type inference algorithm.


## Running the tests

Running the tests only requires the Scala Build Tool installed.
In the terminal, run `sbt mlscriptJVM/test`.


## Running the demo locally

To run the demo on your computer, compile the project with `sbt fastOptJS`, then open the `local_testing.html` file in your browser.

You can make changes to the type inference code
in `shared/src/main/scala/mlscript`,
have it compile to JavaScript on file change with command
`sbt ~fastOptJS`,
and immediately see the results in your browser by refreshing the page with `F5`.
