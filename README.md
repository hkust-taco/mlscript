# MLscript

An playground for type system experimentation,
focused on functional programming, dependent types, and subtyping.


## Running the tests

Running the tests only requires the Scala Build Tool installed.
In the terminal, run `sbt mlscriptJVM/test`.


## Running the demo locally

To run the demo on your computer, first change the line in `index.html` from:
```html
<script type="text/javascript" src="bin/mlscript-opt.js"></script>
```
to:
```html
<script type="text/javascript" src="js/target/scala-2.13/mlscript-fastopt.js"></script>
```

And then compile the project with `sbt fastOptJS`.

Finally, open the file `index.html` in your browser.

You can make changes to the type inference code
in `shared/src/main/scala/mlscript`,
have it compile to JavaScript on file change with command
`sbt ~fastOptJS`,
and immediately see the results in your browser by refreshing the page with `F5`.
