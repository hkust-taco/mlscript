# MLscript

This is the second iteration of the MLscript compiler,
nicknamed _hkmc2_ (Hong Kong MLscript Compiler v2).


## Getting Started

### Project Structure

#### Sub-Projects

Most SBT subprojects are obsolete and will be removed in the future.

Most of the important code of the new compiler is in the `hkmc2` folder.

### Prerequisites

You need [JDK supported by Scala][supported-jdk-versions], [sbt][sbt], [Node.js][node.js], and TypeScript to compile the project and run the tests.

We recommend you to install JDK and sbt via [coursier][coursier]. The versions of Node.js that passed our tests are from v16.14 to v16.17, v17 and v18. Run `npm install` to install TypeScript. **Note that ScalaJS cannot find the global installed TypeScript.** We explicitly support TypeScript v4.7.4.

[supported-jdk-versions]: https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html
[sbt]: https://www.scala-sbt.org/
[node.js]: https://nodejs.org/
[coursier]: https://get-coursier.io/

Some tests in the `compiler` subproject generate and compile C++ while making use of some libraries.
You can run these by installing `nix` (for MacOS, we recommend https://determinate.systems/posts/graphical-nix-installer/)
and running `nix develop` before launching SBT.
If you don't want to use nix, you can install the dependencies manually as follows, but this has not been tested on non-MacOS systems:
```bash
brew install mimalloc boost gmp
```

### Running the tests

Running the tests requires the Scala Build Tool (SBT) installed.

We recommend running all tests in the SBT shell,
i.e., do not restart SBT every time,
but launch it in shell mode (with command `sbt`)
and then use one of the following commands.

- `hkmc2AllTests/test` for running all hkmc2 tests.
- `hkmc2JVM/test` for running only the compilation tests, in `hkmc2/shared/src/test/mlscript-compile`.
- `hkmc2DiffTests/test` for running only the diff-tests, in `hkmc2/shared/src/test/mlscript`.
- `~hkmc2DiffTests/Test/run` for running the test watcher,
  which updates test files as you save them and recompiles the Scala sources automatically on change.
- `test` for compiling all JVM and JS subprojects
  and running every single test in the repository,
  including obsolete ones.

Another useful SBT incantation is `; hkmc2AllTests/test; ~hkmc2DiffTests/Test/run`.
This command runs all hkmc2 tests once and then starts the test watcher.
This is a useful command to use periodically while making changes to the compiler,
to check that you haven't broken anything.

Note that when saved, the special file `ChangedTests.cmd` will trigger the test watcher to run
all tests that currently have unstaged changes in git.
This is useful when you have a working subset of tests that you want to run periodically.

### Running tests individually

Individual tests can be run with `-z`.
For example, `~mlscriptJVM/testOnly mlscript.DiffTests -- -z parser` will watch for file changes and continuously run all parser tests (those that have "parser" in their name).

You can also indicate the test you want in `shared/src/test/scala/mlscript/DiffTests.scala`:

```scala
  // Allow overriding which specific tests to run, sometimes easier for development:
  private val focused = Set[Str](
    // Add the test file path here like this:
    "shared/src/test/diff/mlscript/Methods.mls"
  ).map(os.RelPath(_))
```

To run the tests in ts2mls sub-project individually,
you can indicate the test you want in `ts2mls/js/src/test/scala/ts2mls/TSTypeGenerationTests.scala`:

```scala
private val testsData = List(
    // Put all input files in the `Seq`
    // Then indicate the output file's name
    (Seq("Array.ts"), "Array.d.mls")
  )
```


<!--
### Running the web demo locally

To run the demo on your computer, compile the project with `sbt fastOptJS`, then open the `local_testing.html` file in your browser.

You can make changes to the type inference code
in `shared/src/main/scala/mlscript`,
have it compile to JavaScript on file change with command
`sbt ~fastOptJS`,
and immediately see the results in your browser by refreshing the page with `F5`.
-->


